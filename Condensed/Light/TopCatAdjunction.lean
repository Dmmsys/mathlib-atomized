/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.TopComparison
public import Mathlib.Topology.Category.Sequential
public import Mathlib.Topology.Category.LightProfinite.Sequence
/-!

# The adjunction between light condensed sets and topological spaces

This file defines the functor `lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u}` which is
left adjoint to `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`. We prove that the counit
is bijective (but not in general an isomorphism) and conclude that the right adjoint is faithful.

The counit is an isomorphism for sequential spaces, and we conclude that the functor
`topCatToLightCondSet` is fully faithful when restricted to sequential spaces.
-/

@[expose] public section

universe u

open LightCondensed LightCondSet CategoryTheory LightProfinite

namespace LightCondSet

variable (X : LightCondSet.{u})

set_option backward.privateInPublic true in
/-- Auxiliary definition to define the topology on `X(*)` for a light condensed set `X`. -/
/-
**LightCondSet.coinducingCoprod** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to define the topology on `X(*)` for a light condensed set 
`X`.
-/
private def coinducingCoprod :
    (Σ (i : (S : LightProfinite.{u}) × X.obj.obj ⟨S⟩), i.fst) →
      X.obj.obj ⟨LightProfinite.of PUnit⟩ :=
  fun ⟨⟨_, i⟩, s⟩ ↦ X.obj.map ((of PUnit.{u + 1}).const s).op i

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Let `X` be a light condensed set. We define a topology on `X(*)` as the quotient topology of
all the maps from light profinite sets `S` to `X(*)`, corresponding to elements of `X(S)`.
In other words, the topology coinduced by the map `LightCondSet.coinducingCoprod` above. -/
local instance underlyingTopologicalSpace :
    TopologicalSpace (X.obj.obj ⟨LightProfinite.of PUnit⟩) :=
  TopologicalSpace.coinduced (coinducingCoprod X) inferInstance

/-- The object part of the functor `LightCondSet ⥤ TopCat` -/
/-
**LightCondSet.toTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondSet`。
形式化陈述：toTopCat : TopCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The object part of the functor `LightCondSet ⥤ TopCat`
-/
abbrev toTopCat : TopCat.{u} := TopCat.of (X.obj.obj ⟨LightProfinite.of PUnit⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LightCondSet.continuous_coinducingCoprod** 是 Mathlib 中的一个引理，位于命名空间 `LightCondS
et`。
形式化陈述：continuous_coinducingCoprod {S : LightProfinite.{u}} (x : X.obj.obj ⟨S⟩) :
 Continuous fun a => (X.coinducingCoprod ⟨⟨S, x⟩, a⟩)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_sigma_iff`：continuous_sigma_iff {f : Sigma σ -> X} : Continuo
us f ↔ forall i, Continuous fun a => f ⟨i, a⟩
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
lemma continuous_coinducingCoprod {S : LightProfinite.{u}} (x : X.obj.obj ⟨S⟩) :
    Continuous fun a ↦ (X.coinducingCoprod ⟨⟨S, x⟩, a⟩) := by
  suffices ∀ (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
      Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
  rw [← continuous_sigma_iff]
  apply continuous_coinduced_rng

variable {X} {Y : LightCondSet} (f : X ⟶ Y)

/-- The map part of the functor `LightCondSet ⥤ TopCat` -/
@[simps!]
/-
**LightCondSet.toTopCatMap** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
形式化陈述：toTopCatMap : X.toTopCat ⟶ Y.toTopCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The map part of the functor `LightCondSet ⥤ TopCat`
-/
def toTopCatMap : X.toTopCat ⟶ Y.toTopCat :=
  TopCat.ofHom
  { toFun := f.hom.app ⟨LightProfinite.of PUnit⟩
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      apply continuous_sigma
      intro ⟨S, x⟩
      simp only [Function.comp_apply, coinducingCoprod]
      rw
        [show (fun (a : S) ↦ f.hom.app ⟨of PUnit⟩ (X.obj.map ((of PUnit.{u + 1}).const a).op x)) = _
        from funext fun a ↦ NatTrans.naturality_apply f.hom ((of PUnit.{u + 1}).const a).op x]
      exact continuous_coinducingCoprod _ _ }

/-- The functor `LightCondSet ⥤ TopCat` -/
@[simps]
/-
**LightCondSet._root_.lightCondSetToTopCat** 是 Mathlib 中的一个定义，位于命名空间 `LightCondS
et`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `LightCondSet ⥤ TopCat`
-/
def _root_.lightCondSetToTopCat : LightCondSet.{u} ⥤ TopCat.{u} where
  obj X := X.toTopCat
  map f := toTopCatMap f

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
/-
**LightCondSet.topCatAdjunctionCounit** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
形式化陈述：topCatAdjunctionCounit (X : TopCat.{u}) : X.toLightCondSet.toTopCat ⟶ X
参数：X : TopCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet`
-/
noncomputable def topCatAdjunctionCounit (X : TopCat.{u}) : X.toLightCondSet.toTopCat ⟶ X :=
  TopCat.ofHom
  { toFun x := x.1 PUnit.unit
    continuous_toFun := by
      rw [continuous_coinduced_dom]
      continuity }

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` is always bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is sequential).
-/
/-
**LightCondSet.topCatAdjunctionCounitEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LightCondS
et`。
形式化陈述：topCatAdjunctionCounitEquiv (X : TopCat.{u}) : X.toLightCondSet.toTopCat ≃
 X where toFun
参数：X : TopCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The counit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` is al
ways bijective,
but not an isomorphism in general (the inverse isn't continuous unless `X` is se
quential).
-/
noncomputable def topCatAdjunctionCounitEquiv (X : TopCat.{u}) : X.toLightCondSet.toTopCat ≃ X where
  toFun := topCatAdjunctionCounit X
  invFun x := ContinuousMap.const _ x
/-
**LightCondSet.topCatAdjunctionCounit_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Light
CondSet`。
形式化陈述：topCatAdjunctionCounit_bijective (X : TopCat.{u}) : Function.Bijective (to
pCatAdjunctionCounit X)
参数：X : TopCat.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma topCatAdjunctionCounit_bijective (X : TopCat.{u}) :
    Function.Bijective (topCatAdjunctionCounit X) :=
  (topCatAdjunctionCounitEquiv X).bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
@[simps hom_app]
/-
**LightCondSet.topCatAdjunctionUnit** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
形式化陈述：topCatAdjunctionUnit (X : LightCondSet.{u}) : X ⟶ X.toTopCat.toLightCondSe
t where hom
参数：X : LightCondSet.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The unit of the adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet`
-/
noncomputable def topCatAdjunctionUnit (X : LightCondSet.{u}) : X ⟶ X.toTopCat.toLightCondSet where
  hom := {
    app S := ↾fun x ↦ {
      toFun := fun s ↦ X.obj.map ((of PUnit.{u + 1}).const s).op x
      continuous_toFun := by
        suffices ∀ (i : (T : LightProfinite.{u}) × X.obj.obj ⟨T⟩),
          Continuous (fun (a : i.fst) ↦ X.coinducingCoprod ⟨i, a⟩) from this ⟨_, _⟩
        rw [← continuous_sigma_iff]
        apply continuous_coinduced_rng }
    naturality := fun _ _ _ ↦ by
      ext
      simp only [Opposite.op_unop, TypeCat.Fun.toFun_apply,
        comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        TopCat.toSheafCompHausLike_obj_map, ← Functor.map_comp_apply]
      rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` -/
/-
**LightCondSet.topCatAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
形式化陈述：topCatAdjunction : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where u
nit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet`
-/
noncomputable def topCatAdjunction : lightCondSetToTopCat.{u} ⊣ topCatToLightCondSet where
  unit := { app := topCatAdjunctionUnit }
  counit := { app := topCatAdjunctionCounit }
  left_triangle_components Y := by
    ext
    change Y.obj.map (𝟙 _) _ = _
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**LightCondSet.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : TopCat) : Epi (topCatAdjunction.counit.app X) := by
  rw [TopCat.epi_iff_surjective]
  exact (topCatAdjunctionCounit_bijective _).2
/-
**LightCondSet.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : topCatToLightCondSet.Faithful := topCatAdjunction.faithful_R_of_epi_counit_app

open Sequential
/-
**LightCondSet.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : LightCondSet.{u}) : SequentialSpace X.toTopCat := by
  apply SequentialSpace.coinduced
/-
**LightCondSet.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : LightCondSet.{u}) : SequentialSpace (lightCondSetToTopCat.obj X) :=
  inferInstanceAs (SequentialSpace X.toTopCat)

/-- The functor from light condensed sets to topological spaces lands in sequential spaces. -/
/-
**LightCondSet.lightCondSetToSequential** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`
。
形式化陈述：lightCondSetToSequential : LightCondSet.{u} ⥤ Sequential.{u} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightCondSet.instSequentialSpaceCarrierObjTopCatLightCondSetToTopCat`：∀ 
(X : LightCondSet), SequentialSpace ↑(lightCondSetToTopCat.obj X)

--- 原说明 ---
The functor from light condensed sets to topological spaces lands in sequential 
spaces.
-/
def lightCondSetToSequential : LightCondSet.{u} ⥤ Sequential.{u} where
  obj X := Sequential.of (lightCondSetToTopCat.obj X)
  map f := InducedCategory.homMk (toTopCatMap f)

/--
The functor from topological spaces to light condensed sets restricted to sequential spaces.
-/
/-
**LightCondSet.sequentialToLightCondSet** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`
。
形式化陈述：sequentialToLightCondSet : Sequential.{u} ⥤ LightCondSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from topological spaces to light condensed sets restricted to sequen
tial spaces.
-/
noncomputable def sequentialToLightCondSet :
    Sequential.{u} ⥤ LightCondSet.{u} :=
  sequentialToTop ⋙ topCatToLightCondSet

/--
The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` restricted to sequential
spaces.
-/
/-
**LightCondSet.sequentialAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet`。
形式化陈述：sequentialAdjunction : lightCondSetToSequential ⊣ sequentialToLightCondSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `lightCondSetToTopCat ⊣ topCatToLightCondSet` restricted to seque
ntial
spaces.
-/
noncomputable def sequentialAdjunction :
    lightCondSetToSequential ⊣ sequentialToLightCondSet :=
  topCatAdjunction.restrictFullyFaithful (iC := 𝟭 _) (iD := sequentialToTop)
    (Functor.FullyFaithful.id _) fullyFaithfulSequentialToTop
    (Iso.refl _) (Iso.refl _)

/--
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSet`
is a homeomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for `X : TopCat.{0}`.
-/
/-
**LightCondSet.sequentialAdjunctionHomeo** 是 Mathlib 中的一个定义，位于命名空间 `LightCondSet
`。
形式化陈述：sequentialAdjunctionHomeo (X : TopCat.{0}) [SequentialSpace X] : X.toLight
CondSet.toTopCat ≃ₜ X where toEquiv
参数：X : TopCat.{0}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSe
t`
is a homeomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0
, which is why we
can only prove this for `X : TopCat.{0}`.
-/
noncomputable def sequentialAdjunctionHomeo (X : TopCat.{0}) [SequentialSpace X] :
    X.toLightCondSet.toTopCat ≃ₜ X where
  toEquiv := topCatAdjunctionCounitEquiv X
  continuous_invFun := by
    apply SeqContinuous.continuous
    unfold SeqContinuous
    intro f p h
    let g := (topCatAdjunctionCounitEquiv X).invFun ∘ (OnePoint.continuousMapMkNat f p h)
    change Filter.Tendsto (fun n : ℕ ↦ g n) _ _
    erw [← OnePoint.continuous_iff_from_nat]
    let x : X.toLightCondSet.obj.obj ⟨(ℕ∪{∞})⟩ := OnePoint.continuousMapMkNat f p h
    exact continuous_coinducingCoprod X.toLightCondSet x

/--
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSet`
is an isomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for `X : Sequential.{0}`.
-/
/-
**LightCondSet.sequentialAdjunctionCounitIso** 是 Mathlib 中的一个定义，位于命名空间 `LightCon
dSet`。
形式化陈述：sequentialAdjunctionCounitIso (X : Sequential.{0}) : lightCondSetToSequent
ial.obj (sequentialToLightCondSet.obj X) ≅ X
参数：X : Sequential.{0}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sequential.is_sequential`：∀ (self : Sequential), SequentialSpace ↑self.t
oTop

--- 原说明 ---
The counit of the adjunction `lightCondSetToSequential ⊣ sequentialToLightCondSe
t`
is an isomorphism.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0
, which is why we
can only prove this for `X : Sequential.{0}`.
-/
noncomputable def sequentialAdjunctionCounitIso (X : Sequential.{0}) :
    lightCondSetToSequential.obj (sequentialToLightCondSet.obj X) ≅ X :=
  isoOfHomeo (sequentialAdjunctionHomeo X.toTop)
/-
**LightCondSet.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso sequentialAdjunction.{0}.counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  exact inferInstanceAs (IsIso (sequentialAdjunctionCounitIso X).hom)

/--
The functor from topological spaces to light condensed sets restricted to sequential spaces
is fully faithful.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0, which is why we
can only prove this for the functor `Sequential.{0} ⥤ LightCondSet.{0}`.
-/
/-
**LightCondSet.fullyFaithfulSequentialToLightCondSet** 是 Mathlib 中的一个定义，位于命名空间 `
LightCondSet`。
形式化陈述：fullyFaithfulSequentialToLightCondSet : sequentialToLightCondSet.{0}.Fully
Faithful
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LightCondSet.instIsIsoFunctorSequentialCounitSequentialAdjunction`：Categ
oryTheory.IsIso LightCondSet.sequentialAdjunction.counit

--- 原说明 ---
The functor from topological spaces to light condensed sets restricted to sequen
tial spaces
is fully faithful.

Note: for now, we only have `ℕ∪{∞}` as a light profinite set at universe level 0
, which is why we
can only prove this for the functor `Sequential.{0} ⥤ LightCondSet.{0}`.
-/
noncomputable def fullyFaithfulSequentialToLightCondSet :
    sequentialToLightCondSet.{0}.FullyFaithful :=
  sequentialAdjunction.fullyFaithfulROfIsIsoCounit

end LightCondSet

