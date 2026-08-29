/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fiber functor as in SGA1, following
the definitions in Lenstra's notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fiber functor
* `FiberFunctor` : a fiber functor from a `PreGaloisCategory` to `FintypeCat`
* `GaloisCategory` : a `PreGaloisCategory` that admits a `FiberFunctor`
* `IsConnected` : an object of a category is connected if it is not initial
                        and does not have non-trivial subobjects

Any fiber functor `F` induces an equivalence with the category of finite, discrete `Aut F`-types.
This is proven in `Mathlib/CategoryTheory/Galois/Equivalence.lean`.

## Implementation details

We mostly follow Def 3.1 in Lenstra's notes. In axiom (G3)
we omit the factorisation of morphisms into epimorphisms and monomorphisms
as this is not needed for the proof of the fundamental theorem on Galois categories
(and then follows from it).

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w t

namespace CategoryTheory

open Limits CategoryTheory.Functor

/-!
A category `C` is a PreGalois category if it satisfies all properties
of a Galois category in the sense of SGA1 that do not involve a fiber functor.
A Galois category should furthermore admit a fiber functor.

The only difference between `[PreGaloisCategory C] (F : C ⥤ FintypeCat) [FiberFunctor F]` and
`[GaloisCategory C]` is that the former fixes one fiber functor `F`.
-/

/--
Definition of `PreGaloisCategory` / `PreGaloisCategory` 的定义

English:
class PreGaloisCategory
  parameters: (C : Type u₁) [Category.{u₂, u₁} C]
  axioms and operations (5):
    - hasTerminal : HasTerminal C  [default: by infer_instance]
    - hasPullbacks : HasPullbacks C  [default: by infer_instance]
    - hasFiniteCoproducts : HasFiniteCoproducts C  [default: by infer_instance]
    - hasQuotientsByFiniteGroups((G : Type u₂) [Group G] [Finite G]) : HasColimitsOfShape (SingleObj G) C  [default: by infer_instance]
    - monoInducesIsoOnDirectSummand({X Y : C} (i : X ⟶ Y) [Mono i]) : exists (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

中文:
类 PreGalois范畴
  参数: (C : 类型u₁) [范畴.{u₂, u₁} C]
  公理与运算 (5 个):
    - hasTerminal : 有终止 C  [默认: by infer_instance]
    - hasPullbacks : 有Pullbacks C  [默认: by infer_instance]
    - hasFiniteCoproducts : 有FiniteCoproducts C  [默认: by infer_instance]
    - hasQuotientsByFiniteGroups((G : 类型u₂) [群 G] [有限 G]) : 有形状余极限 (SingleObj G) C  [默认: by infer_instance]
    - monoInducesIsoOnDirectSummand({X Y : C} (i : X ⟶ Y) [单态射 i]) : 存在 (Z : C) (u : Z ⟶ Y), 非空 (是余极限 (BinaryCofan.mk i u))

Depends on / 依赖: infer_instance
-/
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  /-- `C` has a terminal object (G1). -/
  hasTerminal : HasTerminal C := by infer_instance
  /-- `C` has pullbacks (G1). -/
  hasPullbacks : HasPullbacks C := by infer_instance
  /-- `C` has finite coproducts (G2). -/
  hasFiniteCoproducts : HasFiniteCoproducts C := by infer_instance
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
  /-- Every monomorphism in `C` induces an isomorphism on a direct summand (G3). -/
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : exists (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

namespace PreGaloisCategory

/--
Definition of `FiberFunctor` / `FiberFunctor` 的定义

English:
class FiberFunctor
  parameters: {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
  axioms and operations (6):
    - preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F  [default: by infer_instance]
    - preservesPullbacks : PreservesLimitsOfShape WalkingCospan F  [default: by infer_instance]
    - preservesFiniteCoproducts : PreservesFiniteCoproducts F  [default: by infer_instance]
    - preservesEpis : Functor.PreservesEpimorphisms F  [default: by infer_instance]
    - preservesQuotientsByFiniteGroups((G : Type u₂) [Group G] [Finite G]) : PreservesColimitsOfShape (SingleObj G) F  [default: by infer_instance]
    - reflectsIsos : F.ReflectsIsomorphisms  [default: by infer_instance]

中文:
类 Fiber函子
  参数: {C : 类型u₁} [范畴.{u₂, u₁} C] [PreGalois范畴 C]
  公理与运算 (6 个):
    - preservesTerminalObjects : 保持形状极限 (范畴论.离散 命题空.{1}) F  [默认: by infer_instance]
    - preservesPullbacks : 保持形状极限 WalkingCospan F  [默认: by infer_instance]
    - preservesFiniteCoproducts : 保持FiniteCoproducts F  [默认: by infer_instance]
    - preservesEpis : 函子.保持Epimorphisms F  [默认: by infer_instance]
    - preservesQuotientsByFiniteGroups((G : 类型u₂) [群 G] [有限 G]) : 保持形状余极限 (SingleObj G) F  [默认: by infer_instance]
    - reflectsIsos : F.反映同构  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F := by
    infer_instance
  /-- `F` preserves pullbacks (G4). -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  /-- `F` preserves finite coproducts (G5). -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F := by infer_instance
  /-- `F` preserves epimorphisms (G5). -/
  preservesEpis : Functor.PreservesEpimorphisms F := by infer_instance
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
  /-- `F` reflects isomorphisms (G6). -/
  reflectsIsos : F.ReflectsIsomorphisms := by infer_instance

/--
Definition of `IsConnected` / `IsConnected` 的定义

English:
class IsConnected
  parameters: {C : Type u₁} [Category.{u₂, u₁} C] (X : C)
  axioms and operations (2):
    - notInitial : IsInitial X -> False
    - noTrivialComponent((Y : C) (i : Y ⟶ X) [Mono i]) : (IsInitial Y -> False) -> IsIso i

中文:
类 是连通
  参数: {C : 类型u₁} [范畴.{u₂, u₁} C] (X : C)
  公理与运算 (2 个):
    - notInitial : IsInitial X -> 假
    - noTrivialComponent((Y : C) (i : Y ⟶ X) [单态射 i]) : (IsInitial Y -> 假) -> 是同构 i
-/
class IsConnected {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  /-- `X` is not an initial object. -/
  notInitial : IsInitial X -> False
  /-- `X` has no non-trivial subobjects. -/
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y -> False) -> IsIso i

/--
Definition of `PreservesIsConnected` / `PreservesIsConnected` 的定义

English:
class PreservesIsConnected
  parameters: {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
  axioms and operations (1):
    - preserves : forall {X : C} [IsConnected X], IsConnected (F.obj X)

中文:
类 保持是连通
  参数: {C : 类型u₁} [范畴.{u₂, u₁} C] {D : 类型v₁}
  公理与运算 (1 个):
    - preserves : 对任意 {X : C} [是连通 X], 是连通 (F.obj X)
-/
class PreservesIsConnected {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  /-- `F.obj X` is connected if `X` is connected. -/
  preserves : forall {X : C} [IsConnected X], IsConnected (F.obj X)

section
variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteLimits C
  body: hasFiniteLimits_of_hasTerminal_and_pullbacks

中文:
实例 :
  签名: 有有限极限 C
  定义体: hasFiniteLimits_of_hasTerminal_and_pullbacks

Depends on / 依赖: hasFiniteLimits_of_hasTerminal_and_pullbacks
-/
instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryProducts C
  body: hasBinaryProducts_of_hasTerminal_and_pullbacks C

中文:
实例 :
  签名: HasBinaryProducts C
  定义体: hasBinaryProducts_of_hasTerminal_and_pullbacks C

Depends on / 依赖: hasBinaryProducts_of_hasTerminal_and_pullbacks
-/
instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasEqualizers C
  body: hasEqualizers_of_hasPullbacks_and_binary_products

中文:
实例 :
  签名: HasEqualizers C
  定义体: hasEqualizers_of_hasPullbacks_and_binary_products

Depends on / 依赖: hasEqualizers_of_hasPullbacks_and_binary_products
-/
instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

-- A `PreGaloisCategory` has quotients by finite groups in arbitrary universes. -/
instance {G : Type*} [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

end

namespace FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FiberFunctor F]

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsLimitsOfShape (Discrete PEmpty.{1}) F
  body: reflectsLimitsOfShape_of_reflectsIsomorphisms

中文:
实例 :
  签名: 反映形状极限 (离散 命题空.{1}) F
  定义体: reflectsLimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
noncomputable instance : ReflectsLimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsColimitsOfShape (Discrete PEmpty.{1}) F
  body: reflectsColimitsOfShape_of_reflectsIsomorphisms

中文:
实例 :
  签名: 反映形状余极限 (离散 命题空.{1}) F
  定义体: reflectsColimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsIsomorphisms
-/
noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits F
  body: preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

中文:
实例 :
  签名: 保持FiniteLimits F
  定义体: preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

Depends on / 依赖: preservesFiniteLimits_of_preservesTerminal_and_pullbacks
-/
noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

/-- Fiber functors preserve quotients by finite groups in arbitrary universes. -/
instance {G : Type*} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by
  choose G' hg hf he using Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv he.some.toSingleObjEquiv.symm F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsMonomorphisms F
  body: ReflectsMonomorphisms.mk by
  intro X Y f _
  have : IsIso (pullback.fst (F.map f) (F.map f)) :=
    isIso_fst_of_mono (F.map f)
  have : IsIso (F.map (pullback.fst f f)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst f f) := isIso_of_reflects_

中文:
实例 :
  签名: 反映单态射 F
  定义体: ReflectsMonomorphisms.mk by
  intro X Y f _
  have : IsIso (pullback.fst (F.map f) (F.map f)) :=
    isIso_fst_of_mono (F.map f)
  have : IsIso (F.map (pullback.fst f f)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst f f) := isIso_of_reflects_

Depends on / 依赖: F.map, IsIso.comp_isIso, PreservesPullback, PreservesPullback.iso_hom_fst, ReflectsMonomorphisms, ReflectsMonomorphisms.mk, comp_isIso, diagonal_isKernelPair, isIso_fst_of_mono, isIso_of_reflects_iso, iso_hom_fst, mono_of_isIso_fst, pullback, pullback.diagonal_isKernelPair, pullback.fst
-/
instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk by
  intro X Y f _
  have : IsIso (pullback.fst (F.map f) (F.map f)) :=
    isIso_fst_of_mono (F.map f)
  have : IsIso (F.map (pullback.fst f f)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst f f) := isIso_of_reflects_iso (pullback.fst _ _) F
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.Faithful
  body: by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

中文:
实例 :
  签名: F.忠实
  定义体: by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

Depends on / 依赖: F.map, IsIso.comp_isIso, comp_isIso, eq_of_epi_equalizer, equalizer, isIso_of_reflects_iso
-/
instance : F.Faithful where
  map_injective {X Y} f g h := by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

section

/--
Instance `comp_right` / 实例 `comp_right`

English:
instance comp_right
  signature: (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.IsEquivalence]
  body: comp_preservesColimitsOfShape F E

中文:
实例 comp_right
  签名: (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.是等价]
  定义体: comp_preservesColimitsOfShape F E

Depends on / 依赖: comp_preservesColimitsOfShape
-/
instance comp_right (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.IsEquivalence] :
    FiberFunctor (F ⋙ E) where
  preservesQuotientsByFiniteGroups _ := comp_preservesColimitsOfShape F E

end

end FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C]
  (F : C ⥤ FintypeCat.{w})

/-- The canonical action of `Aut F` on the fiber of each object. -/
instance (X : C) : MulAction (Aut F) (F.obj X) where
  smul σ x := σ.hom.app X x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
lemma `mulAction_def` / 引理 `mulAction_def`

English:
lemma mulAction_def
  given: {X : C} (σ : Aut F) (x : F.obj X)
  proof: rfl

中文:
引理 mulAction_def
  条件: {X : C} (σ : Aut F) (x : F.obj X)
  证明: rfl
-/
lemma mulAction_def {X : C} (σ : Aut F) (x : F.obj X) :
    σ • x = σ.hom.app X x :=
  rfl

/--
lemma `mulAction_naturality` / 引理 `mulAction_naturality`

English:
lemma mulAction_naturality
  given: {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X)
  proof: NatTrans.naturality_apply σ.hom f x

中文:
引理 mulAction_naturality
  条件: {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X)
  证明: NatTrans.naturality_apply σ.hom f x

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, naturality_apply
-/
lemma mulAction_naturality {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) :
    σ • F.map f x = F.map f (σ • x) :=
  NatTrans.naturality_apply σ.hom f x

/--
lemma `has_non_trivial_subobject_of_not_isConnected_of_not_initial` / 引理 `has_non_trivial_subobject_of_not_isConnected_of_not_initial`

English:
lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial
  statement: (X : C) (hc : ¬ IsConnected X)
  proof: by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni => hc Y i hni hm⟩

中文:
引理 has_non_trivial_subobject_of_not_isConnected_of_not_initial
  结论: (X : C) (hc : ¬ 是连通 X)
  证明: by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni => hc Y i hni hm⟩

Depends on / 依赖: contrapose
-/
lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : ¬ IsConnected X)
    (hi : IsInitial X -> False) :
    exists (Y : C) (v : Y ⟶ X), (IsInitial Y -> False) ∧ Mono v ∧ (¬ IsIso v) := by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni => hc Y i hni hm⟩

/--
lemma `card_fiber_eq_of_iso` / 引理 `card_fiber_eq_of_iso`

English:
lemma card_fiber_eq_of_iso
  given: {X Y : C} (i : X ≅ Y)
  statement: Nat.card (F.obj X) = Nat.card (F.obj Y)
  proof: by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

中文:
引理 card_fiber_eq_of_iso
  条件: {X Y : C} (i : X ≅ Y)
  结论: 自然数.card (F.obj X) = 自然数.card (F.obj Y)
  证明: by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

Depends on / 依赖: Equiv.bijective, F.obj, FintypeCat, FintypeCat.incl, Iso.toEquiv, Nat.card_eq_of_bijective, bijective, card_eq_of_bijective, mapIso, toEquiv
-/
lemma card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

variable [PreGaloisCategory C] [FiberFunctor F]

/--
lemma `initial_iff_fiber_empty` / 引理 `initial_iff_fiber_empty`

English:
lemma initial_iff_fiber_empty
  given: (X : C)
  statement: Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)
  proof: by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

中文:
引理 initial_iff_fiber_empty
  条件: (X : C)
  结论: 非空 (IsInitial X) ↔ 是空 (F.obj X)
  证明: by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

Depends on / 依赖: Concrete, Concrete.initial_iff_empty_of_preserves_of_reflects, F.obj, IsInitial, IsInitial.isInitialIffObj, initial_iff_empty_of_preserves_of_reflects, isInitialIffObj, nonempty_congr
-/
lemma initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

/--
lemma `not_initial_iff_fiber_nonempty` / 引理 `not_initial_iff_fiber_nonempty`

English:
lemma not_initial_iff_fiber_nonempty
  given: (X : C)
  statement: (IsInitial X -> False) ↔ Nonempty (F.obj X)
  proof: by
  rw [← not_isEmpty_iff]
refine ⟨fun h he => ?_, fun h hin => h (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

中文:
引理 not_initial_iff_fiber_nonempty
  条件: (X : C)
  结论: (IsInitial X -> 假) ↔ 非空 (F.obj X)
  证明: by
  rw [← not_isEmpty_iff]
refine ⟨fun h he => ?_, fun h hin => h (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

Depends on / 依赖: Nonempty, Nonempty.elim, initial_iff_fiber_empty, not_isEmpty_iff
-/
lemma not_initial_iff_fiber_nonempty (X : C) : (IsInitial X -> False) ↔ Nonempty (F.obj X) := by
  rw [← not_isEmpty_iff]
refine ⟨fun h he => ?_, fun h hin => h (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

/--
lemma `not_initial_of_inhabited` / 引理 `not_initial_of_inhabited`

English:
lemma not_initial_of_inhabited
  given: {X : C} (x : F.obj X) (h : IsInitial X)
  statement: False
  proof: ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

中文:
引理 not_initial_of_inhabited
  条件: {X : C} (x : F.obj X) (h : IsInitial X)
  结论: 假
  证明: ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

Depends on / 依赖: initial_iff_fiber_empty
-/
lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

/--
Instance `nonempty_fiber_of_isConnected` / 实例 `nonempty_fiber_of_isConnected`

English:
instance nonempty_fiber_of_isConnected
  signature: (X : C) [IsConnected X]
  body: by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin

中文:
实例 nonempty_fiber_of_isConnected
  签名: (X : C) [是连通 X]
  定义体: by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin

Depends on / 依赖: IsConnected, IsConnected.notInitial, IsInitial, Nonempty, initial_iff_fiber_empty, notInitial, not_nonempty_iff, not_nonempty_iff.mp
-/
instance nonempty_fiber_of_isConnected (X : C) [IsConnected X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin

/--
Definition of `fiberEqualizerEquiv` / `fiberEqualizerEquiv` 的定义

English:
definition fiberEqualizerEquiv
  signature: {X Y : C} (f g : X ⟶ Y)
  body: (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv

@[simp]

中文:
定义 fiberEqualizerEquiv
  签名: {X Y : C} (f g : X ⟶ Y)
  定义体: (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv

@[simp]

Depends on / 依赖: F.map, FintypeCat, FintypeCat.incl, PreservesEqualizer, PreservesEqualizer.iso, Types.equalizerIso, equalizerIso, toEquiv
-/
noncomputable def fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv

@[simp]
/--
lemma `fiberEqualizerEquiv_symm_ι_apply` / 引理 `fiberEqualizerEquiv_symm_ι_apply`

English:
lemma fiberEqualizerEquiv_symm_ι_apply
  statement: {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
  proof: by
  simp only [fiberEqualizerEquiv, Functor.comp_map]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]
  rfl

中文:
引理 fiberEqualizerEquiv_symm_ι_apply
  结论: {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
  证明: by
  simp only [fiberEqualizerEquiv, Functor.comp_map]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]
  rfl

Depends on / 依赖: FintypeCat, FintypeCat.incl, Functor, Functor.comp_map, PreservesEqualizer, PreservesEqualizer.iso_inv_, Types.equalizerIso, Types.equalizerIso_inv_comp_, comp_map, equalizer, equalizerIso, fiberEqualizerEquiv
-/
lemma fiberEqualizerEquiv_symm_ι_apply {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
    (h : F.map f x = F.map g x) :
    F.map (equalizer.ι f g) ((fiberEqualizerEquiv F f g).symm ⟨x, h⟩) = x := by
  simp only [fiberEqualizerEquiv, Functor.comp_map]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]
  rfl

/--
Definition of `fiberPullbackEquiv` / `fiberPullbackEquiv` 的定义

English:
definition fiberPullbackEquiv
  signature: {X A B : C} (f : A ⟶ X) (g : B ⟶ X)
  body: Iso.toEquiv (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom)

@[simp]

中文:
定义 fiberPullbackEquiv
  签名: {X A B : C} (f : A ⟶ X) (g : B ⟶ X)
  定义体: Iso.toEquiv (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom)

@[simp]

Depends on / 依赖: F.map, FintypeCat, FintypeCat.incl, Iso.toEquiv, PreservesPullback, PreservesPullback.iso, Types.pullbackIsoPullback, pullbackIsoPullback, toEquiv
-/
noncomputable def fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 } :=
  Iso.toEquiv (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom)

@[simp]
/--
lemma `fiberPullbackEquiv_symm_fst_apply` / 引理 `fiberPullbackEquiv_symm_fst_apply`

English:
lemma fiberPullbackEquiv_symm_fst_apply
  statement: {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
  proof: by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]
  rfl

@[simp]

中文:
引理 fiberPullbackEquiv_symm_fst_apply
  结论: {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
  证明: by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]
  rfl

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl, Functor, Functor.comp_map, Iso.toEquiv_symm_fun, PreservesPullback, PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback, Types.pullbackIsoPullback_inv_fst, comp_map, fiberPullbackEquiv, iso_inv_fst, pullback, pullback.fst, pullbackIsoPullback, pullbackIsoPullback_inv_fst, toEquiv_symm_fun
-/
lemma fiberPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.fst f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = a := by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]
  rfl

@[simp]
/--
lemma `fiberPullbackEquiv_symm_snd_apply` / 引理 `fiberPullbackEquiv_symm_snd_apply`

English:
lemma fiberPullbackEquiv_symm_snd_apply
  statement: {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
  proof: by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]
  rfl

中文:
引理 fiberPullbackEquiv_symm_snd_apply
  结论: {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
  证明: by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]
  rfl

Depends on / 依赖: FintypeCat, FintypeCat.incl, Functor, Functor.comp_map, Iso.toEquiv_symm_fun, PreservesPullback, PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback, Types.pullbackIsoPullback_inv_snd, comp_map, fiberPullbackEquiv, iso_inv_snd, pullback, pullback.snd, pullbackIsoPullback, pullbackIsoPullback_inv_snd, toEquiv_symm_fun
-/
lemma fiberPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.snd f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = b := by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]
  rfl

/--
Definition of `fiberBinaryProductEquiv` / `fiberBinaryProductEquiv` 的定义

English:
definition fiberBinaryProductEquiv
  signature: (X Y : C)
  body: (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv

@[simp]

中文:
定义 fiberBinaryProductEquiv
  签名: (X Y : C)
  定义体: (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv

@[simp]

Depends on / 依赖: F.obj, FintypeCat, FintypeCat.incl, PreservesLimitPair, PreservesLimitPair.iso, Types.binaryProductIso, binaryProductIso, toEquiv
-/
noncomputable def fiberBinaryProductEquiv (X Y : C) :
    F.obj (X ⨯ Y) ≃ F.obj X × F.obj Y :=
  (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv

@[simp]
/--
lemma `fiberBinaryProductEquiv_symm_fst_apply` / 引理 `fiberBinaryProductEquiv_symm_fst_apply`

English:
lemma fiberBinaryProductEquiv_symm_fst_apply
  given: {X Y : C} (x : F.obj X) (y : F.obj Y)
  proof: by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]
  rfl

@[simp]

中文:
引理 fiberBinaryProductEquiv_symm_fst_apply
  条件: {X Y : C} (x : F.obj X) (y : F.obj Y)
  证明: by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]
  rfl

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl, PreservesLimitPair, PreservesLimitPair.iso_inv_fst, Types.binaryProductIso, Types.binaryProductIso_inv_comp_fst, binaryProductIso, binaryProductIso_inv_comp_fst, fiberBinaryProductEquiv, iso_inv_fst, prod.fst
-/
lemma fiberBinaryProductEquiv_symm_fst_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.fst ((fiberBinaryProductEquiv F X Y).symm (x, y)) = x := by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]
  rfl

@[simp]
/--
lemma `fiberBinaryProductEquiv_symm_snd_apply` / 引理 `fiberBinaryProductEquiv_symm_snd_apply`

English:
lemma fiberBinaryProductEquiv_symm_snd_apply
  given: {X Y : C} (x : F.obj X) (y : F.obj Y)
  proof: by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]
  rfl

中文:
引理 fiberBinaryProductEquiv_symm_snd_apply
  条件: {X Y : C} (x : F.obj X) (y : F.obj Y)
  证明: by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]
  rfl

Depends on / 依赖: FintypeCat, FintypeCat.incl, PreservesLimitPair, PreservesLimitPair.iso_inv_snd, Types.binaryProductIso, Types.binaryProductIso_inv_comp_snd, binaryProductIso, binaryProductIso_inv_comp_snd, fiberBinaryProductEquiv, iso_inv_snd, prod.snd
-/
lemma fiberBinaryProductEquiv_symm_snd_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.snd ((fiberBinaryProductEquiv F X Y).symm (x, y)) = y := by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]
  rfl

/--
lemma `evaluation_injective_of_isConnected` / 引理 `evaluation_injective_of_isConnected`

English:
lemma evaluation_injective_of_isConnected
  given: (A X : C) [IsConnected A] (a : F.obj A)
  proof: by
  intro f g (h : F.map f a = F.map g a)
  have : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

中文:
引理 evaluation_injective_of_isConnected
  条件: (A X : C) [是连通 A] (a : F.obj A)
  证明: by
  intro f g (h : F.map f a = F.map g a)
  have : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

Depends on / 依赖: F.map, IsConnected, IsConnected.noTrivialComponent, eq_of_epi_equalizer, equalizer, fiberEqualizerEquiv, noTrivialComponent, not_initial_of_inhabited
-/
lemma evaluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun (f : A ⟶ X) => F.map f a) := by
  intro f g (h : F.map f a = F.map g a)
  have : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

/--
lemma `evaluation_aut_injective_of_isConnected` / 引理 `evaluation_aut_injective_of_isConnected`

English:
lemma evaluation_aut_injective_of_isConnected
  given: (A : C) [IsConnected A] (a : F.obj A)
  proof: by
  change Function.Injective ((fun f : A ⟶ A => F.map f a) ∘ (fun f : Aut A => f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A

中文:
引理 evaluation_aut_injective_of_isConnected
  条件: (A : C) [是连通 A] (a : F.obj A)
  证明: by
  change Function.Injective ((fun f : A ⟶ A => F.map f a) ∘ (fun f : Aut A => f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A

Depends on / 依赖: Aut.ext, F.map, Function, Function.Injective, Function.Injective.comp, Injective, evaluation_injective_of_isConnected, f.hom
-/
lemma evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun f : Aut A => F.map (f.hom) a) := by
  change Function.Injective ((fun f : A ⟶ A => F.map f a) ∘ (fun f : Aut A => f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A

/--
lemma `epi_of_nonempty_of_isConnected` / 引理 `epi_of_nonempty_of_isConnected`

English:
lemma epi_of_nonempty_of_isConnected
  statement: {X A : C} [IsConnected A] [h : Nonempty (F.obj X)]
  proof: Epi.mk fun {Z} u v huv => by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using ConcreteCategory.congr_hom (F.congr_map huv) _

中文:
引理 epi_of_nonempty_of_isConnected
  结论: {X A : C} [是连通 A] [h : 非空 (F.obj X)]
  证明: Epi.mk fun {Z} u v huv => by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using ConcreteCategory.congr_hom (F.congr_map huv) _

Depends on / 依赖: Classical, Classical.arbitrary, ConcreteCategory, ConcreteCategory.congr_hom, Epi.mk, F.congr_map, F.map, arbitrary, congr_hom, congr_map, evaluation_injective_of_isConnected
-/
lemma epi_of_nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.obj X)]
(f : X ⟶ A) : Epi f := Epi.mk fun {Z} u v huv => by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using ConcreteCategory.congr_hom (F.congr_map huv) _

/--
lemma `surjective_on_fiber_of_epi` / 引理 `surjective_on_fiber_of_epi`

English:
lemma surjective_on_fiber_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f]
  statement: Function.Surjective (F.map f)
  proof: surjective_of_epi (FintypeCat.incl.map (F.map f))

中文:
引理 surjective_on_fiber_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f]
  结论: 函数.满射 (F.map f)
  证明: surjective_of_epi (FintypeCat.incl.map (F.map f))

Depends on / 依赖: F.map, FintypeCat, FintypeCat.incl.map, surjective_of_epi
-/
lemma surjective_on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f) :=
  surjective_of_epi (FintypeCat.incl.map (F.map f))

/--
lemma `surjective_of_nonempty_fiber_of_isConnected` / 引理 `surjective_of_nonempty_fiber_of_isConnected`

English:
lemma surjective_of_nonempty_fiber_of_isConnected
  statement: {X A : C} [Nonempty (F.obj X)]
  proof: by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f

中文:
引理 surjective_of_nonempty_fiber_of_isConnected
  结论: {X A : C} [非空 (F.obj X)]
  证明: by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f

Depends on / 依赖: epi_of_nonempty_of_isConnected, surjective_on_fiber_of_epi
-/
lemma surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
    [IsConnected A] (f : X ⟶ A) :
    Function.Surjective (F.map f) := by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f

/--
Instance `nonempty_fiber_pi_of_nonempty_of_finite` / 实例 `nonempty_fiber_pi_of_nonempty_of_finite`

English:
instance nonempty_fiber_pi_of_nonempty_of_finite
  signature: {ι : Type*} [Finite ι] (X : ι -> C)
  body: by
  cases nonempty_fintype ι
  let f (i : ι) : FintypeCat.{w} := F.obj (X i)
  let i : F.obj (∏ᶜ X) ≅ ∏ᶜ f := PreservesProduct.iso F _
  exact Nonempty.elim inferInstance fun x : (∏ᶜ f : FintypeCat.{w}) => ⟨i.inv x⟩

中文:
实例 nonempty_fiber_pi_of_nonempty_of_finite
  签名: {ι : 类型} [有限 ι] (X : ι -> C)
  定义体: by
  cases nonempty_fintype ι
  let f (i : ι) : FintypeCat.{w} := F.obj (X i)
  let i : F.obj (∏ᶜ X) ≅ ∏ᶜ f := PreservesProduct.iso F _
  exact Nonempty.elim inferInstance fun x : (∏ᶜ f : FintypeCat.{w}) => ⟨i.inv x⟩

Depends on / 依赖: F.obj, FintypeCat, Nonempty, Nonempty.elim, PreservesProduct, PreservesProduct.iso, i.inv, nonempty_fintype
-/
instance nonempty_fiber_pi_of_nonempty_of_finite {ι : Type*} [Finite ι] (X : ι -> C)
    [forall i, Nonempty (F.obj (X i))] : Nonempty (F.obj (∏ᶜ X)) := by
  cases nonempty_fintype ι
  let f (i : ι) : FintypeCat.{w} := F.obj (X i)
  let i : F.obj (∏ᶜ X) ≅ ∏ᶜ f := PreservesProduct.iso F _
  exact Nonempty.elim inferInstance fun x : (∏ᶜ f : FintypeCat.{w}) => ⟨i.inv x⟩

section CardFiber

open ConcreteCategory

attribute [local instance] FintypeCat.fintype in
/--
lemma `isIso_of_mono_of_eq_card_fiber` / 引理 `isIso_of_mono_of_eq_card_fiber`

English:
lemma isIso_of_mono_of_eq_card_fiber
  statement: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflect

中文:
引理 isIso_of_mono_of_eq_card_fiber
  结论: {X Y : C} (f : X ⟶ Y) [单态射 f]
  证明: by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflect

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, F.map, Fintype, Fintype.bijective_iff_injective_and_card, Nat.card_eq_fintype_card, bijective_iff_injective_and_card, card_eq_fintype_card, injective_of_mono_of_preservesPullback, isIso_iff_bijective, isIso_of_reflects_iso
-/
lemma isIso_of_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : Nat.card (F.obj X) = Nat.card (F.obj Y)) : IsIso f := by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflects_iso f F

/--
lemma `lt_card_fiber_of_mono_of_notIso` / 引理 `lt_card_fiber_of_mono_of_notIso`

English:
lemma lt_card_fiber_of_mono_of_notIso
  statement: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [not_lt] at hlt
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt

中文:
引理 lt_card_fiber_of_mono_of_notIso
  结论: {X Y : C} (f : X ⟶ Y) [单态射 f]
  证明: by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [not_lt] at hlt
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt

Depends on / 依赖: F.map, Nat.card_le_card_of_injective, Nat.le_antisymm, card_le_card_of_injective, injective_of_mono_of_preservesPullback, isIso_of_mono_of_eq_card_fiber, le_antisymm, not_lt
-/
lemma lt_card_fiber_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : ¬ IsIso f) : Nat.card (F.obj X) < Nat.card (F.obj Y) := by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [not_lt] at hlt
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt

/--
lemma `non_zero_card_fiber_of_not_initial` / 引理 `non_zero_card_fiber_of_not_initial`

English:
lemma non_zero_card_fiber_of_not_initial
  given: (X : C) (h : IsInitial X -> False)
  proof: by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero

中文:
引理 non_zero_card_fiber_of_not_initial
  条件: (X : C) (h : IsInitial X -> 假)
  证明: by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero

Depends on / 依赖: Finite, Finite.card_eq_zero_iff.mp, Nonempty, Nonempty.elim, card_eq_zero_iff, initial_iff_fiber_empty
-/
lemma non_zero_card_fiber_of_not_initial (X : C) (h : IsInitial X -> False) :
    Nat.card (F.obj X) != 0 := by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero

/--
lemma `card_fiber_coprod_eq_sum` / 引理 `card_fiber_coprod_eq_sum`

English:
lemma card_fiber_coprod_eq_sum
  given: (X Y : C)
  proof: by
  let e : F.obj (X ⨿ Y) ≃ F.obj X oplus F.obj Y := Iso.toEquiv
 (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
 Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective

中文:
引理 card_fiber_coprod_eq_sum
  条件: (X Y : C)
  证明: by
  let e : F.obj (X ⨿ Y) ≃ F.obj X oplus F.obj Y := Iso.toEquiv
 (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
 Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective

Depends on / 依赖: Equiv.bijective, F.obj, FintypeCat, FintypeCat.incl, FintypeCat.incl.obj, Iso.toEquiv, Nat.card_eq_of_bijective, Nat.card_sum, PreservesColimitPair, PreservesColimitPair.iso, Types.binaryCoproductIso, bijective, binaryCoproductIso, card_eq_of_bijective, card_sum, e.toFun, symm.trans, toEquiv
-/
lemma card_fiber_coprod_eq_sum (X Y : C) :
    Nat.card (F.obj (X ⨿ Y)) = Nat.card (F.obj X) + Nat.card (F.obj Y) := by
  let e : F.obj (X ⨿ Y) ≃ F.obj X oplus F.obj Y := Iso.toEquiv
 (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
 Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective e)

/--
lemma `card_hom_le_card_fiber_of_connected` / 引理 `card_hom_le_card_fiber_of_connected`

English:
lemma card_hom_le_card_fiber_of_connected
  given: (A X : C) [IsConnected A]
  proof: by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)

中文:
引理 card_hom_le_card_fiber_of_connected
  条件: (A X : C) [是连通 A]
  证明: by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)

Depends on / 依赖: Classical, Classical.arbitrary, Nat.card_le_card_of_injective, arbitrary, card_le_card_of_injective, evaluation_injective_of_isConnected
-/
lemma card_hom_le_card_fiber_of_connected (A X : C) [IsConnected A] :
    Nat.card (A ⟶ X) <= Nat.card (F.obj X) := by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)

/--
lemma `card_aut_le_card_fiber_of_connected` / 引理 `card_aut_le_card_fiber_of_connected`

English:
lemma card_aut_le_card_fiber_of_connected
  given: (A : C) [IsConnected A]
  proof: by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a

中文:
引理 card_aut_le_card_fiber_of_connected
  条件: (A : C) [是连通 A]
  证明: by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a

Depends on / 依赖: F.obj, Nat.card_le_card_of_injective, Nonempty, card_le_card_of_injective, evaluation_aut_injective_of_isConnected
-/
lemma card_aut_le_card_fiber_of_connected (A : C) [IsConnected A] :
    Nat.card (Aut A) <= Nat.card (F.obj A) := by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a

end CardFiber

end PreGaloisCategory

/--
Definition of `GaloisCategory` / `GaloisCategory` 的定义

English:
class GaloisCategory
  parameters: (C : Type u₁) [Category.{u₂, u₁} C]
  extends: PreGaloisCategory C
  axioms and operations (1):
    - hasFiberFunctor : exists F : C ⥤ FintypeCat.{u₂}, Nonempty (PreGaloisCategory.FiberFunctor F)

中文:
类 Galois范畴
  参数: (C : 类型u₁) [范畴.{u₂, u₁} C]
  继承: PreGalois范畴 C
  公理与运算 (1 个):
    - hasFiberFunctor : 存在 F : C ⥤ FintypeCat.{u₂}, 非空 (PreGalois范畴.Fiber函子 F)
-/
class GaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop
    extends PreGaloisCategory C where
  hasFiberFunctor : exists F : C ⥤ FintypeCat.{u₂}, Nonempty (PreGaloisCategory.FiberFunctor F)

namespace PreGaloisCategory

variable (C : Type u₁) [Category.{u₂, u₁} C] [GaloisCategory C]

/--
Definition of `GaloisCategory.getFiberFunctor` / `GaloisCategory.getFiberFunctor` 的定义

English:
definition GaloisCategory.getFiberFunctor
  signature: : C ⥤ FintypeCat.{u₂}
  body: Classical.choose @GaloisCategory.hasFiberFunctor C _ _

中文:
定义 Galois范畴.getFiberFunctor
  签名: : C ⥤ FintypeCat.{u₂}
  定义体: Classical.choose @GaloisCategory.hasFiberFunctor C _ _

Depends on / 依赖: Classical, Classical.choose, GaloisCategory, GaloisCategory.hasFiberFunctor, hasFiberFunctor
-/
noncomputable def GaloisCategory.getFiberFunctor : C ⥤ FintypeCat.{u₂} :=
Classical.choose @GaloisCategory.hasFiberFunctor C _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiberFunctor (GaloisCategory.getFiberFunctor C)
  body: Classical.choice Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)

中文:
实例 :
  签名: Fiber函子 (Galois范畴.getFiberFunctor C)
  定义体: Classical.choice Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)

Depends on / 依赖: Classical, Classical.choice, Classical.choose_spec, GaloisCategory, GaloisCategory.hasFiberFunctor, choice, choose_spec, hasFiberFunctor
-/
noncomputable instance : FiberFunctor (GaloisCategory.getFiberFunctor C) :=
Classical.choice Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)

variable {C}

/-- In a `GaloisCategory` the set of morphisms out of a connected object is finite. -/
instance (A X : C) [IsConnected A] : Finite (A ⟶ X) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f => F.map f a)
  exact evaluation_injective_of_isConnected F A X a

/-- In a `GaloisCategory` the set of automorphism of a connected object is finite. -/
instance (A : C) [IsConnected A] : Finite (Aut A) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f => F.map f.hom a)
  exact evaluation_aut_injective_of_isConnected F A a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoCoprod C
  body: by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F

中文:
实例 :
  签名: MonoCoprod C
  定义体: by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F

Depends on / 依赖: GaloisCategory, GaloisCategory.getFiberFunctor, MonoCoprod, MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono, getFiberFunctor, monoCoprod_of_preservesCoprod_of_reflectsMono
-/
instance : MonoCoprod C := by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F

end PreGaloisCategory

end CategoryTheory
