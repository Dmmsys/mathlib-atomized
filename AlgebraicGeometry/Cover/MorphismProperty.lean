/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Covers of schemes

This file provides the basic API for covers of schemes. A cover of a scheme `X` with respect to
a morphism property `P` is a jointly surjective indexed family of scheme morphisms with
target `X` all satisfying `P`.

## Implementation details

The definition on the pullback of a cover along a morphism depends on results that
are developed later in the import tree. Hence in this file, they have additional assumptions
that will be automatically satisfied in later files. The motivation here is that we already
know that these assumptions are satisfied for open immersions and hence the cover API for open
immersions can be used to deduce these assumptions in the general case.

-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

variable (K : Precoverage Scheme.{u})

/--
Definition of `JointlySurjective` / `JointlySurjective` 的定义

English:
class JointlySurjective
  parameters: (K : Precoverage Scheme.{u})
  axioms and operations (1):
    - exists_eq({X : Scheme.{u}} (S : Presieve X) (hS : S in K X) (x : X)) : exists (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x in Set.range g

中文:
类 JointlySurjective
  参数: (K : Precoverage 概形.{u})
  公理与运算 (1 个):
    - exists_eq({X : 概形.{u}} (S : Presieve X) (hS : S in K X) (x : X)) : 存在 (Y : 概形.{u}) (g : Y ⟶ X), S g ∧ x in 集合.range g
-/
class JointlySurjective (K : Precoverage Scheme.{u}) : Prop where
  exists_eq {X : Scheme.{u}} (S : Presieve X) (hS : S in K X) (x : X) :
    exists (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x in Set.range g

/--
Definition of `Cover` / `Cover` 的定义

English:
abbreviation Cover
  signature: (K : Precoverage Scheme.{u})
  body: Precoverage.ZeroHypercover.{v} K

中文:
缩写 Cover
  签名: (K : Precoverage 概形.{u})
  定义体: Precoverage.ZeroHypercover.{v} K

Depends on / 依赖: Precoverage, Precoverage.ZeroHypercover, ZeroHypercover
-/
abbrev Cover (K : Precoverage Scheme.{u}) := Precoverage.ZeroHypercover.{v} K

variable {K}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover K) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [forall x, HasPullback (𝒰.f x ≫ f) g]

/--
lemma `Cover.exists_eq` / 引理 `Cover.exists_eq`

English:
lemma Cover.exists_eq
  given: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  proof: by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

中文:
引理 Cover.存在_eq
  条件: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  证明: by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

Depends on / 依赖: JointlySurjective, JointlySurjective.exists_eq, exists_eq
-/
lemma Cover.exists_eq [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    exists i y, 𝒰.f i y = x := by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

/--
Definition of `Cover.idx` / `Cover.idx` 的定义

English:
definition Cover.idx
  signature: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  body: (𝒰.exists_eq x).choose

中文:
定义 Cover.idx
  签名: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  定义体: (𝒰.exists_eq x).choose

Depends on / 依赖: exists_eq
-/
def Cover.idx [JointlySurjective K] (𝒰 : X.Cover K) (x : X) : 𝒰.I₀ :=
  (𝒰.exists_eq x).choose

/--
lemma `Cover.covers` / 引理 `Cover.covers`

English:
lemma Cover.covers
  given: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  proof: (𝒰.exists_eq x).choose_spec

中文:
引理 Cover.covers
  条件: [JointlySurjective K] (𝒰 : X.Cover K) (x : X)
  证明: (𝒰.exists_eq x).choose_spec

Depends on / 依赖: choose_spec, exists_eq
-/
lemma Cover.covers [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    x in Set.range (𝒰.f (𝒰.idx x)) :=
  (𝒰.exists_eq x).choose_spec

/--
theorem `Cover.iUnion_range` / 定理 `Cover.iUnion_range`

English:
theorem Cover.iUnion_range
  given: [JointlySurjective K] {X : Scheme.{u}} (𝒰 : X.Cover K)
  proof: by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x

中文:
定理 Cover.iUnion_range
  条件: [JointlySurjective K] {X : 概形.{u}} (𝒰 : X.Cover K)
  证明: by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x

Depends on / 依赖: Set.eq_univ_iff_forall, Set.mem_iUnion, eq_univ_iff_forall, exists_eq, mem_iUnion
-/
theorem Cover.iUnion_range [JointlySurjective K] {X : Scheme.{u}} (𝒰 : X.Cover K) :
    ⋃ i, Set.range (𝒰.f i) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x

/--
Instance `Cover.nonempty_of_nonempty` / 实例 `Cover.nonempty_of_nonempty`

English:
instance Cover.nonempty_of_nonempty
  signature: [JointlySurjective K] [Nonempty X] (𝒰 : X.Cover K)
  body: by
  obtain ⟨i, _⟩ := 𝒰.exists_eq ‹Nonempty X›.some
  use i

中文:
实例 Cover.nonempty_of_nonempty
  签名: [JointlySurjective K] [非空 X] (𝒰 : X.Cover K)
  定义体: by
  obtain ⟨i, _⟩ := 𝒰.exists_eq ‹Nonempty X›.some
  use i

Depends on / 依赖: Nonempty, exists_eq
-/
instance Cover.nonempty_of_nonempty [JointlySurjective K] [Nonempty X] (𝒰 : X.Cover K) :
    Nonempty 𝒰.I₀ := by
  obtain ⟨i, _⟩ := 𝒰.exists_eq ‹Nonempty X›.some
  use i

section MorphismProperty

variable {P Q : MorphismProperty Scheme.{u}}

/--
lemma `presieve₀_mem_precoverage_iff` / 引理 `presieve₀_mem_precoverage_iff`

English:
lemma presieve₀_mem_precoverage_iff
  given: (E : PreZeroHypercover X)
  proof: by
  simp

@[grind ←]

中文:
引理 presieve₀_mem_precoverage_iff
  条件: (E : PreZeroHypercover X)
  证明: by
  simp

@[grind ←]
-/
lemma presieve₀_mem_precoverage_iff (E : PreZeroHypercover X) :
    E.presieve₀ in precoverage P X ↔ (forall x, exists i, x in Set.range (E.f i)) ∧ forall i, P (E.f i) := by
  simp

@[grind ←]
/--
lemma `Cover.map_prop` / 引理 `Cover.map_prop`

English:
lemma Cover.map_prop
  given: (𝒰 : X.Cover (precoverage P)) (i : 𝒰.I₀)
  statement: P (𝒰.f i)
  proof: 𝒰.mem₀.2 ⟨i⟩

中文:
引理 Cover.map_prop
  条件: (𝒰 : X.Cover (precoverage P)) (i : 𝒰.I₀)
  结论: P (𝒰.f i)
  证明: 𝒰.mem₀.2 ⟨i⟩
-/
lemma Cover.map_prop (𝒰 : X.Cover (precoverage P)) (i : 𝒰.I₀) : P (𝒰.f i) :=
  𝒰.mem₀.2 ⟨i⟩

/-- Given a family of schemes with morphisms to `X` satisfying `P` that jointly
cover `X`, `Cover.mkOfCovers` is an associated `P`-cover of `X`. -/
@[simps!]
/--
Definition of `Cover.mkOfCovers` / `Cover.mkOfCovers` 的定义

English:
definition Cover.mkOfCovers
  signature: (J : Type*) (obj : J -> Scheme.{u}) (map : (j : J) -> obj j ⟶ X)
  body: J
  X := obj
  f := map
  mem₀ := by
    simp_rw [presieve₀_mem_precoverage_iff, Set.mem_range]
    grind

中文:
定义 Cover.mkOfCovers
  签名: (J : 类型) (obj : J -> 概形.{u}) (map : (j : J) -> obj j ⟶ X)
  定义体: J
  X := obj
  f := map
  mem₀ := by
    simp_rw [presieve₀_mem_precoverage_iff, Set.mem_range]
    grind

Depends on / 依赖: Set.mem_range, X.Cover, infer_instance, mem_range, precoverage, simp_rw
-/
def Cover.mkOfCovers (J : Type*) (obj : J -> Scheme.{u}) (map : (j : J) -> obj j ⟶ X)
    (covers : forall x, exists j y, map j y = x)
    (map_prop : forall j, P (map j) := by infer_instance) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    simp_rw [presieve₀_mem_precoverage_iff, Set.mem_range]
    grind

/-- An isomorphism `X ⟶ Y` is a `P`-cover of `Y`. -/
@[simps! I₀ X f]
/--
Definition of `coverOfIsIso` / `coverOfIsIso` 的定义

English:
definition coverOfIsIso
  signature: [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y)
  body: .mkOfCovers PUnit (fun _ => X)
    (fun _ => f)
    (fun x => ⟨⟨⟩, inv f x, by simp [← Hom.comp_apply]⟩)
    (fun _ => P.of_isIso f)

中文:
定义 coverOfIsIso
  签名: [P.余ntainsIdentities] [P.RespectsIso] {X Y : 概形.{u}} (f : X ⟶ Y)
  定义体: .mkOfCovers PUnit (fun _ => X)
    (fun _ => f)
    (fun x => ⟨⟨⟩, inv f x, by simp [← Hom.comp_apply]⟩)
    (fun _ => P.of_isIso f)

Depends on / 依赖: Hom.comp_apply, P.of_isIso, comp_apply, mkOfCovers, of_isIso
-/
def coverOfIsIso [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : Cover.{v} (precoverage P) Y :=
  .mkOfCovers PUnit (fun _ => X)
    (fun _ => f)
    (fun x => ⟨⟨⟩, inv f x, by simp [← Hom.comp_apply]⟩)
    (fun _ => P.of_isIso f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: JointlySurjective (precoverage P)
  body: fun ⟨hR, _⟩ x => by
    rw [jointlySurjectivePrecoverage]; rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    use Y, g, hg
    exact heq

中文:
实例 :
  签名: JointlySurjective (precoverage P)
  定义体: fun ⟨hR, _⟩ x => by
    rw [jointlySurjectivePrecoverage]; rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    use Y, g, hg
    exact heq

Depends on / 依赖: Presieve, Presieve.mem_comap_jointlySurjectivePrecoverage_iff, jointlySurjectivePrecoverage, mem_comap_jointlySurjectivePrecoverage_iff
-/
instance : JointlySurjective (precoverage P) where
  exists_eq {X} R := fun ⟨hR, _⟩ x => by
    rw [jointlySurjectivePrecoverage]; rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    use Y, g, hg
    exact heq

/--
Definition of `Cover.changeProp` / `Cover.changeProp` 的定义

English:
definition Cover.changeProp
  signature: [JointlySurjective K] (𝒰 : X.Cover K) (h : forall j, Q (𝒰.f j))
  body: 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨𝒰.exists_eq, h⟩

中文:
定义 Cover.changeProp
  签名: [JointlySurjective K] (𝒰 : X.Cover K) (h : 对任意 j, Q (𝒰.f j))
  定义体: 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨𝒰.exists_eq, h⟩
-/
def Cover.changeProp [JointlySurjective K] (𝒰 : X.Cover K) (h : forall j, Q (𝒰.f j)) :
    X.Cover (precoverage Q) where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨𝒰.exists_eq, h⟩

/-- We construct a cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original cover. -/
@[simps I₀ X f]
/--
Definition of `Cover.copy` / `Cover.copy` 的定义

English:
definition Cover.copy
  signature: [P.RespectsIso] {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
  body: J
  X := obj
  f := map
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨i, rfl⟩ := e₁.surjective i
      use i, (e₂ i).inv y
      simp [h]
    · simp_rw [h, MorphismProperty.cancel_left_of_respectsIso]
      in

中文:
定义 Cover.copy
  签名: [P.RespectsIso] {X : 概形.{u}} (𝒰 : X.Cover (precoverage P))
  定义体: J
  X := obj
  f := map
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨i, rfl⟩ := e₁.surjective i
      use i, (e₂ i).inv y
      simp [h]
    · simp_rw [h, MorphismProperty.cancel_left_of_respectsIso]
      in
-/
def Cover.copy [P.RespectsIso] {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
    (J : Type*) (obj : J -> Scheme)
    (map : forall i, obj i ⟶ X) (e₁ : J ≃ 𝒰.I₀) (e₂ : forall i, obj i ≅ 𝒰.X (e₁ i))
    (h : forall i, map i = (e₂ i).hom ≫ 𝒰.f (e₁ i)) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨i, rfl⟩ := e₁.surjective i
      use i, (e₂ i).inv y
      simp [h]
    · simp_rw [h, MorphismProperty.cancel_left_of_respectsIso]
      intro i
      exact 𝒰.map_prop _

-- `respectTransparency false` is needed for `simps!`.
-- Consider making implicit-reducible:
-- `Precoverage.ZeroHypercover.bind`, `Cover.mkOfCovers`, `coverOfIso`
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of a cover along an isomorphism. -/
@[simps! I₀ X f, implicit_reducible]
/--
Definition of `Cover.pushforwardIso` / `Cover.pushforwardIso` 的定义

English:
definition Cover.pushforwardIso
  signature: [P.RespectsIso] [P.ContainsIdentities] [P.IsStableUnderComposition]
  body: Cover.copy ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰) 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

中文:
定义 Cover.pushforwardIso
  签名: [P.RespectsIso] [P.余ntainsIdentities] [P.是StableUnderComposition]
  定义体: Cover.copy ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰) 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

Depends on / 依赖: Category, Category.id_comp, Cover.copy, Equiv.punitProd, Equiv.sigmaEquivProd, Iso.refl, coverOfIsIso, id_comp, punitProd, sigmaEquivProd, symm.trans
-/
def Cover.pushforwardIso [P.RespectsIso] [P.ContainsIdentities] [P.IsStableUnderComposition]
    {X Y : Scheme.{u}} (𝒰 : Cover.{v} (precoverage P) X) (f : X ⟶ Y) [IsIso f] :
    Cover.{v} (precoverage P) Y :=
  Cover.copy ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰) 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

/-- Adding map satisfying `P` into a cover gives another cover. -/
@[simps toPreZeroHypercover]
nonrec def Cover.add {X Y : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : Y ⟶ X)
    (hf : P f := by infer_instance) : X.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover.add f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
refine ⟨fun x => ⟨some 𝒰.idx x, 𝒰.covers x⟩, ?_⟩
    rintro (i | i) <;> simp [hf, 𝒰.map_prop]

/--
Definition of `Cover.pullbackHom` / `Cover.pullbackHom` 的定义

English:
definition Cover.pullbackHom
  signature: [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  body: pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]

中文:
定义 Cover.pullbackHom
  签名: [P.是StableUnderBaseChange] [是JointlySurjectivePreserving P]
  定义体: pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]

Depends on / 依赖: pullback, pullback.snd
-/
def Cover.pullbackHom [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) (i) [forall x, HasPullback f (𝒰.f x)] :
    (𝒰.pullback₁ f).X i ⟶ 𝒰.X i :=
  pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]
/--
lemma `Cover.pullbackHom_map` / 引理 `Cover.pullbackHom_map`

English:
lemma Cover.pullbackHom_map
  statement: [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  proof: pullback.condition.symm

中文:
引理 Cover.pullbackHom_map
  结论: [P.是StableUnderBaseChange] [是JointlySurjectivePreserving P]
  证明: pullback.condition.symm

Depends on / 依赖: condition, pullback, pullback.condition.symm
-/
lemma Cover.pullbackHom_map [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X)
    [forall (x : 𝒰.I₀), HasPullback f (𝒰.f x)] (i) :
    𝒰.pullbackHom f i ≫ 𝒰.f i = (𝒰.pullback₁ f).f i ≫ f := pullback.condition.symm

/--
Definition of `AffineCover` / `AffineCover` 的定义

English:
structure AffineCover
  parameters: (P : MorphismProperty Scheme.{u}) (S : Scheme.{u})
  axioms and operations (6):
    - I₀ : Type v
    - X((j : I₀)) : CommRingCat.{u}
    - f((j : I₀)) : Spec (X j) ⟶ S
    - idx((x : S)) : I₀
    - covers((x : S)) : x in Set.range (f (idx x))
    - map_prop((j : I₀)) : P (f j)  [default: by infer_instance]

中文:
结构 仿射覆盖
  参数: (P : MorphismProperty 概形.{u}) (S : 概形.{u})
  公理与运算 (6 个):
    - I₀ : 类型v
    - X((j : I₀)) : 交换环范畴.{u}
    - f((j : I₀)) : Spec (X j) ⟶ S
    - idx((x : S)) : I₀
    - covers((x : S)) : x in 集合.range (f (idx x))
    - map_prop((j : I₀)) : P (f j)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure AffineCover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where
  /-- index set of an affine cover of a scheme `S` -/
  I₀ : Type v
  /-- the ring associated to a component of an affine cover -/
  X (j : I₀) : CommRingCat.{u}
  /-- the components map to `S` -/
  f (j : I₀) : Spec (X j) ⟶ S
  /-- given a point of `x : S`, `idx x` is the index of the component which contains `x` -/
  idx (x : S) : I₀
  /-- the components cover `S` -/
  covers (x : S) : x in Set.range (f (idx x))
  /-- the component maps satisfy `P` -/
  map_prop (j : I₀) : P (f j) := by infer_instance

/-- The cover associated to an affine cover. -/
@[simps]
/--
Definition of `AffineCover.cover` / `AffineCover.cover` 的定义

English:
definition AffineCover.cover
  signature: {X : Scheme.{u}} (𝒰 : X.AffineCover P)
  body: 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, 𝒰.map_prop⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use 𝒰.idx x, y

中文:
定义 仿射覆盖.cover
  签名: {X : 概形.{u}} (𝒰 : X.仿射覆盖 P)
  定义体: 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, 𝒰.map_prop⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use 𝒰.idx x, y
-/
def AffineCover.cover {X : Scheme.{u}} (𝒰 : X.AffineCover P) :
    X.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, 𝒰.map_prop⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use 𝒰.idx x, y

/-- Any `v`-cover `𝒰` induces a `u`-cover indexed by the points of `X`. -/
@[simps!]
/--
Definition of `Cover.ulift` / `Cover.ulift` 的定义

English:
definition Cover.ulift
  signature: (𝒰 : Cover.{v} (precoverage P) X)
  body: X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => 𝒰.map_prop _⟩
    use x, (𝒰.exists_eq x).choose_spec.choose, (𝒰.exists_eq x).choose_spec.choose_spec

中文:
定义 Cover.ulift
  签名: (𝒰 : Cover.{v} (precoverage P) X)
  定义体: X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => 𝒰.map_prop _⟩
    use x, (𝒰.exists_eq x).choose_spec.choose, (𝒰.exists_eq x).choose_spec.choose_spec
-/
def Cover.ulift (𝒰 : Cover.{v} (precoverage P) X) : Cover.{u} (precoverage P) X where
  I₀ := X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => 𝒰.map_prop _⟩
    use x, (𝒰.exists_eq x).choose_spec.choose, (𝒰.exists_eq x).choose_spec.choose_spec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Precoverage.Small.{u} (precoverage P)
  body: ⟨S, Cover.idx 𝒰, (Cover.ulift 𝒰).mem₀⟩

中文:
实例 :
  签名: Precoverage.Small.{u} (precoverage P)
  定义体: ⟨S, Cover.idx 𝒰, (Cover.ulift 𝒰).mem₀⟩

Depends on / 依赖: Cover.idx, Cover.ulift
-/
instance : Precoverage.Small.{u} (precoverage P) where
  zeroHypercoverSmall {S} 𝒰 := ⟨S, Cover.idx 𝒰, (Cover.ulift 𝒰).mem₀⟩

section category

/--
Definition of `Cover.Hom` / `Cover.Hom` 的定义

English:
abbreviation Cover.Hom
  signature: {X : Scheme.{u}} (𝒰 𝒱 : Cover.{v} K X)
  body: Precoverage.ZeroHypercover.Hom K 𝒰 𝒱

@[deprecated (since := "2026-01-13")] alias Cover.Hom.idx := PreZeroHypercover.Hom.s₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.app := PreZeroHypercover.Hom.h₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.w := PreZeroHypercover.Hom.w₀

@[d

中文:
缩写 Cover.态射
  签名: {X : 概形.{u}} (𝒰 𝒱 : Cover.{v} K X)
  定义体: Precoverage.ZeroHypercover.Hom K 𝒰 𝒱

@[deprecated (since := "2026-01-13")] alias Cover.Hom.idx := PreZeroHypercover.Hom.s₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.app := PreZeroHypercover.Hom.h₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.w := PreZeroHypercover.Hom.w₀

@[d

Depends on / 依赖: Precoverage, Precoverage.ZeroHypercover.Hom, ZeroHypercover
-/
abbrev Cover.Hom {X : Scheme.{u}} (𝒰 𝒱 : Cover.{v} K X) :=
  Precoverage.ZeroHypercover.Hom K 𝒰 𝒱

@[deprecated (since := "2026-01-13")] alias Cover.Hom.idx := PreZeroHypercover.Hom.s₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.app := PreZeroHypercover.Hom.h₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.w := PreZeroHypercover.Hom.w₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.id := PreZeroHypercover.Hom.id

@[deprecated (since := "2026-01-13")] alias Cover.Hom.comp := PreZeroHypercover.Hom.comp

@[deprecated (since := "2026-01-13")] alias Cover.id_idx_apply := PreZeroHypercover.id_s₀

@[deprecated (since := "2026-01-13")] alias Cover.id_app := PreZeroHypercover.id_h₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_idx_apply := PreZeroHypercover.comp_s₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_app := PreZeroHypercover.comp_h₀

end category

end MorphismProperty

end Scheme

end AlgebraicGeometry
