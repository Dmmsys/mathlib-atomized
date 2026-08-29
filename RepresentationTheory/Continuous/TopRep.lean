/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Topological representations

This file defines the category `TopRep k G` of topological representations of a monoid `G` over a
topological ring `k`, and shows that it is equivalent to the category `Action (TopModuleCat k) G`.

For a topological group `G` we define the invariants functor `TopRep.invariantsFunctor`, the
coinduction functor `TopRep.coind₁Functor`, the restriction functor `TopRep.resFunctor` along a
group homomorphism `φ : H →* G`, and the morphism `TopRep.invariantsResMap φ f` between invariant
submodules induced by a morphism `f : res φ X ⟶ Y`.
-/

@[expose] public section

universe w u v

/--
Definition of `TopRep` / `TopRep` 的定义

English:
structure TopRep
  parameters: (k : Type u) (G : Type v) [Ring k] [TopologicalSpace k] [Monoid G]
  axioms and operations (8):
    - private(mk) : :
    - V : Type w
    - [hV1 : AddCommGroup V]
    - [hV2 : Module k V]
    - [hV3 : TopologicalSpace V]
    - [hV4 : IsTopologicalAddGroup V]
    - [hV5 : ContinuousSMul k V]
    - ρ : ContRepresentation k G V

中文:
结构 TopRep
  参数: (k : 类型u) (G : 类型v) [Ring k] [TopologicalSpace k] [Monoid G]
  公理与运算 (8 个):
    - private(mk) : :
    - V : Type w
    - [hV1 : AddCommGroup V]
    - [hV2 : Module k V]
    - [hV3 : TopologicalSpace V]
    - [hV4 : IsTopologicalAddGroup V]
    - [hV5 : ContinuousSMul k V]
    - ρ : ContRepresentation k G V
-/
structure TopRep (k : Type u) (G : Type v) [Ring k] [TopologicalSpace k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `TopRep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  [hV3 : TopologicalSpace V]
  [hV4 : IsTopologicalAddGroup V]
  [hV5 : ContinuousSMul k V]
  /-- the underlying continuous representation of an object in `TopRep k G` -/
  ρ : ContRepresentation k G V

namespace TopRep

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [Ring k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y}

open ContRepresentation CategoryTheory

attribute [instance] hV1 hV2 hV3 hV4 hV5

initialize_simps_projections TopRep (-hV1, -hV2)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (TopRep k G) (Type w)
  body: ⟨TopRep.V⟩

中文:
实例 :
  签名: CoeSort (TopRep k G) (Type w)
  定义体: ⟨TopRep.V⟩

Depends on / 依赖: TopRep, TopRep.V
-/
instance : CoeSort (TopRep k G) (Type w) := ⟨TopRep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : TopRep k G
  body: ⟨X, ρ⟩

中文:
缩写 of
  签名: : TopRep k G
  定义体: ⟨X, ρ⟩
-/
abbrev of : TopRep k G := ⟨X, ρ⟩

variable (X ρ) in
/--
lemma `of_V` / 引理 `of_V`

English:
lemma of_V
  statement: (of ρ).V = X
  proof: by with_reducible rfl

中文:
引理 of_V
  结论: (of ρ).V = X
  证明: by with_reducible rfl

Depends on / 依赖: with_reducible
-/
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
/--
lemma `of_ρ` / 引理 `of_ρ`

English:
lemma of_ρ
  statement: (of ρ).ρ = ρ
  proof: by with_reducible rfl

中文:
引理 of_ρ
  结论: (of ρ).ρ = ρ
  证明: by with_reducible rfl

Depends on / 依赖: with_reducible
-/
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

/-- The type of morphisms in `TopRep k G`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (A B : TopRep k G)
  axioms and operations (2):
    - private(mk) : :
    - hom' : A.ρ ->ⁱL B.ρ

中文:
结构 Hom
  参数: (A B : TopRep k G)
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : A.ρ ->ⁱL B.ρ
-/
structure Hom (A B : TopRep k G) where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ ->ⁱL B.ρ

variable (A B C : TopRep.{w} k G)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (TopRep.{w} k G)
  body: Hom A B
  id A := ⟨.id (π₁ := A.ρ)⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category (TopRep.{w} k G)
  定义体: Hom A B
  id A := ⟨.id (π₁ := A.ρ)⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category (TopRep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id (π₁ := A.ρ)⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory (TopRep.{w} k G) (fun A B => A.ρ ->ⁱL B.ρ)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory (TopRep.{w} k G) (fun A B => A.ρ ->ⁱL B.ρ)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory (TopRep.{w} k G) (fun A B => A.ρ ->ⁱL B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: (f : Hom A B)
  body: ConcreteCategory.hom (C := TopRep k G) f

中文:
缩写 Hom.hom
  签名: (f : Hom A B)
  定义体: ConcreteCategory.hom (C := TopRep k G) f
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := TopRep k G) f

variable {A B} in
/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : ρ ->ⁱL σ)
  body: ConcreteCategory.ofHom (C := TopRep.{w} k G) f

中文:
缩写 ofHom
  签名: (f : ρ ->ⁱL σ)
  定义体: ConcreteCategory.ofHom (C := TopRep.{w} k G) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, TopRep
-/
abbrev ofHom (f : ρ ->ⁱL σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := TopRep.{w} k G) f

/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: (f : ρ ->ⁱL σ)
  statement: (ofHom f).hom = f
  proof: rfl

中文:
引理 hom_ofHom
  条件: (f : ρ ->ⁱL σ)
  结论: (ofHom f).hom = f
  证明: rfl
-/
@[simp] lemma hom_ofHom (f : ρ ->ⁱL σ) : (ofHom f).hom = f := rfl

/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: (f : A ⟶ B)
  statement: ofHom f.hom = f
  proof: rfl

中文:
引理 ofHom_hom
  条件: (f : A ⟶ B)
  结论: ofHom f.hom = f
  证明: rfl
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

variable {A B} in
/--
Definition of `Hom.toTopModuleCatHom` / `Hom.toTopModuleCatHom` 的定义

English:
abbreviation Hom.toTopModuleCatHom
  signature: (f : Hom A B)
  body: TopModuleCat.ofHom f.hom.toContinuousLinearMap

中文:
缩写 Hom.toTopModuleCatHom
  签名: (f : Hom A B)
  定义体: TopModuleCat.ofHom f.hom.toContinuousLinearMap

Depends on / 依赖: TopModuleCat, TopModuleCat.ofHom, f.hom.toContinuousLinearMap, toContinuousLinearMap
-/
abbrev Hom.toTopModuleCatHom (f : Hom A B) :
    TopModuleCat.of k A ⟶ TopModuleCat.of k B :=
  TopModuleCat.ofHom f.hom.toContinuousLinearMap

/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  statement: (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ)
  proof: rfl

中文:
引理 hom_id
  结论: (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ)
  证明: rfl
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id (π₁ := A.ρ) := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (a : A)
  statement: (𝟙 A : A ⟶ A) a = a
  proof: rfl

中文:
引理 id_apply
  条件: (a : A)
  结论: (𝟙 A : A ⟶ A) a = a
  证明: rfl
-/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := rfl

/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: (f : A ⟶ B) (g : B ⟶ C)
  statement: (f ≫ g).hom = g.hom.comp f.hom
  proof: rfl

中文:
引理 hom_comp
  条件: (f : A ⟶ B) (g : B ⟶ C)
  结论: (f ≫ g).hom = g.hom.comp f.hom
  证明: rfl
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  statement: (f ≫ g) a = g (f a)
  proof: rfl

中文:
引理 comp_apply
  条件: (f : A ⟶ B) (g : B ⟶ C) (a : A)
  结论: (f ≫ g) a = g (f a)
  证明: rfl
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := rfl

variable {A B} in
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : A ⟶ B} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

中文:
引理 hom_ext
  条件: {f g : A ⟶ B} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
/--
lemma `hom_comm_apply` / 引理 `hom_comm_apply`

English:
lemma hom_comm_apply
  given: (f : A ⟶ B) (g : G) (a : A)
  statement: f.hom (A.ρ g a) = B.ρ g (f.hom a)
  proof: by
  simpa using! congr($(f.hom.2 g) a)

中文:
引理 hom_comm_apply
  条件: (f : A ⟶ B) (g : G) (a : A)
  结论: f.hom (A.ρ g a) = B.ρ g (f.hom a)
  证明: by
  simpa using! congr($(f.hom.2 g) a)

Depends on / 依赖: f.hom
-/
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using! congr($(f.hom.2 g) a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (A ⟶ B)
  body: fast_instance% ConcreteCategory.homEquiv.addCommGroup

中文:
实例 :
  签名: AddCommGroup (A ⟶ B)
  定义体: fast_instance% ConcreteCategory.homEquiv.addCommGroup

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.addCommGroup, addCommGroup, fast_instance, homEquiv
-/
instance : AddCommGroup (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.addCommGroup

/--
lemma `hom_zero` / 引理 `hom_zero`

English:
lemma hom_zero
  statement: (0 : A ⟶ B).hom = 0
  proof: rfl

中文:
引理 hom_zero
  结论: (0 : A ⟶ B).hom = 0
  证明: rfl
-/
@[simp] lemma hom_zero : (0 : A ⟶ B).hom = 0 := rfl

/--
lemma `hom_add` / 引理 `hom_add`

English:
lemma hom_add
  given: (f g : A ⟶ B)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
引理 hom_add
  条件: (f g : A ⟶ B)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
lemma hom_add (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

/--
lemma `hom_sub` / 引理 `hom_sub`

English:
lemma hom_sub
  given: (f g : A ⟶ B)
  statement: (f - g).hom = f.hom - g.hom
  proof: rfl

中文:
引理 hom_sub
  条件: (f g : A ⟶ B)
  结论: (f - g).hom = f.hom - g.hom
  证明: rfl
-/
lemma hom_sub (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

/--
lemma `ofHom_add` / 引理 `ofHom_add`

English:
lemma ofHom_add
  given: (f g : ρ ->ⁱL σ)
  statement: ofHom (f + g) = ofHom f + ofHom g
  proof: rfl

中文:
引理 ofHom_add
  条件: (f g : ρ ->ⁱL σ)
  结论: ofHom (f + g) = ofHom f + ofHom g
  证明: rfl
-/
lemma ofHom_add (f g : ρ ->ⁱL σ) : ofHom (f + g) = ofHom f + ofHom g := rfl

/--
lemma `ofHom_sub` / 引理 `ofHom_sub`

English:
lemma ofHom_sub
  given: (f g : ρ ->ⁱL σ)
  statement: ofHom (f - g) = ofHom f - ofHom g
  proof: rfl

中文:
引理 ofHom_sub
  条件: (f g : ρ ->ⁱL σ)
  结论: ofHom (f - g) = ofHom f - ofHom g
  证明: rfl
-/
lemma ofHom_sub (f g : ρ ->ⁱL σ) : ofHom (f - g) = ofHom f - ofHom g := rfl

/--
lemma `comp_add'` / 引理 `comp_add'`

English:
lemma comp_add'
  given: (f : A ⟶ B) (g h : B ⟶ C)
  statement: f ≫ (g + h) = f ≫ g + f ≫ h
  proof: by
  ext : 1; simp [hom_add, ContIntertwiningMap.add_comp]

中文:
引理 comp_add'
  条件: (f : A ⟶ B) (g h : B ⟶ C)
  结论: f ≫ (g + h) = f ≫ g + f ≫ h
  证明: by
  ext : 1; simp [hom_add, ContIntertwiningMap.add_comp]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.add_comp, add_comp, hom_add
-/
lemma comp_add' (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.add_comp]

/--
lemma `add_comp'` / 引理 `add_comp'`

English:
lemma add_comp'
  given: (f g : A ⟶ B) (h : B ⟶ C)
  statement: (f + g) ≫ h = f ≫ h + g ≫ h
  proof: by
  ext : 1; simp [hom_add, ContIntertwiningMap.comp_add]

中文:
引理 add_comp'
  条件: (f g : A ⟶ B) (h : B ⟶ C)
  结论: (f + g) ≫ h = f ≫ h + g ≫ h
  证明: by
  ext : 1; simp [hom_add, ContIntertwiningMap.comp_add]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.comp_add, comp_add, hom_add
-/
lemma add_comp' (f g : A ⟶ B) (h : B ⟶ C) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  ext : 1; simp [hom_add, ContIntertwiningMap.comp_add]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (TopRep k G)
  body: inferInstance
  add_comp := TopRep.add_comp'
  comp_add := TopRep.comp_add'

中文:
实例 :
  签名: Preadditive (TopRep k G)
  定义体: inferInstance
  add_comp := TopRep.add_comp'
  comp_add := TopRep.comp_add'
-/
instance : Preadditive (TopRep k G) where
  homGroup := inferInstance
  add_comp := TopRep.add_comp'
  comp_add := TopRep.comp_add'

section Linear

variable {k : Type u} {G : Type v} {X Y : Type w} [TopologicalSpace k] [CommRing k]
  [Monoid G] [AddCommGroup X] [Module k X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul k X] [AddCommGroup Y] [Module k Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul k Y] {ρ : ContRepresentation k G X}
  {σ : ContRepresentation k G Y} {A B C : TopRep k G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module k (A ⟶ B)
  body: fast_instance% ConcreteCategory.homEquiv.module k

中文:
实例 :
  签名: Module k (A ⟶ B)
  定义体: fast_instance% ConcreteCategory.homEquiv.module k

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.module, fast_instance, homEquiv, module
-/
instance : Module k (A ⟶ B) := fast_instance% ConcreteCategory.homEquiv.module k

/--
lemma `hom_smul` / 引理 `hom_smul`

English:
lemma hom_smul
  given: (r : k) (f : A ⟶ B)
  statement: (r • f).hom = r • f.hom
  proof: rfl

中文:
引理 hom_smul
  条件: (r : k) (f : A ⟶ B)
  结论: (r • f).hom = r • f.hom
  证明: rfl
-/
lemma hom_smul (r : k) (f : A ⟶ B) : (r • f).hom = r • f.hom := rfl

/--
lemma `ofHom_smul` / 引理 `ofHom_smul`

English:
lemma ofHom_smul
  given: (r : k) (f : ρ ->ⁱL σ)
  statement: ofHom (r • f) = r • ofHom f
  proof: rfl

中文:
引理 ofHom_smul
  条件: (r : k) (f : ρ ->ⁱL σ)
  结论: ofHom (r • f) = r • ofHom f
  证明: rfl
-/
lemma ofHom_smul (r : k) (f : ρ ->ⁱL σ) : ofHom (r • f) = r • ofHom f := rfl

variable (A B C) in
/--
lemma `smul_comp'` / 引理 `smul_comp'`

English:
lemma smul_comp'
  given: (r : k) (f : A ⟶ B) (g : B ⟶ C)
  statement: (r • f) ≫ g = r • (f ≫ g)
  proof: by
  ext; simp [hom_smul, ContIntertwiningMap.comp_smul]

中文:
引理 smul_comp'
  条件: (r : k) (f : A ⟶ B) (g : B ⟶ C)
  结论: (r • f) ≫ g = r • (f ≫ g)
  证明: by
  ext; simp [hom_smul, ContIntertwiningMap.comp_smul]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.comp_smul, Nonempty, StrongNormalizationMonoid, comp_smul, hom_smul
-/
lemma smul_comp' (r : k) (f : A ⟶ B) (g : B ⟶ C) : (r • f) ≫ g = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.comp_smul]

variable (A B C) in
/--
lemma `comp_smul'` / 引理 `comp_smul'`

English:
lemma comp_smul'
  given: (f : A ⟶ B) (r : k) (g : B ⟶ C)
  statement: f ≫ (r • g) = r • (f ≫ g)
  proof: by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]

中文:
引理 comp_smul'
  条件: (f : A ⟶ B) (r : k) (g : B ⟶ C)
  结论: f ≫ (r • g) = r • (f ≫ g)
  证明: by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.smul_comp, hom_smul, smul_comp
-/
lemma comp_smul' (f : A ⟶ B) (r : k) (g : B ⟶ C) : f ≫ (r • g) = r • (f ≫ g) := by
  ext; simp [hom_smul, ContIntertwiningMap.smul_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryTheory.Linear k (TopRep k G)
  body: inferInstance
  smul_comp := smul_comp'
  comp_smul := comp_smul'

中文:
实例 :
  签名: CategoryTheory.Linear k (TopRep k G)
  定义体: inferInstance
  smul_comp := smul_comp'
  comp_smul := comp_smul'
-/
instance : CategoryTheory.Linear k (TopRep k G) where
  homModule := inferInstance
  smul_comp := smul_comp'
  comp_smul := comp_smul'

end Linear

section equivAction

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toActionTopModFunc` / `toActionTopModFunc` 的定义

English:
definition toActionTopModFunc
  signature: : TopRep k G ⥤ Action (TopModuleCat k) G where
  body: ⟨.of k X.V, (TopModuleCat.endRingEquiv (.of k X.V)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toTopModuleCatHom, fun g => by ext1; simp [TopModuleCat.endRingEquiv, f.hom.2 g]⟩

中文:
定义 toActionTopModFunc
  签名: : TopRep k G ⥤ Action (TopModuleCat k) G where
  定义体: ⟨.of k X.V, (TopModuleCat.endRingEquiv (.of k X.V)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toTopModuleCatHom, fun g => by ext1; simp [TopModuleCat.endRingEquiv, f.hom.2 g]⟩

Depends on / 依赖: TopModuleCat, TopModuleCat.endRingEquiv, endRingEquiv, symm.toMonoidHom.comp, toMonoidHom
-/
def toActionTopModFunc : TopRep k G ⥤ Action (TopModuleCat k) G where
  obj X := ⟨.of k X.V, (TopModuleCat.endRingEquiv (.of k X.V)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toTopModuleCatHom, fun g => by ext1; simp [TopModuleCat.endRingEquiv, f.hom.2 g]⟩

/--
Definition of `fromActionTopModFunc` / `fromActionTopModFunc` 的定义

English:
definition fromActionTopModFunc
  signature: : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where
  body: .of .ofMonoidHom (TopModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map {X Y} f := ofHom ⟨f.hom.hom, fun g => by
    simpa [← toMonoidHom_apply] using congr(TopModuleCat.Hom.hom $(f.comm g))⟩

中文:
定义 fromActionTopModFunc
  签名: : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where
  定义体: .of .ofMonoidHom (TopModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map {X Y} f := ofHom ⟨f.hom.hom, fun g => by
    simpa [← toMonoidHom_apply] using congr(TopModuleCat.Hom.hom $(f.comm g))⟩

Depends on / 依赖: TopModuleCat, TopModuleCat.endRingEquiv, endRingEquiv, ofMonoidHom, toMonoidHom, toMonoidHom.comp
-/
def fromActionTopModFunc : Action (TopModuleCat.{w} k) G ⥤ TopRep k G where
obj X := .of .ofMonoidHom (TopModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map {X Y} f := ofHom ⟨f.hom.hom, fun g => by
    simpa [← toMonoidHom_apply] using congr(TopModuleCat.Hom.hom $(f.comm g))⟩

/--
Definition of `toActionFromAction` / `toActionFromAction` 的定义

English:
definition toActionFromAction
  signature: (X : TopRep.{w} k G)
  body: ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩
  inv := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩

中文:
定义 toActionFromAction
  签名: (X : TopRep.{w} k G)
  定义体: ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩
  inv := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id
-/
def toActionFromAction (X : TopRep.{w} k G) :
    fromActionTopModFunc.obj (toActionTopModFunc.obj X) ≅ X where
  hom := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩
  inv := ofHom ⟨ContinuousLinearMap.id k X.V, fun _ => rfl⟩

/--
Definition of `fromActionToAction` / `fromActionToAction` 的定义

English:
definition fromActionToAction
  signature: (X : Action (TopModuleCat.{w} k) G)
  body: ⟨𝟙 _, fun _ => rfl⟩
  inv := ⟨𝟙 _, fun _ => rfl⟩

中文:
定义 fromActionToAction
  签名: (X : Action (TopModuleCat.{w} k) G)
  定义体: ⟨𝟙 _, fun _ => rfl⟩
  inv := ⟨𝟙 _, fun _ => rfl⟩
-/
def fromActionToAction (X : Action (TopModuleCat.{w} k) G) :
    toActionTopModFunc.obj (fromActionTopModFunc.obj X) ≅ X where
  hom := ⟨𝟙 _, fun _ => rfl⟩
  inv := ⟨𝟙 _, fun _ => rfl⟩

/--
Definition of `TopRepEquivActionTop` / `TopRepEquivActionTop` 的定义

English:
definition TopRepEquivActionTop
  signature: : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G where
  body: toActionTopModFunc
  inverse := fromActionTopModFunc
  unitIso := NatIso.ofComponents toActionFromAction
  counitIso := NatIso.ofComponents fromActionToAction

中文:
定义 TopRepEquivActionTop
  签名: : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G where
  定义体: toActionTopModFunc
  inverse := fromActionTopModFunc
  unitIso := NatIso.ofComponents toActionFromAction
  counitIso := NatIso.ofComponents fromActionToAction

Depends on / 依赖: toActionTopModFunc
-/
def TopRepEquivActionTop : TopRep.{w} k G ≌ Action (TopModuleCat.{w} k) G where
  functor := toActionTopModFunc
  inverse := fromActionTopModFunc
  unitIso := NatIso.ofComponents toActionFromAction
  counitIso := NatIso.ofComponents fromActionToAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toActionTopModFunc (k := k) (G := G)).IsEquivalence
  body: TopRepEquivActionTop (k := k) (G := G).isEquivalence_functor

中文:
实例 :
  签名: (toActionTopModFunc (k := k) (G := G)).IsEquivalence
  定义体: TopRepEquivActionTop (k := k) (G := G).isEquivalence_functor

Depends on / 依赖: IsEquivalence
-/
instance : (toActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromActionTopModFunc (k := k) (G := G)).IsEquivalence
  body: TopRepEquivActionTop (k := k) (G := G).isEquivalence_inverse

中文:
实例 :
  签名: (fromActionTopModFunc (k := k) (G := G)).IsEquivalence
  定义体: TopRepEquivActionTop (k := k) (G := G).isEquivalence_inverse

Depends on / 依赖: IsEquivalence
-/
instance : (fromActionTopModFunc (k := k) (G := G)).IsEquivalence :=
  TopRepEquivActionTop (k := k) (G := G).isEquivalence_inverse

end equivAction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
Definition of `invariants` / `invariants` 的定义

English:
abbreviation invariants
  signature: (X : TopRep k G)
  body: .of k X.ρ.invariants

中文:
缩写 invariants
  签名: (X : TopRep k G)
  定义体: .of k X.ρ.invariants

Depends on / 依赖: invariants
-/
abbrev invariants (X : TopRep k G) : TopModuleCat k := .of k X.ρ.invariants

variable (k G) in
/--
Definition of `invariantsFunctor` / `invariantsFunctor` 的定义

English:
abbreviation invariantsFunctor
  signature: : TopRep k G ⥤ TopModuleCat k where
  body: .of k A.ρ.invariants
  map f := TopModuleCat.ofHom f.hom.mapInvariants

中文:
缩写 invariantsFunctor
  签名: : TopRep k G ⥤ TopModuleCat k where
  定义体: .of k A.ρ.invariants
  map f := TopModuleCat.ofHom f.hom.mapInvariants

Depends on / 依赖: invariants
-/
abbrev invariantsFunctor : TopRep k G ⥤ TopModuleCat k where
  obj A := .of k A.ρ.invariants
  map f := TopModuleCat.ofHom f.hom.mapInvariants

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invariantsFunctor k G).Additive

中文:
实例 :
  签名: (invariantsFunctor k G).Additive
-/
instance : (invariantsFunctor k G).Additive where

instance {k : Type u} [CommRing k] [TopologicalSpace k] : (invariantsFunctor k G).Linear k where

/--
Definition of `coind₁` / `coind₁` 的定义

English:
abbreviation coind₁
  signature: (A : TopRep k G)
  body: of A.ρ.coind₁

中文:
缩写 coind₁
  签名: (A : TopRep k G)
  定义体: of A.ρ.coind₁
-/
abbrev coind₁ (A : TopRep k G) : TopRep k G := of A.ρ.coind₁

variable (k G) in
/--
Definition of `coind₁Functor` / `coind₁Functor` 的定义

English:
abbreviation coind₁Functor
  signature: : TopRep k G ⥤ TopRep k G where
  body: coind₁
map φ := ofHom ContRepresentation.coind₁Map φ.hom

中文:
缩写 coind₁Functor
  签名: : TopRep k G ⥤ TopRep k G where
  定义体: coind₁
map φ := ofHom ContRepresentation.coind₁Map φ.hom

Depends on / 依赖: Subsingleton, Subsingleton.elim, iff_comp_injective
-/
abbrev coind₁Functor : TopRep k G ⥤ TopRep k G where
  obj := coind₁
map φ := ofHom ContRepresentation.coind₁Map φ.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopRep.coind₁Functor k G).Additive

中文:
实例 :
  签名: (TopRep.coind₁Functor k G).Additive
-/
instance : (TopRep.coind₁Functor k G).Additive where

instance {k : Type u} [CommRing k] [TopologicalSpace k] : (coind₁Functor k G).Linear k where

/-- The constant function `rep ⟶ C(G, rep)` as a natural transformation. -/
@[implicit_reducible, simps]
/--
Definition of `coind₁ι` / `coind₁ι` 的定义

English:
definition coind₁ι
  signature: : 𝟭 (TopRep k G) ⟶ coind₁Functor k G where
  body: ofHom rep.ρ.coind₁ι

中文:
定义 coind₁ι
  签名: : 𝟭 (TopRep k G) ⟶ coind₁Functor k G where
  定义体: ofHom rep.ρ.coind₁ι
-/
def coind₁ι : 𝟭 (TopRep k G) ⟶ coind₁Functor k G where
  app rep := ofHom rep.ρ.coind₁ι

/--
Definition of `res` / `res` 的定义

English:
abbreviation res
  signature: {H : Type*} [Monoid H] (φ : H ->* G) (A : TopRep k G)
  body: of (A.ρ.restrict φ)

中文:
缩写 res
  签名: {H : 类型} [Monoid H] (φ : H ->* G) (A : TopRep k G)
  定义体: of (A.ρ.restrict φ)

Depends on / 依赖: restrict
-/
abbrev res {H : Type*} [Monoid H] (φ : H ->* G) (A : TopRep k G) : TopRep k H := of (A.ρ.restrict φ)

/--
Definition of `resFunctor` / `resFunctor` 的定义

English:
abbreviation resFunctor
  signature: {H : Type*} [Monoid H] (φ : H ->* G)
  body: res φ
map f := ofHom f.hom.restrict φ

中文:
缩写 resFunctor
  签名: {H : 类型} [Monoid H] (φ : H ->* G)
  定义体: res φ
map f := ofHom f.hom.restrict φ
-/
abbrev resFunctor {H : Type*} [Monoid H] (φ : H ->* G) :
    TopRep k G ⥤ TopRep k H where
  obj := res φ
map f := ofHom f.hom.restrict φ

section invariantsResMap

variable {G H : Type*} [Group G]

@[simp]
/--
lemma `resFunctor_map_hom` / 引理 `resFunctor_map_hom`

English:
lemma resFunctor_map_hom
  given: [Monoid H] (φ : H ->* G) {A B : TopRep k G} (f : A ⟶ B)
  proof: rfl

中文:
引理 resFunctor_map_hom
  条件: [Monoid H] (φ : H ->* G) {A B : TopRep k G} (f : A ⟶ B)
  证明: rfl
-/
lemma resFunctor_map_hom [Monoid H] (φ : H ->* G) {A B : TopRep k G} (f : A ⟶ B) :
    ((resFunctor φ).map f).hom = f.hom.restrict φ := rfl

variable [Group H]

/--
Definition of `invariantsResMap` / `invariantsResMap` 的定义

English:
definition invariantsResMap
  signature: (φ : H ->* G) {X : TopRep k G} {Y : TopRep k H} (f : res φ X ⟶ Y)
  body: TopModuleCat.ofHom (f.hom.mapInvariantsOfRes φ)

中文:
定义 invariantsResMap
  签名: (φ : H ->* G) {X : TopRep k G} {Y : TopRep k H} (f : res φ X ⟶ Y)
  定义体: TopModuleCat.ofHom (f.hom.mapInvariantsOfRes φ)

Depends on / 依赖: TopModuleCat, TopModuleCat.ofHom, f.hom.mapInvariantsOfRes, mapInvariantsOfRes
-/
def invariantsResMap (φ : H ->* G) {X : TopRep k G} {Y : TopRep k H} (f : res φ X ⟶ Y) :
    X.invariants ⟶ Y.invariants :=
  TopModuleCat.ofHom (f.hom.mapInvariantsOfRes φ)

/--
lemma `invariantsResMap_comp` / 引理 `invariantsResMap_comp`

English:
lemma invariantsResMap_comp
  statement: {X : TopRep k G} {Y Y' : TopRep k H} (φ : H ->* G)
  proof: rfl

中文:
引理 invariantsResMap_comp
  结论: {X : TopRep k G} {Y Y' : TopRep k H} (φ : H ->* G)
  证明: rfl
-/
lemma invariantsResMap_comp {X : TopRep k G} {Y Y' : TopRep k H} (φ : H ->* G)
    (f : res φ X ⟶ Y) (g : Y ⟶ Y') :
    invariantsResMap φ (f ≫ g) = invariantsResMap φ f ≫ (invariantsFunctor k H).map g := rfl

/--
lemma `invariantsResMap_map_comp` / 引理 `invariantsResMap_map_comp`

English:
lemma invariantsResMap_map_comp
  statement: {X X' : TopRep k G} {Y : TopRep k H} (φ : H ->* G)
  proof: rfl

中文:
引理 invariantsResMap_map_comp
  结论: {X X' : TopRep k G} {Y : TopRep k H} (φ : H ->* G)
  证明: rfl
-/
lemma invariantsResMap_map_comp {X X' : TopRep k G} {Y : TopRep k H} (φ : H ->* G)
    (f : X ⟶ X') (g : res φ X' ⟶ Y) :
    invariantsResMap φ ((resFunctor φ).map f ≫ g) =
      (invariantsFunctor k G).map f ≫ invariantsResMap φ g := rfl

end invariantsResMap

end TopRep
