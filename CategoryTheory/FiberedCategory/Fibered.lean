/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)fibered.

## Main definitions

- `IsPreFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that any morphism in the base `𝒮` can be lifted to a Cartesian morphism in `𝒳`.

- `IsFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
  This means that it is prefibered, and that the composition of any two Cartesian morphisms is
  Cartesian.

In the literature one often sees the notion of a fibered category defined as the existence of
strongly Cartesian morphisms lying over any given morphism in the base. This is equivalent to the
notion above, and we give an alternate constructor `IsFibered.of_exists_isCartesian'` for
constructing a fibered category this way.

## Implementation

The constructor of `IsPreFibered` is called `exists_isCartesian'`. The reason for the prime is that
when wanting to apply this condition, it is recommended to instead use the lemma
`exists_isCartesian` (without the prime), which is more applicable with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/--
Definition of `Functor.IsPreFibered` / `Functor.IsPreFibered` 的定义

English:
class Functor.IsPreFibered
  parameters: (p : 𝒳 ⥤ 𝒮)
  axioms and operations (1):
    - exists_isCartesian'({a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a)) : exists (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

中文:
类 函子.是PreFibered
  参数: (p : 𝒳 ⥤ 𝒮)
  公理与运算 (1 个):
    - exists_isCartesian'({a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a)) : 存在 (b : 𝒳) (φ : b ⟶ a), 是Cartesian p f φ

Depends on / 依赖: IsPreFibered, IsPreFibered.exists_isCartesian, exists_isCartesian
-/
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  exists_isCartesian' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : exists (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

/--
lemma `IsPreFibered.exists_isCartesian` / 引理 `IsPreFibered.exists_isCartesian`

English:
lemma IsPreFibered.exists_isCartesian
  statement: (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
  proof: by
  subst ha; exact IsPreFibered.exists_isCartesian' f

中文:
引理 是PreFibered.存在_isCartesian
  结论: (p : 𝒳 ⥤ 𝒮) [p.是PreFibered] {a : 𝒳} {R S : 𝒮}
  证明: by
  subst ha; exact IsPreFibered.exists_isCartesian' f
-/
protected lemma IsPreFibered.exists_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : exists (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.exists_isCartesian' f

/--
Definition of `Functor.IsFibered` / `Functor.IsFibered` 的定义

English:
class Functor.IsFibered
  parameters: (p : 𝒳 ⥤ 𝒮)
  extends: IsPreFibered p
  axioms and operations (1):
    - comp({R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [IsCartesian p f φ] [IsCartesian p g ψ]) : IsCartesian p (f ≫ g) (φ ≫ ψ)

中文:
类 函子.是Fibered
  参数: (p : 𝒳 ⥤ 𝒮)
  继承: 是PreFibered p
  公理与运算 (1 个):
    - comp({R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) [是Cartesian p f φ] [是Cartesian p g ψ]) : 是Cartesian p (f ≫ g) (φ ≫ ψ)
-/
class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) : Prop extends IsPreFibered p where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)

instance (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ) :=
  IsFibered.comp f g φ ψ

namespace Functor.IsPreFibered

variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

/--
Definition of `pullbackObj` / `pullbackObj` 的定义

English:
definition pullbackObj
  signature: : 𝒳
  body: Classical.choose (IsPreFibered.exists_isCartesian p ha f)

中文:
定义 pullbackObj
  签名: : 𝒳
  定义体: Classical.choose (IsPreFibered.exists_isCartesian p ha f)

Depends on / 依赖: Classical, Classical.choose, IsPreFibered, IsPreFibered.exists_isCartesian, exists_isCartesian
-/
noncomputable def pullbackObj : 𝒳 :=
  Classical.choose (IsPreFibered.exists_isCartesian p ha f)

/--
Definition of `pullbackMap` / `pullbackMap` 的定义

English:
definition pullbackMap
  signature: : pullbackObj ha f ⟶ a
  body: Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

中文:
定义 pullbackMap
  签名: : pullbackObj ha f ⟶ a
  定义体: Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, IsPreFibered, IsPreFibered.exists_isCartesian, choose_spec, exists_isCartesian
-/
noncomputable def pullbackMap : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

/--
Instance `pullbackMap.IsCartesian` / 实例 `pullbackMap.IsCartesian`

English:
instance pullbackMap.IsCartesian
  signature: : IsCartesian p f (pullbackMap ha f)
  body: Classical.choose_spec (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

中文:
实例 pullbackMap.是Cartesian
  签名: : 是Cartesian p f (pullbackMap ha f)
  定义体: Classical.choose_spec (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

Depends on / 依赖: Classical, Classical.choose_spec, IsPreFibered, IsPreFibered.exists_isCartesian, choose_spec, exists_isCartesian
-/
instance pullbackMap.IsCartesian : IsCartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreFibered.exists_isCartesian p ha f))

/--
lemma `pullbackObj_proj` / 引理 `pullbackObj_proj`

English:
lemma pullbackObj_proj
  statement: p.obj (pullbackObj ha f) = R
  proof: domain_eq p f (pullbackMap ha f)

中文:
引理 pullbackObj_proj
  结论: p.obj (pullbackObj ha f) = R
  证明: domain_eq p f (pullbackMap ha f)

Depends on / 依赖: domain_eq, pullbackMap
-/
lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end Functor.IsPreFibered

namespace Functor.IsFibered

open IsCartesian Functor.IsPreFibered

/--
Instance `isStronglyCartesian_of_isCartesian` / 实例 `isStronglyCartesian_of_isCartesian`

English:
instance isStronglyCartesian_of_isCartesian
  signature: (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)
  body: by
    -- Let `ψ` be a Cartesian arrow lying over `g`
    let ψ := pullbackMap (domain_eq p f φ) g
    -- Let `τ` be the map induced by the universal property of `ψ ≫ φ`.
    let τ := IsCartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    -- It is easily verified that `τ ≫ ψ` lifts `g` and `τ ≫ ψ ≫ φ = φ'`
    refine ⟨⟨inferInstance, by simp only [assoc, IsCartesian.fac, τ]⟩, ?_⟩
    -- It remains to check that `τ ≫ ψ` is unique.
    -- So fix another lift `π` of `g` satisfying `π ≫ φ = φ'`.
    intro π ⟨hπ, hπ_comp⟩
    -- Write `π` as `π = τ' ≫ ψ` for some `τ'` induced by the universal property of `ψ`.
    rw [← fac p g ψ π]
    -- It remains to show that `τ' = τ`. This follows again from the universal property of `ψ`.
    congr 1
    apply map_uniq
    rwa [← assoc, IsCartesian.fac]

中文:
实例 isStronglyCartesian_of_isCartesian
  签名: (p : 𝒳 ⥤ 𝒮) [p.是Fibered] {R S : 𝒮} (f : R ⟶ S)
  定义体: by
    -- Let `ψ` be a Cartesian arrow lying over `g`
    let ψ := pullbackMap (domain_eq p f φ) g
    -- Let `τ` be the map induced by the universal property of `ψ ≫ φ`.
    let τ := IsCartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    -- It is easily verified that `τ ≫ ψ` lifts `g` and `τ ≫ ψ ≫ φ = φ'`
    refine ⟨⟨inferInstance, by simp only [assoc, IsCartesian.fac, τ]⟩, ?_⟩
    -- It remains to check that `τ ≫ ψ` is unique.
    -- So fix another lift `π` of `g` satisfying `π ≫ φ = φ'`.
    intro π ⟨hπ, hπ_comp⟩
    -- Write `π` as `π = τ' ≫ ψ` for some `τ'` induced by the universal property of `ψ`.
    rw [← fac p g ψ π]
    -- It remains to show that `τ' = τ`. This follows again from the universal property of `ψ`.
    congr 1
    apply map_uniq
    rwa [← assoc, IsCartesian.fac]
-/
instance isStronglyCartesian_of_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ where
  universal_property' g φ' hφ' := by
    -- Let `ψ` be a Cartesian arrow lying over `g`
    let ψ := pullbackMap (domain_eq p f φ) g
    -- Let `τ` be the map induced by the universal property of `ψ ≫ φ`.
    let τ := IsCartesian.map p (g ≫ f) (ψ ≫ φ) φ'
    use τ ≫ ψ
    -- It is easily verified that `τ ≫ ψ` lifts `g` and `τ ≫ ψ ≫ φ = φ'`
    refine ⟨⟨inferInstance, by simp only [assoc, IsCartesian.fac, τ]⟩, ?_⟩
    -- It remains to check that `τ ≫ ψ` is unique.
    -- So fix another lift `π` of `g` satisfying `π ≫ φ = φ'`.
    intro π ⟨hπ, hπ_comp⟩
    -- Write `π` as `π = τ' ≫ ψ` for some `τ'` induced by the universal property of `ψ`.
    rw [← fac p g ψ π]
    -- It remains to show that `τ' = τ`. This follows again from the universal property of `ψ`.
    congr 1
    apply map_uniq
    rwa [← assoc, IsCartesian.fac]

/--
lemma `isStronglyCartesian_of_exists_isCartesian` / 引理 `isStronglyCartesian_of_exists_isCartesian`

English:
lemma isStronglyCartesian_of_exists_isCartesian
  statement: (p : 𝒳 ⥤ 𝒮) (h : forall (a : 𝒳) (R : 𝒮)
  proof: by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a Cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCartesian.map p (p.map φ) ψ (f' := g ≫ p.map φ) rfl φ'
  -- Let `Φ : a' ≅ a` be natural isomorphism induced between `φ` and `ψ`.
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  -- The map induced by `φ` will be `τ' ≫ Φ.hom`
  use τ' ≫ Φ.hom
  -- It is easily verified that `τ' ≫ Φ.hom` lifts `g` and `τ' ≫ Φ.hom ≫ φ = φ'`
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ]
  -- It remains to check that it is unique. This follows from the universal property of `ψ`.
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]

中文:
引理 isStronglyCartesian_of_存在_isCartesian
  结论: (p : 𝒳 ⥤ 𝒮) (h : 对任意 (a : 𝒳) (R : 𝒮)
  证明: by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a Cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCartesian.map p (p.map φ) ψ (f' := g ≫ p.map φ) rfl φ'
  -- Let `Φ : a' ≅ a` be natural isomorphism induced between `φ` and `ψ`.
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  -- The map induced by `φ` will be `τ' ≫ Φ.hom`
  use τ' ≫ Φ.hom
  -- It is easily verified that `τ' ≫ Φ.hom` lifts `g` and `τ' ≫ Φ.hom ≫ φ = φ'`
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ]
  -- It remains to check that it is unique. This follows from the universal property of `ψ`.
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]

Depends on / 依赖: subst_hom_lift
-/
lemma isStronglyCartesian_of_exists_isCartesian (p : 𝒳 ⥤ 𝒮) (h : forall (a : 𝒳) (R : 𝒮)
    (f : R ⟶ p.obj a), exists (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) {R S : 𝒮} (f : R ⟶ S)
      {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ := by
  constructor
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a Cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCartesian.map p (p.map φ) ψ (f' := g ≫ p.map φ) rfl φ'
  -- Let `Φ : a' ≅ a` be natural isomorphism induced between `φ` and `ψ`.
  let Φ := domainUniqueUpToIso p (p.map φ) φ ψ
  -- The map induced by `φ` will be `τ' ≫ Φ.hom`
  use τ' ≫ Φ.hom
  -- It is easily verified that `τ' ≫ Φ.hom` lifts `g` and `τ' ≫ Φ.hom ≫ φ = φ'`
  refine ⟨⟨by simp only [Φ]; infer_instance, ?_⟩, ?_⟩
  · simp [τ', Φ]
  -- It remains to check that it is unique. This follows from the universal property of `ψ`.
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  apply IsStronglyCartesian.map_uniq p (p.map φ) ψ rfl φ'
  simp [hπ_comp, Φ]

/--
lemma `of_exists_isStronglyCartesian` / 引理 `of_exists_isStronglyCartesian`

English:
lemma of_exists_isStronglyCartesian
  statement: {p : 𝒳 ⥤ 𝒮}
  proof: by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCartesian f φ := isStronglyCartesian_of_exists_isCartesian p h _ _
    have : p.IsStronglyCartesian g ψ := isStronglyCartesian_of_exists_isCartesian p h _ _
    inferInstance

中文:
引理 of_存在_isStronglyCartesian
  结论: {p : 𝒳 ⥤ 𝒮}
  证明: by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCartesian f φ := isStronglyCartesian_of_exists_isCartesian p h _ _
    have : p.IsStronglyCartesian g ψ := isStronglyCartesian_of_exists_isCartesian p h _ _
    inferInstance

Depends on / 依赖: IsStronglyCartesian, isStronglyCartesian_of_exists_isCartesian, p.IsStronglyCartesian
-/
lemma of_exists_isStronglyCartesian {p : 𝒳 ⥤ 𝒮}
    (h : forall (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
      exists (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) :
    IsFibered p where
  exists_isCartesian' := by
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := fun R S T f g {a b c} φ ψ _ _ =>
    have : p.IsStronglyCartesian f φ := isStronglyCartesian_of_exists_isCartesian p h _ _
    have : p.IsStronglyCartesian g ψ := isStronglyCartesian_of_exists_isCartesian p h _ _
    inferInstance

/--
Definition of `pullbackPullbackIso` / `pullbackPullbackIso` 的定义

English:
definition pullbackPullbackIso
  signature: {p : 𝒳 ⥤ 𝒮} [IsFibered p]
  body: domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

中文:
定义 pullbackPullbackIso
  签名: {p : 𝒳 ⥤ 𝒮} [是Fibered p]
  定义体: domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

Depends on / 依赖: domainUniqueUpToIso, pullbackMap, pullbackObj_proj
-/
noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p]
    {R S T : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  domainUniqueUpToIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

end Functor.IsFibered

end CategoryTheory
