/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Cartesian morphisms

This file defines Cartesian resp. strongly Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted to `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCartesian p f φ` expresses that `φ` is a Cartesian morphism lying over `f` with respect to `p` in
the sense of SGA 1 VI 5.1. This means that for any morphism `φ' : a' ⟶ b` lying over `f` there is
a unique morphism `τ : a' ⟶ a` lying over `𝟙 R`, such that `φ' = τ ≫ φ`.

`IsStronglyCartesian p f φ` expresses that `φ` is a strongly Cartesian morphism lying over `f` with
respect to `p`, see <https://stacks.math.columbia.edu/tag/02XK>.

## Implementation

The constructor of `IsStronglyCartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
* [Stacks: Fibred Categories](https://stacks.math.columbia.edu/tag/02XJ)
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/--
Definition of `IsCartesian` / `IsCartesian` 的定义

English:
class IsCartesian
  parameters: : Prop where
  axioms and operations (2):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property({a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']) : exists! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

中文:
类 是Cartesian
  参数: : 命题 where
  公理与运算 (2 个):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property({a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']) : 存在! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'
-/
class IsCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      exists! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'
attribute [instance] IsCartesian.toIsHomLift

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly Cartesian if for
all morphisms `φ' : a' ⟶ b` and all diagrams of the form
```
a' a --φ--> b
| | |
v v v
R' --g--> R --f--> S
```
such that `φ'` lifts `g ≫ f`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
/--
Definition of `IsStronglyCartesian` / `IsStronglyCartesian` 的定义

English:
class IsStronglyCartesian
  parameters: : Prop where
  axioms and operations (2):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property'({a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ']) : exists! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'

中文:
类 是StronglyCartesian
  参数: : 命题 where
  公理与运算 (2 个):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property'({a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ']) : 存在! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'
-/
class IsStronglyCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ'] :
      exists! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'
attribute [instance] IsStronglyCartesian.toIsHomLift

end

namespace IsCartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]

section

variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def map
  body: Classical.choose IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'

中文:
定义 noncomputable
  签名: def map
  定义体: Classical.choose IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'
-/
protected noncomputable def map : a' ⟶ a :=
Classical.choose IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'

/--
Instance `map_isHomLift` / 实例 `map_isHomLift`

English:
instance map_isHomLift
  signature: : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ')
  body: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]

中文:
实例 map_isHomLift
  签名: : IsHomLift p (𝟙 R) (是Cartesian.map p f φ φ')
  定义体: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]

Depends on / 依赖: Classical, Classical.choose_spec, IsCartesian, IsCartesian.universal_property, choose_spec, universal_property
-/
instance map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  statement: IsCartesian.map p f φ φ' ≫ φ = φ'
  proof: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

中文:
引理 fac
  结论: 是Cartesian.map p f φ φ' ≫ φ = φ'
  证明: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

Depends on / 依赖: Classical, Classical.choose_spec, IsCartesian, IsCartesian.universal_property, choose_spec, universal_property
-/
lemma fac : IsCartesian.map p f φ φ' ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/--
lemma `map_uniq` / 引理 `map_uniq`

English:
lemma map_uniq
  given: (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ')
  proof: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

中文:
引理 map_uniq
  条件: (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ')
  证明: (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

Depends on / 依赖: Classical, Classical.choose_spec, IsCartesian, IsCartesian.universal_property, choose_spec, universal_property
-/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = IsCartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
  proof: by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (ψ ≫ φ) ψ' h.symm]

@[simp]

中文:
引理 ext
  结论: (φ : a ⟶ b) [是Cartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
  证明: by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (ψ ≫ φ) ψ' h.symm]

@[simp]
-/
protected lemma ext (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (ψ ≫ φ) ψ' h.symm]

@[simp]
/--
lemma `map_self` / 引理 `map_self`

English:
lemma map_self
  statement: IsCartesian.map p f φ φ = 𝟙 a
  proof: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

中文:
引理 map_self
  结论: 是Cartesian.map p f φ φ = 𝟙 a
  证明: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

Depends on / 依赖: id_comp, map_uniq, subst_hom_lift
-/
lemma map_self : IsCartesian.map p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

/--
Instance `of_comp_iso` / 实例 `of_comp_iso`

English:
instance of_comp_iso
  signature: {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom]
  body: by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp only [fac_assoc, assoc, Iso.inv_hom_id, comp_id]⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    rw [Iso.eq_comp_inv]
    simp only [assoc, hτ₂]

中文:
实例 of_comp_iso
  签名: {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom]
  定义体: by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp only [fac_assoc, assoc, Iso.inv_hom_id, comp_id]⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    rw [Iso.eq_comp_inv]
    simp only [assoc, hτ₂]

Depends on / 依赖: IsCartesian, IsCartesian.map, Iso.eq_comp_inv, Iso.inv_hom_id, comp_id, eq_comp_inv, fac_assoc, inv_hom_id, map_uniq
-/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp only [fac_assoc, assoc, Iso.inv_hom_id, comp_id]⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    rw [Iso.eq_comp_inv]
    simp only [assoc, hτ₂]

/-- The canonical isomorphism between the domains of two Cartesian arrows
lying over the same object. -/
@[simps]
/--
Definition of `domainUniqueUpToIso` / `domainUniqueUpToIso` 的定义

English:
definition domainUniqueUpToIso
  signature: {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ']
  body: IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp

中文:
定义 domainUniqueUpToIso
  签名: {a' : 𝒳} (φ' : a' ⟶ b) [是Cartesian p f φ']
  定义体: IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp

Depends on / 依赖: IsCartesian, IsCartesian.map
-/
noncomputable def domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a where
  hom := IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp]

/--
Instance `domainUniqueUpToIso_inv_isHomLift` / 实例 `domainUniqueUpToIso_inv_isHomLift`

English:
instance domainUniqueUpToIso_inv_isHomLift
  signature: {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ']
  body: domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'

中文:
实例 domainUniqueUpToIso_inv_isHomLift
  签名: {a' : 𝒳} (φ' : a' ⟶ b) [是Cartesian p f φ']
  定义体: domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'

Depends on / 依赖: IsCartesian, IsCartesian.map_isHomLift, domainUniqueUpToIso_hom, map_isHomLift
-/
instance domainUniqueUpToIso_inv_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').hom :=
  domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'

/--
Instance `domainUniqueUpToIso_hom_isHomLift` / 实例 `domainUniqueUpToIso_hom_isHomLift`

English:
instance domainUniqueUpToIso_hom_isHomLift
  signature: {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ']
  body: domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ

中文:
实例 domainUniqueUpToIso_hom_isHomLift
  签名: {a' : 𝒳} (φ' : a' ⟶ b) [是Cartesian p f φ']
  定义体: domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ

Depends on / 依赖: IsCartesian, IsCartesian.map_isHomLift, domainUniqueUpToIso_inv, map_isHomLift
-/
instance domainUniqueUpToIso_hom_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').inv :=
  domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ

/--
Instance `of_iso_comp` / 实例 `of_iso_comp`

English:
instance of_iso_comp
  signature: {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom]
  body: by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

中文:
实例 of_iso_comp
  签名: {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom]
  定义体: by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

Depends on / 依赖: IsCartesian, IsCartesian.map, Iso.eq_comp_inv, eq_comp_inv, map_uniq
-/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

end IsCartesian

namespace IsStronglyCartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCartesian p f φ]

/--
lemma `universal_property` / 引理 `universal_property`

English:
lemma universal_property
  statement: {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
  proof: by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f

中文:
引理 universal_property
  结论: {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
  证明: by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f

Depends on / 依赖: IsHomLift, IsStronglyCartesian, IsStronglyCartesian.universal_property, p.IsHomLift, subst_hom_lift, universal_property
-/
lemma universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : exists! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f

/--
Instance `isCartesian_of_isStronglyCartesian` / 实例 `isCartesian_of_isStronglyCartesian`

English:
instance isCartesian_of_isStronglyCartesian
  signature: : p.IsCartesian f φ where
  body: fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

中文:
实例 isCartesian_of_isStronglyCartesian
  签名: : p.是Cartesian f φ where
  定义体: fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

Depends on / 依赖: universal_property
-/
instance isCartesian_of_isStronglyCartesian : p.IsCartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

section

variable {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f) (φ' : a' ⟶ b)
  [IsHomLift p f' φ']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : a' ⟶ a
  body: Classical.choose universal_property p f φ _ _ hf' φ'

中文:
定义 map
  签名: : a' ⟶ a
  定义体: Classical.choose universal_property p f φ _ _ hf' φ'

Depends on / 依赖: Classical, Classical.choose, universal_property
-/
noncomputable def map : a' ⟶ a :=
Classical.choose universal_property p f φ _ _ hf' φ'

/--
Instance `map_isHomLift` / 实例 `map_isHomLift`

English:
instance map_isHomLift
  signature: : IsHomLift p g (map p f φ hf' φ')
  body: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]

中文:
实例 map_isHomLift
  签名: : IsHomLift p g (map p f φ hf' φ')
  定义体: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, universal_property
-/
instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  statement: (map p f φ hf' φ') ≫ φ = φ'
  proof: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

中文:
引理 fac
  结论: (map p f φ hf' φ') ≫ φ = φ'
  证明: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, universal_property
-/
lemma fac : (map p f φ hf' φ') ≫ φ = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

/--
lemma `map_uniq` / 引理 `map_uniq`

English:
lemma map_uniq
  given: (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ')
  statement: ψ = map p f φ hf' φ'
  proof: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

中文:
引理 map_uniq
  条件: (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ')
  结论: ψ = map p f φ hf' φ'
  证明: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, universal_property
-/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
  proof: by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]

@[simp]

中文:
引理 ext
  结论: (φ : a ⟶ b) [是StronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
  证明: by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]

@[simp]
-/
protected lemma ext (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
    {ψ ψ' : a' ⟶ a} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]

@[simp]
/--
lemma `map_self` / 引理 `map_self`

English:
lemma map_self
  statement: map p f φ (id_comp f).symm φ = 𝟙 a
  proof: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

中文:
引理 map_self
  结论: map p f φ (id_comp f).symm φ = 𝟙 a
  证明: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

Depends on / 依赖: id_comp, map_uniq, subst_hom_lift
-/
lemma map_self : map p f φ (id_comp f).symm φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

/-- When its possible to compare the two, the composition of two `IsStronglyCartesian.map` will also
be given by a `IsStronglyCartesian.map`. In other words, given diagrams
```
a'' a' a --φ--> b
| | | |
v v v v
R'' --g'--> R' --g--> R --f--> S
```
and
```
a' --φ'--> b
| |
v v
R' --f'--> S
```
and
```
a'' --φ''--> b
| |
v v
R'' --f''--> S
```
such that `φ` and `φ'` are strongly Cartesian morphisms, and such that `f' = g ≫ f` and
`f'' = g' ≫ f'`. Then composing the induced map from `a'' ⟶ a'` with the induced map from
`a' ⟶ a` gives the induced map from `a'' ⟶ a`. -/
@[reassoc (attr := simp)]
/--
lemma `map_comp_map` / 引理 `map_comp_map`

English:
lemma map_comp_map
  statement: {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
  proof: by
  apply map_uniq p f φ
  simp only [assoc, fac]

中文:
引理 map_comp_map
  结论: {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
  证明: by
  apply map_uniq p f φ
  simp only [assoc, fac]

Depends on / 依赖: map_uniq
-/
lemma map_comp_map {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
    {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ'' : a'' ⟶ b)
    [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f' φ' H' φ'' ≫ map p f φ H φ' =
      map p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ]
  body: by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]

中文:
实例 comp
  签名: [是StronglyCartesian p f φ] [是StronglyCartesian p g ψ]
  定义体: by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]

Depends on / 依赖: map_uniq
-/
instance comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
    IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
  proof: by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    /- We get a morphism `π : a' ⟶ a` such that `π ≫ φ ≫ ψ = τ ≫ ψ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ 

中文:
引理 of_comp
  结论: [是StronglyCartesian p g ψ] [是StronglyCartesian p (f ≫ g) (φ ≫ ψ)]
  证明: by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    /- We get a morphism `π : a' ⟶ a` such that `π ≫ φ ≫ ψ = τ ≫ ψ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ 
-/
protected lemma of_comp [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p f φ] : IsStronglyCartesian p f φ where
  universal_property' := by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    /- We get a morphism `π : a' ⟶ a` such that `π ≫ φ ≫ ψ = τ ≫ ψ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := h ≫ f ≫ g) rfl (τ ≫ ψ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `π ≫ φ = τ` follows from `π ≫ φ ≫ ψ = τ ≫ ψ` and the universal property of
    `ψ`. -/
    · apply IsStronglyCartesian.ext p g ψ (h ≫ f) (by simp)
    -- Finally, the uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

/--
Instance `of_iso` / 实例 `of_iso`

English:
instance of_iso
  signature: (φ : a ≅ b) [IsHomLift p f φ.hom]
  body: by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by cat_disch⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)

中文:
实例 of_iso
  签名: (φ : a ≅ b) [IsHomLift p f φ.hom]
  定义体: by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by cat_disch⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)

Depends on / 依赖: IsHomLift, IsHomLift.comp, cat_disch, isoOfIsoLift
-/
instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom where
  universal_property' := by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by cat_disch⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)

/--
Instance `of_isIso` / 实例 `of_isIso`

English:
instance of_isIso
  signature: (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ]
  body: @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

中文:
实例 of_isIso
  签名: (φ : a ⟶ b) [IsHomLift p f φ] [是同构 φ]
  定义体: @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

Depends on / 依赖: IsStronglyCartesian, IsStronglyCartesian.of_iso, of_iso
-/
instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f φ :=
  @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/--
lemma `isIso_of_base_isIso` / 引理 `isIso_of_base_isIso`

English:
lemma isIso_of_base_isIso
  given: (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f]
  statement: IsIso φ
  proof: by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ` be the morphism induced by applying universal property to `𝟙 b` lying over `f⁻¹ ≫ f`.
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property.
  have inv_h

中文:
引理 isIso_of_base_isIso
  条件: (φ : a ⟶ b) [是StronglyCartesian p f φ] [是同构 f]
  结论: 是同构 φ
  证明: by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ` be the morphism induced by applying universal property to `𝟙 b` lying over `f⁻¹ ≫ f`.
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property.
  have inv_h

Depends on / 依赖: subst_hom_lift
-/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ` be the morphism induced by applying universal property to `𝟙 b` lying over `f⁻¹ ≫ f`.
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property.
  have inv_hom : φ' ≫ φ = 𝟙 b := fac p (p.map φ) φ _ (𝟙 b)
  refine ⟨?_, inv_hom⟩
  -- We will now show that `φ ≫ φ' = 𝟙 a` by showing that `(φ ≫ φ') ≫ φ = 𝟙 a ≫ φ`.
  have h₁ : IsHomLift p (𝟙 (p.obj a)) (φ ≫ φ') := by
    rw [← IsIso.hom_inv_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCartesian.ext p (p.map φ) φ (𝟙 (p.obj a))
  simp only [assoc, inv_hom, comp_id, id_comp]

end

section

variable {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}

/-- The canonical isomorphism between the domains of two strongly Cartesian morphisms lying over
isomorphic objects. -/
@[simps]
/--
Definition of `domainIsoOfBaseIso` / `domainIsoOfBaseIso` 的定义

English:
definition domainIsoOfBaseIso
  signature: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  body: map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

中文:
定义 domainIsoOfBaseIso
  签名: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  定义体: map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ
-/
noncomputable def domainIsoOfBaseIso (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : a' ≅ a where
  hom := map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

/--
Instance `domainUniqueUpToIso_inv_isHomLift` / 实例 `domainUniqueUpToIso_inv_isHomLift`

English:
instance domainUniqueUpToIso_inv_isHomLift
  signature: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  body: domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'

中文:
实例 domainUniqueUpToIso_inv_isHomLift
  签名: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  定义体: domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'

Depends on / 依赖: IsStronglyCartesian, IsStronglyCartesian.map_isHomLift, domainIsoOfBaseIso_hom, map_isHomLift
-/
instance domainUniqueUpToIso_inv_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.hom (domainIsoOfBaseIso p h φ φ').hom :=
  domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'

/--
Instance `domainUniqueUpToIso_hom_isHomLift` / 实例 `domainUniqueUpToIso_hom_isHomLift`

English:
instance domainUniqueUpToIso_hom_isHomLift
  signature: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  body: by
  have : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

中文:
实例 domainUniqueUpToIso_hom_isHomLift
  签名: (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
  定义体: by
  have : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

Depends on / 依赖: IsCartesian, IsCartesian.toIsHomLift, IsHomLift, IsStronglyCartesian, IsStronglyCartesian.map_isHomLift, g.hom, g.inv, h.symm, map_isHomLift, p.IsHomLift, toIsHomLift
-/
instance domainUniqueUpToIso_hom_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.inv (domainIsoOfBaseIso p h φ φ').inv := by
  have : p.IsHomLift ((fun x => g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

end

end IsStronglyCartesian

end CategoryTheory.Functor
