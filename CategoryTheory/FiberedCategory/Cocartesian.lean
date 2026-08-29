/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Co-Cartesian morphisms

This file defines co-Cartesian resp. strongly co-Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted from `Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCocartesian p f φ` expresses that `φ` is a co-Cartesian morphism lying over `f : R ⟶ S` with
respect to `p`. This means that for any morphism `φ' : a ⟶ b'` lying over `f` there
is a unique morphism `τ : b ⟶ b'` lying over `𝟙 S`, such that `φ' = φ ≫ τ`.

`IsStronglyCocartesian p f φ` expresses that `φ` is a strongly co-Cartesian morphism lying over `f`
with respect to `p`.

## Implementation

The constructor of `IsStronglyCocartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCocartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/--
Definition of `IsCocartesian` / `IsCocartesian` 的定义

English:
class IsCocartesian
  parameters: : Prop where
  axioms and operations (2):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property({b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ']) : exists! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'

中文:
类 IsCocartesian
  参数: : 命题 where
  公理与运算 (2 个):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property({b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ']) : 存在! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'
-/
class IsCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ'] :
      exists! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'

attribute [instance] IsCocartesian.toIsHomLift
/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly co-Cartesian if for
all morphisms `φ' : a ⟶ b'` and all diagrams of the form
```
a --φ--> b b'
| | |
v v v
R --f--> S --g--> S'
```
such that `φ'` lifts `f ≫ g`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
/--
Definition of `IsStronglyCocartesian` / `IsStronglyCocartesian` 的定义

English:
class IsStronglyCocartesian
  parameters: : Prop where
  axioms and operations (2):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property'({b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ']) : exists! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'

中文:
类 IsStronglyCocartesian
  参数: : 命题 where
  公理与运算 (2 个):
    - [toIsHomLift : IsHomLift p f φ]
    - universal_property'({b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ']) : 存在! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'
-/
class IsStronglyCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ'] :
      exists! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'
attribute [instance] IsStronglyCocartesian.toIsHomLift

end

namespace IsCocartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCocartesian p f φ]

section

variable {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ']

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def map
  body: Classical.choose IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ'

中文:
定义 noncomputable
  签名: def map
  定义体: Classical.choose IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ'
-/
protected noncomputable def map : b ⟶ b' :=
Classical.choose IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ'

/--
Instance `map_isHomLift` / 实例 `map_isHomLift`

English:
instance map_isHomLift
  signature: : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ')
  body: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]

中文:
实例 map_isHomLift
  签名: : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ')
  定义体: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]

Depends on / 依赖: Classical, Classical.choose_spec, IsCocartesian, IsCocartesian.universal_property, choose_spec, universal_property
-/
instance map_isHomLift : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  statement: φ ≫ IsCocartesian.map p f φ φ' = φ'
  proof: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

中文:
引理 fac
  结论: φ ≫ IsCocartesian.map p f φ φ' = φ'
  证明: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

Depends on / 依赖: Classical, Classical.choose_spec, IsCocartesian, IsCocartesian.universal_property, choose_spec, universal_property
-/
lemma fac : φ ≫ IsCocartesian.map p f φ φ' = φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/--
lemma `map_uniq` / 引理 `map_uniq`

English:
lemma map_uniq
  given: (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ')
  proof: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

中文:
引理 map_uniq
  条件: (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ')
  证明: (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

Depends on / 依赖: Classical, Classical.choose_spec, IsCocartesian, IsCocartesian.universal_property, choose_spec, universal_property
-/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') :
    ψ = IsCocartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
  proof: by
  rw [map_uniq p f φ (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (φ ≫ ψ) ψ' h.symm]

@[simp]

中文:
引理 ext
  结论: (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
  证明: by
  rw [map_uniq p f φ (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (φ ≫ ψ) ψ' h.symm]

@[simp]
-/
protected lemma ext (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
    [IsHomLift p (𝟙 S) ψ] [IsHomLift p (𝟙 S) ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (φ ≫ ψ) ψ' h.symm]

@[simp]
/--
lemma `map_self` / 引理 `map_self`

English:
lemma map_self
  statement: IsCocartesian.map p f φ φ = 𝟙 b
  proof: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

中文:
引理 map_self
  结论: IsCocartesian.map p f φ φ = 𝟙 b
  证明: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

Depends on / 依赖: comp_id, map_uniq, subst_hom_lift
-/
lemma map_self : IsCocartesian.map p f φ φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/--
Definition of `codomainUniqueUpToIso` / `codomainUniqueUpToIso` 的定义

English:
definition codomainUniqueUpToIso
  signature: {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ']
  body: IsCocartesian.map p f φ φ'
  inv := IsCocartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ
    apply IsCocartesian.ext p (p.map φ) φ
    simp only [fac_assoc, fac, comp_id]
  inv_hom_id := by
    subst_hom_lift p f φ'
    apply IsCocartesian.ext p (p.map φ') φ'
    simp only [fac_ass

中文:
定义 codomainUniqueUpToIso
  签名: {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ']
  定义体: IsCocartesian.map p f φ φ'
  inv := IsCocartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ
    apply IsCocartesian.ext p (p.map φ) φ
    simp only [fac_assoc, fac, comp_id]
  inv_hom_id := by
    subst_hom_lift p f φ'
    apply IsCocartesian.ext p (p.map φ') φ'
    simp only [fac_ass

Depends on / 依赖: IsCocartesian, IsCocartesian.map
-/
noncomputable def codomainUniqueUpToIso {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ'] :
    b ≅ b' where
  hom := IsCocartesian.map p f φ φ'
  inv := IsCocartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ
    apply IsCocartesian.ext p (p.map φ) φ
    simp only [fac_assoc, fac, comp_id]
  inv_hom_id := by
    subst_hom_lift p f φ'
    apply IsCocartesian.ext p (p.map φ') φ'
    simp only [fac_assoc, fac, comp_id]

/--
Instance `of_comp_iso` / 实例 `of_comp_iso`

English:
instance of_comp_iso
  signature: {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom]
  body: by
    intro c ψ hψ
    use φ'.inv ≫ IsCocartesian.map p f φ ψ
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_inv_comp]
    apply map_uniq
    exact ((assoc φ _ _) ▸ hτ₂)

中文:
实例 of_comp_iso
  签名: {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom]
  定义体: by
    intro c ψ hψ
    use φ'.inv ≫ IsCocartesian.map p f φ ψ
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_inv_comp]
    apply map_uniq
    exact ((assoc φ _ _) ▸ hτ₂)

Depends on / 依赖: IsCocartesian, IsCocartesian.map, Iso.eq_inv_comp, eq_inv_comp, map_uniq
-/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCocartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use φ'.inv ≫ IsCocartesian.map p f φ ψ
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_inv_comp]
    apply map_uniq
    exact ((assoc φ _ _) ▸ hτ₂)

/--
Instance `of_iso_comp` / 实例 `of_iso_comp`

English:
instance of_iso_comp
  signature: {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom]
  body: by
    intro c ψ hψ
    use IsCocartesian.map p f φ (φ'.inv ≫ ψ)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_inv_comp, ← assoc, hτ₂]

中文:
实例 of_iso_comp
  签名: {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom]
  定义体: by
    intro c ψ hψ
    use IsCocartesian.map p f φ (φ'.inv ≫ ψ)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_inv_comp, ← assoc, hτ₂]

Depends on / 依赖: IsCocartesian, IsCocartesian.map, Iso.eq_inv_comp, eq_inv_comp, map_uniq
-/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCocartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCocartesian.map p f φ (φ'.inv ≫ ψ)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_inv_comp, ← assoc, hτ₂]

end IsCocartesian

namespace IsStronglyCocartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCocartesian p f φ]

/--
lemma `universal_property` / 引理 `universal_property`

English:
lemma universal_property
  statement: {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g)
  proof: by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (f ≫ g) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCocartesian.universal_property' f

中文:
引理 universal_property
  结论: {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g)
  证明: by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (f ≫ g) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCocartesian.universal_property' f

Depends on / 依赖: IsHomLift, IsStronglyCocartesian, IsStronglyCocartesian.universal_property, p.IsHomLift, subst_hom_lift, universal_property
-/
lemma universal_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g)
    (φ' : a ⟶ b') [IsHomLift p f' φ'] : exists! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (f ≫ g) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCocartesian.universal_property' f

/--
Instance `isCocartesian_of_isStronglyCocartesian` / 实例 `isCocartesian_of_isStronglyCocartesian`

English:
instance isCocartesian_of_isStronglyCocartesian
  signature: : p.IsCocartesian f φ where
  body: fun φ' => universal_property p f φ (𝟙 S) f (comp_id f).symm φ'

中文:
实例 isCocartesian_of_isStronglyCocartesian
  签名: : p.IsCocartesian f φ where
  定义体: fun φ' => universal_property p f φ (𝟙 S) f (comp_id f).symm φ'

Depends on / 依赖: comp_id, universal_property
-/
instance isCocartesian_of_isStronglyCocartesian : p.IsCocartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 S) f (comp_id f).symm φ'

section

variable {S' : 𝒮} {b' : 𝒳} {g : S ⟶ S'} {f' : R ⟶ S'} (hf' : f' = f ≫ g) (φ' : a ⟶ b')
  [IsHomLift p f' φ']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : b ⟶ b'
  body: Classical.choose universal_property p f φ _ _ hf' φ'

中文:
定义 map
  签名: : b ⟶ b'
  定义体: Classical.choose universal_property p f φ _ _ hf' φ'

Depends on / 依赖: Classical, Classical.choose, universal_property
-/
noncomputable def map : b ⟶ b' :=
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
  statement: φ ≫ (map p f φ hf' φ') = φ'
  proof: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

中文:
引理 fac
  结论: φ ≫ (map p f φ hf' φ') = φ'
  证明: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, universal_property
-/
lemma fac : φ ≫ (map p f φ hf' φ') = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2


/--
lemma `map_uniq` / 引理 `map_uniq`

English:
lemma map_uniq
  given: (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ')
  statement: ψ = map p f φ hf' φ'
  proof: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

中文:
引理 map_uniq
  条件: (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ')
  结论: ψ = map p f φ hf' φ'
  证明: (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, universal_property
-/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
  proof: by
  rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ' h.symm]

@[simp]

中文:
引理 ext
  结论: (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
  证明: by
  rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ' h.symm]

@[simp]
-/
protected lemma ext (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
    {ψ ψ' : b ⟶ b'} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ rfl]; rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ' h.symm]

@[simp]
/--
lemma `map_self` / 引理 `map_self`

English:
lemma map_self
  statement: map p f φ (comp_id f).symm φ = 𝟙 b
  proof: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

中文:
引理 map_self
  结论: map p f φ (comp_id f).symm φ = 𝟙 b
  证明: by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

Depends on / 依赖: comp_id, map_uniq, subst_hom_lift
-/
lemma map_self : map p f φ (comp_id f).symm φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/-- When its possible to compare the two, the composition of two `IsStronglyCocartesian.map` will
also be given by a `IsStronglyCocartesian.map`. In other words, given diagrams
```
a --φ--> b b' b''
| | | |
v v v v
R --f--> S --g--> S' --g'--> S'
```
and
```
a --φ'--> b'
| |
v v
R --f'--> S'

```
and
```
a --φ''--> b''
| |
v v
R --f''--> S''
```
such that `φ` and `φ'` are strongly co-Cartesian morphisms, and such that `f' = f ≫ g` and
`f'' = f' ≫ g'`. Then composing the induced map from `b ⟶ b'` with the induced map from
`b' ⟶ b''` gives the induced map from `b ⟶ b''`. -/
@[reassoc (attr := simp)]
/--
lemma `map_comp_map` / 引理 `map_comp_map`

English:
lemma map_comp_map
  statement: {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : S ⟶ S'}
  proof: by
  apply map_uniq p f φ
  simp only [fac_assoc, fac]

中文:
引理 map_comp_map
  结论: {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : S ⟶ S'}
  证明: by
  apply map_uniq p f φ
  simp only [fac_assoc, fac]

Depends on / 依赖: fac_assoc, map_uniq
-/
lemma map_comp_map {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : S ⟶ S'}
    {g' : S' ⟶ S''} (H : f' = f ≫ g) (H' : f'' = f' ≫ g') (φ' : a ⟶ b') (φ'' : a ⟶ b'')
    [IsStronglyCocartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f φ H φ' ≫ map p f' φ' H' φ'' =
      map p f φ (show f'' = f ≫ (g ≫ g') by rwa [← assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [fac_assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ]
  body: by
    intro c' h τ hτ
use map p g ψ (f' := g ≫ h) rfl map p f φ (assoc f g h) τ
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simp only [assoc, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [← hπ'₂, assoc]

中文:
实例 comp
  签名: [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ]
  定义体: by
    intro c' h τ hτ
use map p g ψ (f' := g ≫ h) rfl map p f φ (assoc f g h) τ
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simp only [assoc, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [← hπ'₂, assoc]

Depends on / 依赖: map_uniq
-/
instance comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ] :
    IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro c' h τ hτ
use map p g ψ (f' := g ≫ h) rfl map p f φ (assoc f g h) τ
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simp only [assoc, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [← hπ'₂, assoc]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ)]
  proof: by
    intro c' h τ hτ
    /- We get a morphism `π : c ⟶ c'` such that `(φ ≫ ψ) ≫ π = φ ≫ τ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := f ≫ g ≫ h) (assoc f g h).symm (φ ≫ τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /-

中文:
引理 of_comp
  结论: [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ)]
  证明: by
    intro c' h τ hτ
    /- We get a morphism `π : c ⟶ c'` such that `(φ ≫ ψ) ≫ π = φ ≫ τ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := f ≫ g ≫ h) (assoc f g h).symm (φ ≫ τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /-
-/
protected lemma of_comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p g ψ] : IsStronglyCocartesian p g ψ where
  universal_property' := by
    intro c' h τ hτ
    /- We get a morphism `π : c ⟶ c'` such that `(φ ≫ ψ) ≫ π = φ ≫ τ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := f ≫ g ≫ h) (assoc f g h).symm (φ ≫ τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `ψ ≫ π = τ` follows from `φ ≫ ψ ≫ π = φ ≫ τ` and the universal property of
    `φ`. -/
· apply IsStronglyCocartesian.ext p f φ (g ≫ h) by simp only [← assoc, fac]
    -- Finally, uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
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
    intro b' g τ hτ
    use φ.inv ≫ τ
    refine ⟨?_, by cat_disch⟩
    simpa [← assoc] using (IsHomLift.comp p (isoOfIsoLift p f φ).inv (f ≫ g) φ.inv τ)

中文:
实例 of_iso
  签名: (φ : a ≅ b) [IsHomLift p f φ.hom]
  定义体: by
    intro b' g τ hτ
    use φ.inv ≫ τ
    refine ⟨?_, by cat_disch⟩
    simpa [← assoc] using (IsHomLift.comp p (isoOfIsoLift p f φ).inv (f ≫ g) φ.inv τ)

Depends on / 依赖: IsHomLift, IsHomLift.comp, cat_disch, isoOfIsoLift
-/
instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCocartesian p f φ.hom where
  universal_property' := by
    intro b' g τ hτ
    use φ.inv ≫ τ
    refine ⟨?_, by cat_disch⟩
    simpa [← assoc] using (IsHomLift.comp p (isoOfIsoLift p f φ).inv (f ≫ g) φ.inv τ)

/--
Instance `of_isIso` / 实例 `of_isIso`

English:
instance of_isIso
  signature: (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ]
  body: @IsStronglyCocartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

中文:
实例 of_isIso
  签名: (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ]
  定义体: @IsStronglyCocartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

Depends on / 依赖: IsStronglyCocartesian, IsStronglyCocartesian.of_iso, of_iso
-/
instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCocartesian p f φ :=
  @IsStronglyCocartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/--
lemma `isIso_of_base_isIso` / 引理 `isIso_of_base_isIso`

English:
lemma isIso_of_base_isIso
  given: (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f]
  statement: IsIso φ
  proof: by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ'` be the morphism induced by applying universal property to `𝟙 a` lying over `f ≫ f⁻¹`.
  let φ' := map p (p.map φ) φ (IsIso.hom_inv_id (p.map φ)).symm (𝟙 a)
  use φ'
  -- `φ ≫ φ' = 𝟙 a` follows immediately from the universal property.
  have inv_

中文:
引理 isIso_of_base_isIso
  条件: (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f]
  结论: IsIso φ
  证明: by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ'` be the morphism induced by applying universal property to `𝟙 a` lying over `f ≫ f⁻¹`.
  let φ' := map p (p.map φ) φ (IsIso.hom_inv_id (p.map φ)).symm (𝟙 a)
  use φ'
  -- `φ ≫ φ' = 𝟙 a` follows immediately from the universal property.
  have inv_

Depends on / 依赖: subst_hom_lift
-/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ'` be the morphism induced by applying universal property to `𝟙 a` lying over `f ≫ f⁻¹`.
  let φ' := map p (p.map φ) φ (IsIso.hom_inv_id (p.map φ)).symm (𝟙 a)
  use φ'
  -- `φ ≫ φ' = 𝟙 a` follows immediately from the universal property.
  have inv_hom : φ ≫ φ' = 𝟙 a := fac p (p.map φ) φ _ (𝟙 a)
  refine ⟨inv_hom, ?_⟩
  -- We will now show that `φ' ≫ φ = 𝟙 b` by showing that `φ ≫ (φ' ≫ φ) = φ ≫ 𝟙 b`.
  have h₁ : IsHomLift p (𝟙 (p.obj b)) (φ' ≫ φ) := by
    rw [← IsIso.inv_hom_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCocartesian.ext p (p.map φ) φ (𝟙 (p.obj b))
  simp only [← assoc, inv_hom, comp_id, id_comp]

end

/--
Definition of `codomainIsoOfBaseIso` / `codomainIsoOfBaseIso` 的定义

English:
definition codomainIsoOfBaseIso
  signature: {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'}
  body: map p f φ h φ'
  inv := @map _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (· ≫ g.inv) h.symm) φ
    (by simp only [assoc, Iso.hom_inv_id, comp_id]; infer_instance)

中文:
定义 codomainIsoOfBaseIso
  签名: {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'}
  定义体: map p f φ h φ'
  inv := @map _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (· ≫ g.inv) h.symm) φ
    (by simp only [assoc, Iso.hom_inv_id, comp_id]; infer_instance)
-/
noncomputable def codomainIsoOfBaseIso {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'}
    {g : S ≅ S'} (h : f' = f ≫ g.hom) (φ : a ⟶ b) (φ' : a ⟶ b') [IsStronglyCocartesian p f φ]
    [IsStronglyCocartesian p f' φ'] : b ≅ b' where
  hom := map p f φ h φ'
  inv := @map _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (· ≫ g.inv) h.symm) φ
    (by simp only [assoc, Iso.hom_inv_id, comp_id]; infer_instance)

end IsStronglyCocartesian

end CategoryTheory.Functor
