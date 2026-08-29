/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Bousfield localization

Given a predicate `P : ObjectProperty C` on the objects of a category `C`,
we define `W.isLocal : MorphismProperty C` as the class of morphisms `f : X ⟶ Y`
such that for any `Z : C` such that `P Z`, the precomposition with `f`
induces a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of the left Bousfield localization
in the context of model categories.)

When `G ⊣ F` is an adjunction with `F : C ⥤ D` fully faithful, then
`G : D ⥤ C` is a localization functor for the class `isLocal (· ∈ Set.range F.obj)`,
which then identifies to the inverse image by `G` of the class of
isomorphisms in `C`.

The dual results are also obtained.

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

/-! ### Left Bousfield localization -/

section

variable (P : ObjectProperty C)

/--
Definition of `isLocal` / `isLocal` 的定义

English:
definition isLocal
  signature: : MorphismProperty C
  body: fun _ _ f =>
  forall Z, P Z -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

中文:
定义 isLocal
  签名: : Morphism命题erty C
  定义体: fun _ _ f =>
  forall Z, P Z -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)
-/
def isLocal : MorphismProperty C := fun _ _ f =>
  forall Z, P Z -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

variable {P} in
/-- The bijection `(Y ⟶ Z) ≃ (X ⟶ Z)` induced by `f : X ⟶ Y` when `P.isLocal f`
and `P Z`. -/
@[simps! apply]
/--
Definition of `isLocal.homEquiv` / `isLocal.homEquiv` 的定义

English:
definition isLocal.homEquiv
  signature: {X Y : C} {f : X ⟶ Y} (hf : P.isLocal f) (Z : C) (hZ : P Z)
  body: Equiv.ofBijective _ (hf Z hZ)

中文:
定义 isLocal.homEquiv
  签名: {X Y : C} {f : X ⟶ Y} (hf : P.isLocal f) (Z : C) (hZ : P Z)
  定义体: Equiv.ofBijective _ (hf Z hZ)

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def isLocal.homEquiv {X Y : C} {f : X ⟶ Y} (hf : P.isLocal f) (Z : C) (hZ : P Z) :
    (Y ⟶ Z) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hf Z hZ)

/--
lemma `isoClosure_isLocal` / 引理 `isoClosure_isLocal`

English:
lemma isoClosure_isLocal
  statement: P.isoClosure.isLocal = P.isLocal
  proof: by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (P.le_isoClosure _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.h

中文:
引理 isoClosure_isLocal
  结论: P.isoClosure.isLocal = P.isLocal
  证明: by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (P.le_isoClosure _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.h

Depends on / 依赖: P.le_isoClosure, cancel_mono, comp_id, e.hom, e.hom_inv_id, e.inv, hom_inv_id, le_isoClosure, reassoc_of
-/
lemma isoClosure_isLocal : P.isoClosure.isLocal = P.isLocal := by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (P.le_isoClosure _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.hom)
      exact ⟨a ≫ e.inv, by simp only [reassoc_of% h, e.hom_inv_id, comp_id]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isLocal.IsMultiplicative
  body: by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using! Function.Bijective.comp (hf Z hZ) (hg Z hZ)

中文:
实例 :
  签名: P.isLocal.IsMultiplicative
  定义体: by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using! Function.Bijective.comp (hf Z hZ) (hg Z hZ)

Depends on / 依赖: Bijective, Function, Function.Bijective.comp, Function.bijective_id, bijective_id, comp_mem, id_comp
-/
instance : P.isLocal.IsMultiplicative where
  id_mem X Z _ := by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using! Function.Bijective.comp (hf Z hZ) (hg Z hZ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isLocal.HasTwoOutOfThreeProperty
  body: by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using! hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using! hfg Z hZ

中文:
实例 :
  签名: P.isLocal.HasTwoOutOfThree命题erty
  定义体: by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using! hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using! hfg Z hZ

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, of_comp_iff, of_precomp
-/
instance : P.isLocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using! hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using! hfg Z hZ

/--
lemma `isLocal_of_isIso` / 引理 `isLocal_of_isIso`

English:
lemma isLocal_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: P.isLocal f
  proof: fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

中文:
引理 isLocal_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f]
  结论: P.isLocal f
  证明: fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

Depends on / 依赖: cancel_epi
-/
lemma isLocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isLocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩

/--
lemma `isLocal_iff_isIso` / 引理 `isLocal_iff_isIso`

English:
lemma isLocal_iff_isIso
  given: {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y)
  proof: by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply isLocal_of_isIso

中文:
引理 isLocal_iff_isIso
  条件: {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y)
  证明: by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply isLocal_of_isIso

Depends on / 依赖: comp_id, isLocal_of_isIso, reassoc_of
-/
lemma isLocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isLocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply isLocal_of_isIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isLocal.RespectsIso
  body: P.isLocal.comp_mem f g (isLocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isLocal.comp_mem g f hg (isLocal_of_isIso _ f)

中文:
实例 :
  签名: P.isLocal.RespectsIso
  定义体: P.isLocal.comp_mem f g (isLocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isLocal.comp_mem g f hg (isLocal_of_isIso _ f)

Depends on / 依赖: P.isLocal.comp_mem, comp_mem, isLocal, isLocal_of_isIso
-/
instance : P.isLocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isLocal.comp_mem f g (isLocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isLocal.comp_mem g f hg (isLocal_of_isIso _ f)

/--
lemma `le_isLocal_iff` / 引理 `le_isLocal_iff`

English:
lemma le_isLocal_iff
  given: (P : ObjectProperty C) (W : MorphismProperty C)
  proof: ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩

中文:
引理 le_isLocal_iff
  条件: (P : Object命题erty C) (W : Morphism命题erty C)
  证明: ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩

Depends on / 依赖: Cardinal, Cardinal.mk_le_of_surjective, Function, Function.Surjective, Order.cof_le, Ordinal, Ordinal.cof_toType, Set.mem_range_self, Set.range, Surjective, cof_le, cof_ord, cof_toType, contrapose, hk.le, isCardinalFiltered_preorder, mem_range_self, mk_le_of_surjective, out.cof_ord
-/
lemma le_isLocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W <= P.isLocal ↔ P <= W.isLocal :=
  ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩

/--
lemma `galoisConnection_isLocal` / 引理 `galoisConnection_isLocal`

English:
lemma galoisConnection_isLocal
  proof: le_isLocal_iff

中文:
引理 galoisConnection_isLocal
  证明: le_isLocal_iff
-/
lemma galoisConnection_isLocal :
    GaloisConnection (OrderDual.toDual ∘ isLocal (C := C))
      (MorphismProperty.isLocal ∘ OrderDual.ofDual) :=
  le_isLocal_iff

end

/-! ### Right Bousfield localization -/

section

variable (P : ObjectProperty C)

/--
Definition of `isColocal` / `isColocal` 的定义

English:
definition isColocal
  signature: : MorphismProperty C
  body: fun _ _ g =>
  forall X, P X -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

中文:
定义 isColocal
  签名: : Morphism命题erty C
  定义体: fun _ _ g =>
  forall X, P X -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)
-/
def isColocal : MorphismProperty C := fun _ _ g =>
  forall X, P X -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

variable {P} in
/-- The bijection `(X ⟶ Y) ≃ (X ⟶ Z)` induced by `g : Y ⟶ Z` when `P.isColocal g`
and `P X`. -/
@[simps! apply]
/--
Definition of `isColocal.homEquiv` / `isColocal.homEquiv` 的定义

English:
definition isColocal.homEquiv
  signature: {Y Z : C} {g : Y ⟶ Z} (hg : P.isColocal g) (X : C) (hX : P X)
  body: Equiv.ofBijective _ (hg X hX)

中文:
定义 isColocal.homEquiv
  签名: {Y Z : C} {g : Y ⟶ Z} (hg : P.isColocal g) (X : C) (hX : P X)
  定义体: Equiv.ofBijective _ (hg X hX)

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def isColocal.homEquiv {Y Z : C} {g : Y ⟶ Z} (hg : P.isColocal g) (X : C) (hX : P X) :
    (X ⟶ Y) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hg X hX)

/--
lemma `isoClosure_isColocal` / 引理 `isoClosure_isColocal`

English:
lemma isoClosure_isColocal
  statement: P.isoClosure.isColocal = P.isColocal
  proof: by
  ext Y Z g
  constructor
  · intro hg X hX
    exact hg _ (P.le_isoClosure _ hX)
  · rintro hg X ⟨X', hX', ⟨e⟩⟩
    constructor
    · intro f₁ f₂ eq
      rw [← cancel_epi e.inv]
      apply (hg _ hX').1
      simp [eq]
    · intro f
      obtain ⟨a, h⟩ := (hg _ hX').2 (e.inv ≫ f)
      exact ⟨e

中文:
引理 isoClosure_isColocal
  结论: P.isoClosure.isColocal = P.isColocal
  证明: by
  ext Y Z g
  constructor
  · intro hg X hX
    exact hg _ (P.le_isoClosure _ hX)
  · rintro hg X ⟨X', hX', ⟨e⟩⟩
    constructor
    · intro f₁ f₂ eq
      rw [← cancel_epi e.inv]
      apply (hg _ hX').1
      simp [eq]
    · intro f
      obtain ⟨a, h⟩ := (hg _ hX').2 (e.inv ≫ f)
      exact ⟨e

Depends on / 依赖: P.le_isoClosure, cancel_epi, e.hom, e.inv, le_isoClosure
-/
lemma isoClosure_isColocal : P.isoClosure.isColocal = P.isColocal := by
  ext Y Z g
  constructor
  · intro hg X hX
    exact hg _ (P.le_isoClosure _ hX)
  · rintro hg X ⟨X', hX', ⟨e⟩⟩
    constructor
    · intro f₁ f₂ eq
      rw [← cancel_epi e.inv]
      apply (hg _ hX').1
      simp [eq]
    · intro f
      obtain ⟨a, h⟩ := (hg _ hX').2 (e.inv ≫ f)
      exact ⟨e.hom ≫ a, by simp [h]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isColocal.IsMultiplicative
  body: by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg X hX := by
    convert! Function.Bijective.comp (hg X hX) (hf X hX)
    cat_disch

中文:
实例 :
  签名: P.isColocal.IsMultiplicative
  定义体: by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg X hX := by
    convert! Function.Bijective.comp (hg X hX) (hf X hX)
    cat_disch

Depends on / 依赖: Bijective, Function, Function.Bijective.comp, Function.bijective_id, bijective_id, cat_disch, comp_mem, convert, id_comp
-/
instance : P.isColocal.IsMultiplicative where
  id_mem _ _ _ := by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg X hX := by
    convert! Function.Bijective.comp (hg X hX) (hf X hX)
    cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isColocal.HasTwoOutOfThreeProperty
  body: by
    rw [← Function.Bijective.of_comp_iff' (hg X hX)]
    convert! hfg X hX
    cat_disch
  of_precomp f g hf hfg X hX := by
    rw [← Function.Bijective.of_comp_iff _ (hf X hX)]
    convert! hfg X hX
    cat_disch

中文:
实例 :
  签名: P.isColocal.HasTwoOutOfThree命题erty
  定义体: by
    rw [← Function.Bijective.of_comp_iff' (hg X hX)]
    convert! hfg X hX
    cat_disch
  of_precomp f g hf hfg X hX := by
    rw [← Function.Bijective.of_comp_iff _ (hf X hX)]
    convert! hfg X hX
    cat_disch

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, cat_disch, convert, of_comp_iff, of_precomp
-/
instance : P.isColocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg X hX := by
    rw [← Function.Bijective.of_comp_iff' (hg X hX)]
    convert! hfg X hX
    cat_disch
  of_precomp f g hf hfg X hX := by
    rw [← Function.Bijective.of_comp_iff _ (hf X hX)]
    convert! hfg X hX
    cat_disch

/--
lemma `isColocal_of_isIso` / 引理 `isColocal_of_isIso`

English:
lemma isColocal_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: P.isColocal f
  proof: fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_mono f]
  · intro g
    exact ⟨g ≫ inv f, by simp⟩

中文:
引理 isColocal_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [IsIso f]
  结论: P.isColocal f
  证明: fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_mono f]
  · intro g
    exact ⟨g ≫ inv f, by simp⟩

Depends on / 依赖: cancel_mono
-/
lemma isColocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isColocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_mono f]
  · intro g
    exact ⟨g ≫ inv f, by simp⟩

/--
lemma `isColocal_iff_isIso` / 引理 `isColocal_iff_isIso`

English:
lemma isColocal_iff_isIso
  given: {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y)
  proof: by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hY).2 (𝟙 Y)
    exact ⟨g, (hf _ hX).1 (by cat_disch), hg⟩
  · apply isColocal_of_isIso

中文:
引理 isColocal_iff_isIso
  条件: {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y)
  证明: by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hY).2 (𝟙 Y)
    exact ⟨g, (hf _ hX).1 (by cat_disch), hg⟩
  · apply isColocal_of_isIso

Depends on / 依赖: cat_disch, isColocal_of_isIso
-/
lemma isColocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isColocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hY).2 (𝟙 Y)
    exact ⟨g, (hf _ hX).1 (by cat_disch), hg⟩
  · apply isColocal_of_isIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isColocal.RespectsIso
  body: P.isColocal.comp_mem f g (isColocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isColocal.comp_mem g f hg (isColocal_of_isIso _ f)

中文:
实例 :
  签名: P.isColocal.RespectsIso
  定义体: P.isColocal.comp_mem f g (isColocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isColocal.comp_mem g f hg (isColocal_of_isIso _ f)

Depends on / 依赖: P.isColocal.comp_mem, comp_mem, isColocal, isColocal_of_isIso
-/
instance : P.isColocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isColocal.comp_mem f g (isColocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isColocal.comp_mem g f hg (isColocal_of_isIso _ f)

/--
lemma `le_isColocal_iff` / 引理 `le_isColocal_iff`

English:
lemma le_isColocal_iff
  given: (P : ObjectProperty C) (W : MorphismProperty C)
  proof: ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩

中文:
引理 le_isColocal_iff
  条件: (P : Object命题erty C) (W : Morphism命题erty C)
  证明: ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩
-/
lemma le_isColocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W <= P.isColocal ↔ P <= W.isColocal :=
  ⟨fun h _ hZ _ _ _ hf => h _ hf _ hZ,
    fun h _ _ _ hf _ hZ => h _ hZ _ hf⟩

/--
lemma `galoisConnection_isColocal` / 引理 `galoisConnection_isColocal`

English:
lemma galoisConnection_isColocal
  proof: le_isColocal_iff

中文:
引理 galoisConnection_isColocal
  证明: le_isColocal_iff
-/
lemma galoisConnection_isColocal :
    GaloisConnection (OrderDual.toDual ∘ isColocal (C := C))
      (MorphismProperty.isColocal ∘ OrderDual.ofDual) :=
  le_isColocal_iff

end

/-! ### Bousfield localization and adjunctions -/

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]
include adj

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isLocal_adj_unit_app` / 引理 `isLocal_adj_unit_app`

English:
lemma isLocal_adj_unit_app
  given: (X : D)
  statement: isLocal (· in Set.range F.obj) (adj.unit.app X)
  proof: by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
        (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop

中文:
引理 isLocal_adj_unit_app
  条件: (X : D)
  结论: isLocal (· in Set.range F.obj) (adj.unit.app X)
  证明: by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
        (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop

Depends on / 依赖: Adjunction, Adjunction.homEquiv, FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, adj.homEquiv, bijective, convert, homEquiv, homEquiv.symm.trans, ofFullyFaithful
-/
lemma isLocal_adj_unit_app (X : D) : isLocal (· in Set.range F.obj) (adj.unit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
        (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop

/--
lemma `isLocal_iff_isIso_map` / 引理 `isLocal_iff_isIso_map`

English:
lemma isLocal_iff_isIso_map
  given: {X Y : D} (f : X ⟶ Y)
  proof: by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· in Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [this]; rw [(isLocal (· in Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]; rw [isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨f

中文:
引理 isLocal_iff_isIso_map
  条件: {X Y : D} (f : X ⟶ Y)
  证明: by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· in Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [this]; rw [(isLocal (· in Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]; rw [isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨f

Depends on / 依赖: F.obj, G.map, Set.range, adj.unit.naturality, isIso_of_fully_faithful, isLocal, isLocal_adj_unit_app, isLocal_iff_isIso, naturality, postcomp_iff, precomp_iff
-/
lemma isLocal_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    isLocal (· in Set.range F.obj) f ↔ IsIso (G.map f) := by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· in Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y)]; rw [this]; rw [(isLocal (· in Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X)]; rw [isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨fun _ => isIso_of_fully_faithful F (G.map f), fun _ => inferInstance⟩

/--
lemma `isLocal_eq_inverseImage_isomorphisms` / 引理 `isLocal_eq_inverseImage_isomorphisms`

English:
lemma isLocal_eq_inverseImage_isomorphisms
  proof: by
  ext P₁ P₂ f
  rw [isLocal_iff_isIso_map adj]
  rfl

中文:
引理 isLocal_eq_inverseImage_isomorphisms
  证明: by
  ext P₁ P₂ f
  rw [isLocal_iff_isIso_map adj]
  rfl

Depends on / 依赖: isLocal_iff_isIso_map
-/
lemma isLocal_eq_inverseImage_isomorphisms :
    isLocal (· in Set.range F.obj) = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [isLocal_iff_isIso_map adj]
  rfl

/--
lemma `isLocalization_isLocal` / 引理 `isLocalization_isLocal`

English:
lemma isLocalization_isLocal
  statement: G.IsLocalization (isLocal (· in Set.range F.obj))
  proof: by
  rw [isLocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

中文:
引理 isLocalization_isLocal
  结论: G.IsLocalization (isLocal (· in Set.range F.obj))
  证明: by
  rw [isLocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

Depends on / 依赖: adj.isLocalization, isLocal_eq_inverseImage_isomorphisms, isLocalization
-/
lemma isLocalization_isLocal : G.IsLocalization (isLocal (· in Set.range F.obj)) := by
  rw [isLocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

end

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [G.Full] [G.Faithful]
include adj

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isColocal_adj_counit_app` / 引理 `isColocal_adj_counit_app`

English:
lemma isColocal_adj_counit_app
  given: (X : C)
  statement: isColocal (· in Set.range G.obj) (adj.counit.app X)
  proof: by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
        (adj.homEquiv Y X).symm).bijective using 1
  dsimp [Adjunction.homEquiv]
  cat_disch

中文:
引理 isColocal_adj_counit_app
  条件: (X : C)
  结论: isColocal (· in Set.range G.obj) (adj.counit.app X)
  证明: by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
        (adj.homEquiv Y X).symm).bijective using 1
  dsimp [Adjunction.homEquiv]
  cat_disch

Depends on / 依赖: Adjunction, Adjunction.homEquiv, FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, adj.homEquiv, bijective, cat_disch, convert, homEquiv, homEquiv.symm.trans, ofFullyFaithful
-/
lemma isColocal_adj_counit_app (X : C) : isColocal (· in Set.range G.obj) (adj.counit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
        (adj.homEquiv Y X).symm).bijective using 1
  dsimp [Adjunction.homEquiv]
  cat_disch

/--
lemma `isColocal_iff_isIso_map` / 引理 `isColocal_iff_isIso_map`

English:
lemma isColocal_iff_isIso_map
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  have := adj.counit.naturality f
  dsimp at this
  rw [← (isColocal _).precomp_iff _ _ (isColocal_adj_counit_app adj X)]; rw [← this]; rw [(isColocal _).postcomp_iff _ _ (isColocal_adj_counit_app adj Y)]; rw [isColocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨fun _ => isIso_of_fully_f

中文:
引理 isColocal_iff_isIso_map
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  have := adj.counit.naturality f
  dsimp at this
  rw [← (isColocal _).precomp_iff _ _ (isColocal_adj_counit_app adj X)]; rw [← this]; rw [(isColocal _).postcomp_iff _ _ (isColocal_adj_counit_app adj Y)]; rw [isColocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨fun _ => isIso_of_fully_f

Depends on / 依赖: F.map, adj.counit.naturality, counit, isColocal, isColocal_adj_counit_app, isColocal_iff_isIso, isIso_of_fully_faithful, naturality, postcomp_iff, precomp_iff
-/
lemma isColocal_iff_isIso_map {X Y : C} (f : X ⟶ Y) :
    isColocal (· in Set.range G.obj) f ↔ IsIso (F.map f) := by
  have := adj.counit.naturality f
  dsimp at this
  rw [← (isColocal _).precomp_iff _ _ (isColocal_adj_counit_app adj X)]; rw [← this]; rw [(isColocal _).postcomp_iff _ _ (isColocal_adj_counit_app adj Y)]; rw [isColocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]
  exact ⟨fun _ => isIso_of_fully_faithful G (F.map f), fun _ => inferInstance⟩

/--
lemma `isColocal_eq_inverseImage_isomorphisms` / 引理 `isColocal_eq_inverseImage_isomorphisms`

English:
lemma isColocal_eq_inverseImage_isomorphisms
  proof: by
  ext P₁ P₂ f
  rw [isColocal_iff_isIso_map adj]
  rfl

中文:
引理 isColocal_eq_inverseImage_isomorphisms
  证明: by
  ext P₁ P₂ f
  rw [isColocal_iff_isIso_map adj]
  rfl

Depends on / 依赖: isColocal_iff_isIso_map
-/
lemma isColocal_eq_inverseImage_isomorphisms :
    isColocal (· in Set.range G.obj) = (MorphismProperty.isomorphisms _).inverseImage F := by
  ext P₁ P₂ f
  rw [isColocal_iff_isIso_map adj]
  rfl

/--
lemma `isLocalization_isColocal` / 引理 `isLocalization_isColocal`

English:
lemma isLocalization_isColocal
  statement: F.IsLocalization (isColocal (· in Set.range G.obj))
  proof: by
  rw [isColocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization'

中文:
引理 isLocalization_isColocal
  结论: F.IsLocalization (isColocal (· in Set.range G.obj))
  证明: by
  rw [isColocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization'

Depends on / 依赖: adj.isLocalization, isColocal_eq_inverseImage_isomorphisms, isLocalization
-/
lemma isLocalization_isColocal : F.IsLocalization (isColocal (· in Set.range G.obj)) := by
  rw [isColocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization'

end

end ObjectProperty

open Localization

/--
lemma `ObjectProperty.le_isLocal_isLocal` / 引理 `ObjectProperty.le_isLocal_isLocal`

English:
lemma ObjectProperty.le_isLocal_isLocal
  given: (P : ObjectProperty C)
  proof: by
  rw [← le_isLocal_iff]

中文:
引理 ObjectProperty.le_isLocal_isLocal
  条件: (P : Object命题erty C)
  证明: by
  rw [← le_isLocal_iff]

Depends on / 依赖: le_isLocal_iff
-/
lemma ObjectProperty.le_isLocal_isLocal (P : ObjectProperty C) :
    P <= P.isLocal.isLocal := by
  rw [← le_isLocal_iff]

/--
lemma `MorphismProperty.le_isLocal_isLocal` / 引理 `MorphismProperty.le_isLocal_isLocal`

English:
lemma MorphismProperty.le_isLocal_isLocal
  given: (W : MorphismProperty C)
  proof: by
  rw [ObjectProperty.le_isLocal_iff]

中文:
引理 MorphismProperty.le_isLocal_isLocal
  条件: (W : Morphism命题erty C)
  证明: by
  rw [ObjectProperty.le_isLocal_iff]

Depends on / 依赖: ObjectProperty, ObjectProperty.le_isLocal_iff, le_isLocal_iff
-/
lemma MorphismProperty.le_isLocal_isLocal (W : MorphismProperty C) :
    W <= W.isLocal.isLocal := by
  rw [ObjectProperty.le_isLocal_iff]

/--
lemma `ObjectProperty.le_isColocal_isColocal` / 引理 `ObjectProperty.le_isColocal_isColocal`

English:
lemma ObjectProperty.le_isColocal_isColocal
  given: (P : ObjectProperty C)
  proof: by
  rw [← le_isColocal_iff]

中文:
引理 ObjectProperty.le_isColocal_isColocal
  条件: (P : Object命题erty C)
  证明: by
  rw [← le_isColocal_iff]

Depends on / 依赖: le_isColocal_iff
-/
lemma ObjectProperty.le_isColocal_isColocal (P : ObjectProperty C) :
    P <= P.isColocal.isColocal := by
  rw [← le_isColocal_iff]

/--
lemma `MorphismProperty.le_isColocal_isColocal` / 引理 `MorphismProperty.le_isColocal_isColocal`

English:
lemma MorphismProperty.le_isColocal_isColocal
  given: (W : MorphismProperty C)
  proof: by
  rw [ObjectProperty.le_isColocal_iff]

中文:
引理 MorphismProperty.le_isColocal_isColocal
  条件: (W : Morphism命题erty C)
  证明: by
  rw [ObjectProperty.le_isColocal_iff]

Depends on / 依赖: ObjectProperty, ObjectProperty.le_isColocal_iff, le_isColocal_iff
-/
lemma MorphismProperty.le_isColocal_isColocal (W : MorphismProperty C) :
    W <= W.isColocal.isColocal := by
  rw [ObjectProperty.le_isColocal_iff]

end CategoryTheory
