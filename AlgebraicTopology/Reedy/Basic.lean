/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nima Rasekh, Aras Ergus
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Order.SuccPred.Basic

/-!
# Reedy categories

In this file, we introduce the definition of a Reedy structure
on a category `C` equipped with two classes of morphisms
`W₁` and `W₂` (these are sometimes denoted `C₋` and `C₊` in
the literature).

## TODO
* Construct the Reedy model category structure on the category of
functors `C ⥤ D` when `C` is a Reedy category and `D` a model category
https://github.com/leanprover-community/project-intentions/issues/5

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]

-/

@[expose] public section

open CategoryTheory

namespace HomotopicalAlgebra

open MorphismProperty in
/--
Definition of `ReedyStructure` / `ReedyStructure` 的定义

English:
structure ReedyStructure
  parameters: {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
  axioms and operations (4):
    - deg : C -> α
    - lt₁({X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f)) : deg Y < deg X
    - lt₂({X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f)) : deg X < deg Y
    - nonempty_unique({X Y : C} (f : X ⟶ Y)) : Nonempty (Unique (W₁.MapFactorizationData W₂ f))

中文:
结构 ReedyStructure
  参数: {C : 类型} [范畴* C] (W₁ W₂ : MorphismProperty C)
  公理与运算 (4 个):
    - deg : C -> α
    - lt₁({X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f)) : deg Y < deg X
    - lt₂({X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f)) : deg X < deg Y
    - nonempty_unique({X Y : C} (f : X ⟶ Y)) : 非空 (唯一 (W₁.MapFactorizationData W₂ f))
-/
structure ReedyStructure {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative]
    (α : Type*) [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α] where
  /-- the degree of an object -/
  deg : C -> α
  lt₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f) : deg Y < deg X
  lt₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f) : deg X < deg Y
  nonempty_unique {X Y : C} (f : X ⟶ Y) :
    Nonempty (Unique (W₁.MapFactorizationData W₂ f))

namespace ReedyStructure

variable {C : Type*} [Category* C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

/-- The opposite of a Reedy structure. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : ReedyStructure W₂.op W₁.op α where
  body: r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)

中文:
定义 op
  签名: : ReedyStructure W₂.op W₁.op α where
  定义体: r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)
-/
protected def op : ReedyStructure W₂.op W₁.op α where
  deg := r.deg ∘ Opposite.unop
  lt₁ f hf hf' := r.lt₂ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  lt₂ f hf hf' := r.lt₁ f.unop hf (by
    simpa [MorphismProperty.identities_op_iff] using hf')
  nonempty_unique f :=
    MorphismProperty.MapFactorizationData.opEquiv.uniqueCongr.nonempty_congr.1
      (r.nonempty_unique f.unop)

/--
lemma `le₁` / 引理 `le₁`

English:
lemma le₁
  given: {X Y : C} (f : X ⟶ Y) (hf : W₁ f)
  statement: r.deg Y <= r.deg X
  proof: by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le

中文:
引理 le₁
  条件: {X Y : C} (f : X ⟶ Y) (hf : W₁ f)
  结论: r.deg Y <= r.deg X
  证明: by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le

Depends on / 依赖: MorphismProperty, MorphismProperty.identities, identities, r.lt
-/
lemma le₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) : r.deg Y <= r.deg X := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₁ f hf hf').le

/--
lemma `le₂` / 引理 `le₂`

English:
lemma le₂
  given: {X Y : C} (f : X ⟶ Y) (hf : W₂ f)
  statement: r.deg X <= r.deg Y
  proof: by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le

中文:
引理 le₂
  条件: {X Y : C} (f : X ⟶ Y) (hf : W₂ f)
  结论: r.deg X <= r.deg Y
  证明: by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le

Depends on / 依赖: MorphismProperty, MorphismProperty.identities, identities, r.lt
-/
lemma le₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) : r.deg X <= r.deg Y := by
  by_cases hf' : MorphismProperty.identities C f
  · cases hf'
    rfl
  · exact (r.lt₂ f hf hf').le

/--
lemma `identities_of_prop₁_of_eq` / 引理 `identities_of_prop₁_of_eq`

English:
lemma identities_of_prop₁_of_eq
  given: {X Y : C} {f : X ⟶ Y} (hf : W₁ f) (h : r.deg X = r.deg Y)
  proof: by
  by_contra
  exact h.not_gt (r.lt₁ _ hf this)

中文:
引理 identities_of_prop₁_of_eq
  条件: {X Y : C} {f : X ⟶ Y} (hf : W₁ f) (h : r.deg X = r.deg Y)
  证明: by
  by_contra
  exact h.not_gt (r.lt₁ _ hf this)

Depends on / 依赖: h.not_gt, not_gt, r.lt
-/
lemma identities_of_prop₁_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₁ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_gt (r.lt₁ _ hf this)

/--
lemma `identities_of_prop₂_of_eq` / 引理 `identities_of_prop₂_of_eq`

English:
lemma identities_of_prop₂_of_eq
  given: {X Y : C} {f : X ⟶ Y} (hf : W₂ f) (h : r.deg X = r.deg Y)
  proof: by
  by_contra
  exact h.not_lt (r.lt₂ _ hf this)

include r in

中文:
引理 identities_of_prop₂_of_eq
  条件: {X Y : C} {f : X ⟶ Y} (hf : W₂ f) (h : r.deg X = r.deg Y)
  证明: by
  by_contra
  exact h.not_lt (r.lt₂ _ hf this)

include r in

Depends on / 依赖: h.not_lt, not_lt, r.lt
-/
lemma identities_of_prop₂_of_eq {X Y : C} {f : X ⟶ Y} (hf : W₂ f) (h : r.deg X = r.deg Y) :
    MorphismProperty.identities _ f := by
  by_contra
  exact h.not_lt (r.lt₂ _ hf this)

include r in
/--
lemma `subsingleton_mapFactorizationData` / 引理 `subsingleton_mapFactorizationData`

English:
lemma subsingleton_mapFactorizationData
  given: ⦃X Y
  statement: C⦄ (f : X ⟶ Y) :
  proof: by
  have := (r.nonempty_unique f).some
  infer_instance

中文:
引理 subsingleton_mapFactorizationData
  条件: ⦃X Y
  结论: C⦄ (f : X ⟶ Y) :
  证明: by
  have := (r.nonempty_unique f).some
  infer_instance

Depends on / 依赖: infer_instance, nonempty_unique, r.nonempty_unique
-/
lemma subsingleton_mapFactorizationData ⦃X Y : C⦄ (f : X ⟶ Y) :
    Subsingleton (W₁.MapFactorizationData W₂ f) := by
  have := (r.nonempty_unique f).some
  infer_instance

/-- The Reedy factorization of a morphism `f : X ⟶ Y` as a morphism in `W₁`
followed by a morphism in `W₂`. -/
@[no_expose]
/--
Definition of `mapFactorizationData` / `mapFactorizationData` 的定义

English:
definition mapFactorizationData
  signature: {X Y : C} (f : X ⟶ Y)
  body: by
  letI := (r.nonempty_unique f).some
  exact default

include r in

中文:
定义 mapFactorizationData
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: by
  letI := (r.nonempty_unique f).some
  exact default

include r in

Depends on / 依赖: nonempty_unique, r.nonempty_unique
-/
noncomputable def mapFactorizationData {X Y : C} (f : X ⟶ Y) :
    W₁.MapFactorizationData W₂ f := by
  letI := (r.nonempty_unique f).some
  exact default

include r in
/--
lemma `unique_obj` / 引理 `unique_obj`

English:
lemma unique_obj
  given: {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f)
  proof: by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  rfl

include r in

中文:
引理 unique_obj
  条件: {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f)
  证明: by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  rfl

include r in

Depends on / 依赖: Subsingleton, Subsingleton.elim, r.subsingleton_mapFactorizationData, subsingleton_mapFactorizationData
-/
lemma unique_obj {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    fac.Z = fac'.Z := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  rfl

include r in
/--
lemma `unique` / 引理 `unique`

English:
lemma unique
  given: {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f)
  proof: by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  simp

中文:
引理 unique
  条件: {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f)
  证明: by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  simp

Depends on / 依赖: Subsingleton, Subsingleton.elim, r.subsingleton_mapFactorizationData, subsingleton_mapFactorizationData
-/
lemma unique {X Y : C} {f : X ⟶ Y} (fac fac' : W₁.MapFactorizationData W₂ f) :
    exists (h : fac.Z = fac'.Z), fac.i = fac'.i ≫ eqToHom h.symm ∧ fac.p = eqToHom h ≫ fac'.p := by
  have := r.subsingleton_mapFactorizationData f
  obtain rfl : fac = fac' := Subsingleton.elim _ _
  simp

/-- The degree of a morphism for a Reedy structure. It is defined as the degree of
the intermediate object in the Reedy factorization, but it is also the smallest
degree of an intermediate object in a factorization, see the lemma `degHom_le`. -/
@[no_expose]
/--
Definition of `degHom` / `degHom` 的定义

English:
definition degHom
  signature: {X Y : C} (f : X ⟶ Y)
  body: r.deg (r.mapFactorizationData f).Z

中文:
定义 degHom
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: r.deg (r.mapFactorizationData f).Z

Depends on / 依赖: mapFactorizationData, r.deg, r.mapFactorizationData
-/
noncomputable def degHom {X Y : C} (f : X ⟶ Y) : α := r.deg (r.mapFactorizationData f).Z

/--
lemma `degHom_eq` / 引理 `degHom_eq`

English:
lemma degHom_eq
  given: {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f)
  proof: by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl

中文:
引理 degHom_eq
  条件: {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f)
  证明: by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl

Depends on / 依赖: Subsingleton, Subsingleton.elim, mapFactorizationData, r.mapFactorizationData, r.subsingleton_mapFactorizationData, subsingleton_mapFactorizationData
-/
lemma degHom_eq {X Y : C} {f : X ⟶ Y} (h : W₁.MapFactorizationData W₂ f) :
    r.degHom f = r.deg h.Z := by
  have := r.subsingleton_mapFactorizationData
  rw [← Subsingleton.elim (r.mapFactorizationData f) h]
  rfl

/--
lemma `exists_fac` / 引理 `exists_fac`

English:
lemma exists_fac
  given: {X Y : C} (f : X ⟶ Y)
  proof: ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩

中文:
引理 存在_fac
  条件: {X Y : C} (f : X ⟶ Y)
  证明: ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩

Depends on / 依赖: mapFactorizationData, r.mapFactorizationData
-/
lemma exists_fac {X Y : C} (f : X ⟶ Y) :
    exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), W₁ a ∧ W₂ b ∧ a ≫ b = f ∧ r.degHom f = r.deg Z :=
  ⟨_, _, _, (r.mapFactorizationData f).hi, (r.mapFactorizationData f).hp,
    (r.mapFactorizationData f).fac, rfl⟩

/--
lemma `degHom_le` / 引理 `degHom_le`

English:
lemma degHom_le
  given: {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
  proof: by
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg := MorphismProperty.MapFactorizationData.mk (f := f ≫ g) Zh (f₁ ≫ h₁) (h₂ ≫ g₂)
    (by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g])
    (W₁.comp_mem _ _ hf₁ hh₁) (W₂.comp_mem _ _ hh₂ hg₂)
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)

中文:
引理 degHom_le
  条件: {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y)
  证明: by
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg := MorphismProperty.MapFactorizationData.mk (f := f ≫ g) Zh (f₁ ≫ h₁) (h₂ ≫ g₂)
    (by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g])
    (W₁.comp_mem _ _ hf₁ hh₁) (W₂.comp_mem _ _ hh₂ hg₂)
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)

Depends on / 依赖: MapFactorizationData, MorphismProperty, MorphismProperty.MapFactorizationData.mk, comp_mem, degHom_eq, eq_f, eq_g, eq_h, exists_fac, fac_f, fac_g, fac_h, factfg, r.degHom_eq, r.exists_fac, r.le, reassoc_of
-/
lemma degHom_le {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) :
    r.degHom (f ≫ g) <= r.deg Z := by
  obtain ⟨Zf, f₁, f₂, hf₁, hf₂, fac_f, eq_f⟩ := r.exists_fac f
  obtain ⟨Zg, g₁, g₂, hg₁, hg₂, fac_g, eq_g⟩ := r.exists_fac g
  obtain ⟨Zh, h₁, h₂, hh₁, hh₂, fac_h, eq_h⟩ := r.exists_fac (f₂ ≫ g₁)
  let factfg := MorphismProperty.MapFactorizationData.mk (f := f ≫ g) Zh (f₁ ≫ h₁) (h₂ ≫ g₂)
    (by simp [reassoc_of% fac_h, reassoc_of% fac_f, fac_g])
    (W₁.comp_mem _ _ hf₁ hh₁) (W₂.comp_mem _ _ hh₂ hg₂)
  rw [r.degHom_eq factfg]
  exact (r.le₁ _ hh₁).trans (r.le₂ _ hf₂)

/--
lemma `degHom_le_deg_left` / 引理 `degHom_le_deg_left`

English:
lemma degHom_le_deg_left
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simpa using r.degHom_le (𝟙 X) f

中文:
引理 degHom_le_deg_left
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simpa using r.degHom_le (𝟙 X) f

Depends on / 依赖: degHom_le, r.degHom_le
-/
lemma degHom_le_deg_left {X Y : C} (f : X ⟶ Y) :
    r.degHom f <= r.deg X := by
  simpa using r.degHom_le (𝟙 X) f

/--
lemma `degHom_le_deg_right` / 引理 `degHom_le_deg_right`

English:
lemma degHom_le_deg_right
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simpa using r.degHom_le f (𝟙 Y)

中文:
引理 degHom_le_deg_right
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simpa using r.degHom_le f (𝟙 Y)

Depends on / 依赖: degHom_le, r.degHom_le
-/
lemma degHom_le_deg_right {X Y : C} (f : X ⟶ Y) :
    r.degHom f <= r.deg Y := by
  simpa using r.degHom_le f (𝟙 Y)

/--
lemma `degHom_comp_le_left` / 引理 `degHom_comp_le_left`

English:
lemma degHom_comp_le_left
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  have ⟨_, f₁, f₂, _, _, h_fac, h_deg⟩ := r.exists_fac f
  rw [h_deg]; rw [← h_fac]; rw [Category.assoc]
  exact r.degHom_le f₁ (f₂ ≫ g)

中文:
引理 degHom_comp_le_left
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  have ⟨_, f₁, f₂, _, _, h_fac, h_deg⟩ := r.exists_fac f
  rw [h_deg]; rw [← h_fac]; rw [Category.assoc]
  exact r.degHom_le f₁ (f₂ ≫ g)

Depends on / 依赖: Category, Category.assoc, degHom_le, exists_fac, h_deg, h_fac, r.degHom_le, r.exists_fac
-/
lemma degHom_comp_le_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) <= r.degHom f := by
  have ⟨_, f₁, f₂, _, _, h_fac, h_deg⟩ := r.exists_fac f
  rw [h_deg]; rw [← h_fac]; rw [Category.assoc]
  exact r.degHom_le f₁ (f₂ ≫ g)

/--
lemma `degHom_comp_le_right` / 引理 `degHom_comp_le_right`

English:
lemma degHom_comp_le_right
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  have ⟨_, g₁, g₂, _, _, h_fac, h_deg⟩ := r.exists_fac g
  rw [h_deg]; rw [← h_fac]; rw [← Category.assoc]
  exact r.degHom_le (f ≫ g₁) g₂

中文:
引理 degHom_comp_le_right
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  have ⟨_, g₁, g₂, _, _, h_fac, h_deg⟩ := r.exists_fac g
  rw [h_deg]; rw [← h_fac]; rw [← Category.assoc]
  exact r.degHom_le (f ≫ g₁) g₂

Depends on / 依赖: Category, Category.assoc, degHom_le, exists_fac, h_deg, h_fac, r.degHom_le, r.exists_fac
-/
lemma degHom_comp_le_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    r.degHom (f ≫ g) <= r.degHom g := by
  have ⟨_, g₁, g₂, _, _, h_fac, h_deg⟩ := r.exists_fac g
  rw [h_deg]; rw [← h_fac]; rw [← Category.assoc]
  exact r.degHom_le (f ≫ g₁) g₂

/--
lemma `prop₂_of_degHom_eq_deg_left` / 引理 `prop₂_of_degHom_eq_deg_left`

English:
lemma prop₂_of_degHom_eq_deg_left
  given: {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X)
  proof: by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₁_of_eq hp (by aesop)
  obtain rfl : i = f := by simpa using fac
  exact hi

中文:
引理 prop₂_of_degHom_eq_deg_left
  条件: {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X)
  证明: by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₁_of_eq hp (by aesop)
  obtain rfl : i = f := by simpa using fac
  exact hi

Depends on / 依赖: exists_fac, r.exists_fac, r.identities_of_prop
-/
lemma prop₂_of_degHom_eq_deg_left {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg X) :
    W₂ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₁_of_eq hp (by aesop)
  obtain rfl : i = f := by simpa using fac
  exact hi

/--
lemma `prop₁_of_degHom_eq_deg_right` / 引理 `prop₁_of_degHom_eq_deg_right`

English:
lemma prop₁_of_degHom_eq_deg_right
  given: {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y)
  proof: by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₂_of_eq hi (by aesop)
  obtain rfl : p = f := by simpa using fac
  exact hp

中文:
引理 prop₁_of_degHom_eq_deg_right
  条件: {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y)
  证明: by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₂_of_eq hi (by aesop)
  obtain rfl : p = f := by simpa using fac
  exact hp

Depends on / 依赖: exists_fac, r.exists_fac, r.identities_of_prop
-/
lemma prop₁_of_degHom_eq_deg_right {X Y : C} {f : X ⟶ Y} (hf : r.degHom f = r.deg Y) :
    W₁ f := by
  obtain ⟨Z, p, i, hp, hi, fac, h⟩ := r.exists_fac f
  obtain ⟨_⟩ := r.identities_of_prop₂_of_eq hi (by aesop)
  obtain rfl : p = f := by simpa using fac
  exact hp

/--
lemma `degHom_lt_or_of_degHom_comp_lt` / 引理 `degHom_lt_or_of_degHom_comp_lt`

English:
lemma degHom_lt_or_of_degHom_comp_lt
  proof: by
  contrapose! hfg
  let φ := MorphismProperty.MapFactorizationData.mk Z f g rfl
    (r.prop₁_of_degHom_eq_deg_right (le_antisymm (r.degHom_le_deg_right f) hfg.left))
    (r.prop₂_of_degHom_eq_deg_left (le_antisymm (r.degHom_le_deg_left g) hfg.right))
  rw [r.degHom_eq φ]

@[simp]

中文:
引理 degHom_lt_or_of_degHom_comp_lt
  证明: by
  contrapose! hfg
  let φ := MorphismProperty.MapFactorizationData.mk Z f g rfl
    (r.prop₁_of_degHom_eq_deg_right (le_antisymm (r.degHom_le_deg_right f) hfg.left))
    (r.prop₂_of_degHom_eq_deg_left (le_antisymm (r.degHom_le_deg_left g) hfg.right))
  rw [r.degHom_eq φ]

@[simp]

Depends on / 依赖: MapFactorizationData, MorphismProperty, MorphismProperty.MapFactorizationData.mk, contrapose, degHom_eq, degHom_le_deg_left, degHom_le_deg_right, hfg.left, hfg.right, le_antisymm, r.degHom_eq, r.degHom_le_deg_left, r.degHom_le_deg_right, r.prop
-/
lemma degHom_lt_or_of_degHom_comp_lt
    {X Z Y : C} (f : X ⟶ Z) (g : Z ⟶ Y) (hfg : r.degHom (f ≫ g) < r.deg Z) :
    r.degHom f < r.deg Z ∨ r.degHom g < r.deg Z := by
  contrapose! hfg
  let φ := MorphismProperty.MapFactorizationData.mk Z f g rfl
    (r.prop₁_of_degHom_eq_deg_right (le_antisymm (r.degHom_le_deg_right f) hfg.left))
    (r.prop₂_of_degHom_eq_deg_left (le_antisymm (r.degHom_le_deg_left g) hfg.right))
  rw [r.degHom_eq φ]

@[simp]
/--
lemma `degHom_id` / 引理 `degHom_id`

English:
lemma degHom_id
  given: (X : C)
  statement: r.degHom (𝟙 X) = r.deg X
  proof: r.degHom_eq (MorphismProperty.MapFactorizationData.mk X (𝟙 X) (𝟙 X) (by simp) (W₁.id_mem _)
  (W₂.id_mem _))

中文:
引理 degHom_id
  条件: (X : C)
  结论: r.degHom (𝟙 X) = r.deg X
  证明: r.degHom_eq (MorphismProperty.MapFactorizationData.mk X (𝟙 X) (𝟙 X) (by simp) (W₁.id_mem _)
  (W₂.id_mem _))

Depends on / 依赖: MapFactorizationData, MorphismProperty, MorphismProperty.MapFactorizationData.mk, degHom_eq, id_mem, r.degHom_eq
-/
lemma degHom_id (X : C) : r.degHom (𝟙 X) = r.deg X :=
  r.degHom_eq (MorphismProperty.MapFactorizationData.mk X (𝟙 X) (𝟙 X) (by simp) (W₁.id_mem _)
  (W₂.id_mem _))

/--
lemma `deg_eq_of_iso` / 引理 `deg_eq_of_iso`

English:
lemma deg_eq_of_iso
  given: {X Y : C} (e : X ≅ Y)
  statement: r.deg X = r.deg Y
  proof: by
  have {X Y : C} (e : X ≅ Y) : r.deg X <= r.deg Y := by
    rw [← r.degHom_id X]; rw [← e.hom_inv_id]
    apply r.degHom_le
  exact le_antisymm (this e) (this e.symm)

include r in

中文:
引理 deg_eq_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  结论: r.deg X = r.deg Y
  证明: by
  have {X Y : C} (e : X ≅ Y) : r.deg X <= r.deg Y := by
    rw [← r.degHom_id X]; rw [← e.hom_inv_id]
    apply r.degHom_le
  exact le_antisymm (this e) (this e.symm)

include r in

Depends on / 依赖: degHom_id, degHom_le, e.hom_inv_id, e.symm, hom_inv_id, le_antisymm, r.deg, r.degHom_id, r.degHom_le
-/
lemma deg_eq_of_iso {X Y : C} (e : X ≅ Y) : r.deg X = r.deg Y := by
  have {X Y : C} (e : X ≅ Y) : r.deg X <= r.deg Y := by
    rw [← r.degHom_id X]; rw [← e.hom_inv_id]
    apply r.degHom_le
  exact le_antisymm (this e) (this e.symm)

include r in
/--
lemma `prop₁_of_iso` / 引理 `prop₁_of_iso`

English:
lemma prop₁_of_iso
  given: {X Y : C} (e : X ≅ Y)
  statement: W₁ e.hom
  proof: r.prop₁_of_degHom_eq_deg_right (by
    refine le_antisymm ?_ ?_
    · simpa using r.degHom_comp_le_right e.hom (𝟙 Y)
    · simpa using r.degHom_comp_le_right e.inv e.hom)

include r in

中文:
引理 prop₁_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  结论: W₁ e.hom
  证明: r.prop₁_of_degHom_eq_deg_right (by
    refine le_antisymm ?_ ?_
    · simpa using r.degHom_comp_le_right e.hom (𝟙 Y)
    · simpa using r.degHom_comp_le_right e.inv e.hom)

include r in

Depends on / 依赖: degHom_comp_le_right, e.hom, e.inv, le_antisymm, r.degHom_comp_le_right, r.prop
-/
lemma prop₁_of_iso {X Y : C} (e : X ≅ Y) : W₁ e.hom :=
  r.prop₁_of_degHom_eq_deg_right (by
    refine le_antisymm ?_ ?_
    · simpa using r.degHom_comp_le_right e.hom (𝟙 Y)
    · simpa using r.degHom_comp_le_right e.inv e.hom)

include r in
/--
lemma `prop₂_of_iso` / 引理 `prop₂_of_iso`

English:
lemma prop₂_of_iso
  given: {X Y : C} (e : X ≅ Y)
  statement: W₂ e.hom
  proof: (r.op.prop₁_of_iso e.op)

include r in

中文:
引理 prop₂_of_iso
  条件: {X Y : C} (e : X ≅ Y)
  结论: W₂ e.hom
  证明: (r.op.prop₁_of_iso e.op)

include r in

Depends on / 依赖: e.op, r.op.prop
-/
lemma prop₂_of_iso {X Y : C} (e : X ≅ Y) : W₂ e.hom :=
  (r.op.prop₁_of_iso e.op)

include r in
/--
lemma `skeletal` / 引理 `skeletal`

English:
lemma skeletal
  statement: Skeletal C
  proof: by
  intro X Y ⟨e⟩
  exact (r.unique (f := e.hom)
    (.mk X (𝟙 X) e.hom (by simp) (W₁.id_mem X) (r.prop₂_of_iso e))
    (.mk Y e.hom (𝟙 Y) (by simp) (r.prop₁_of_iso e) (W₂.id_mem Y))).choose

中文:
引理 skeletal
  结论: Skeletal C
  证明: by
  intro X Y ⟨e⟩
  exact (r.unique (f := e.hom)
    (.mk X (𝟙 X) e.hom (by simp) (W₁.id_mem X) (r.prop₂_of_iso e))
    (.mk Y e.hom (𝟙 Y) (by simp) (r.prop₁_of_iso e) (W₂.id_mem Y))).choose

Depends on / 依赖: e.hom, id_mem, r.prop, r.unique, unique
-/
lemma skeletal : Skeletal C := by
  intro X Y ⟨e⟩
  exact (r.unique (f := e.hom)
    (.mk X (𝟙 X) e.hom (by simp) (W₁.id_mem X) (r.prop₂_of_iso e))
    (.mk Y e.hom (𝟙 Y) (by simp) (r.prop₁_of_iso e) (W₂.id_mem Y))).choose

end ReedyStructure

end HomotopicalAlgebra
