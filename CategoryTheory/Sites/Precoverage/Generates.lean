/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
public import Mathlib.Logic.Small.Set

/-!
# Generators of a Grothendieck topology

Let `K` be a precoverage and `J` a Grothendieck topology on a category `C`. We
say `K` generates `J` if for every presheaf `F` on `C`, it is a sheaf for `J` if and only
if it is a sheaf for every covering in `K`.

If `K` generates `J`, then `J` is the smallest Grothendieck topology containing `K`. The converse
only holds if `K` is a coverage or a pretopology.

## Implementation details

For `C : Type u` and `Category.{v} C`, the definition of `Precoverage.Generates` quantifies over
presheafs `Cᵒᵖ ⥤ Type max u v`. We then show that this implies that the condition holds
for all presheafs `Cᵒᵖ ⥤ Type w`.
-/

@[expose] public section

universe t t' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
  {K : Precoverage C} {J : GrothendieckTopology C}

namespace Precoverage

/--
Definition of `Generates` / `Generates` 的定义

English:
structure Generates
  parameters: (K : Precoverage C) (J : GrothendieckTopology C)
  axioms and operations (2):
    - le_toPrecoverage : K <= J.toPrecoverage
    - isSheaf_of_forall_max((F : Cᵒᵖ ⥤ Type (max u v)) (H : forall ⦃X : C⦄, forall R in K X, R.IsSheafFor F)) : Presieve.IsSheaf J F

中文:
结构 Generates
  参数: (K : Precoverage C) (J : Grothendieck拓扑 C)
  公理与运算 (2 个):
    - le_toPrecoverage : K <= J.toPrecoverage
    - isSheaf_of_forall_max((F : Cᵒᵖ ⥤ 类型 (最大值 u v)) (H : 对任意 ⦃X : C⦄, 对任意 R in K X, R.IsSheafFor F)) : Presieve.是层 J F
-/
structure Generates (K : Precoverage C) (J : GrothendieckTopology C) : Prop where
  le_toPrecoverage : K <= J.toPrecoverage
  isSheaf_of_forall_max (F : Cᵒᵖ ⥤ Type (max u v)) (H : forall ⦃X : C⦄, forall R in K X, R.IsSheafFor F) :
    Presieve.IsSheaf J F

variable {K : Precoverage C} {J : GrothendieckTopology C}

/--
lemma `Generates.generate_mem` / 引理 `Generates.generate_mem`

English:
lemma Generates.generate_mem
  given: (H : K.Generates J) {X : C} {R : Presieve X} (h : R in K X)
  proof: H.le_toPrecoverage _ h

中文:
引理 Generates.generate_mem
  条件: (H : K.Generates J) {X : C} {R : Presieve X} (h : R in K X)
  证明: H.le_toPrecoverage _ h

Depends on / 依赖: H.le_toPrecoverage, le_toPrecoverage
-/
lemma Generates.generate_mem (H : K.Generates J) {X : C} {R : Presieve X} (h : R in K X) :
    .generate R in J X :=
  H.le_toPrecoverage _ h

/--
lemma `Generates.isSheaf_of_forall_aux` / 引理 `Generates.isSheaf_of_forall_aux`

English:
lemma Generates.isSheaf_of_forall_aux
  statement: (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
  proof: by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR => ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR

中文:
引理 Generates.isSheaf_of_对任意_aux
  结论: (h : K.Generates J) (F : Cᵒᵖ ⥤ 类型 w)
  证明: by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR => ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR
-/
private lemma Generates.isSheaf_of_forall_aux (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : forall ⦃X : C⦄, forall R in K X, Presieve.IsSheafFor F R)
    [forall (Z : C), _root_.Small.{max u v} (F.obj (.op Z))] :
    Presieve.IsSheaf J F := by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR => ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR

/--
lemma `Generates.isSheaf_of_forall` / 引理 `Generates.isSheaf_of_forall`

English:
lemma Generates.isSheaf_of_forall
  statement: (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
  proof: by
  /- By assumption, the statement holds for `w = max u v`. The idea of the proof is
  to construct a suitable `Type max u v` valued subsheaf of `F` for each covering sieve `S` in
  `J` and every family of sections over `S` to check the necessary conditions.
  We explain existence below, uniqueness works similarly. -/
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2) union
      .range (fun (g : Z ⟶ X) => F.map g.op t₁) union .range (fun (g : Z ⟶ X) => F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
fun Z g hg => ⟨x g hg, .base .inl .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ in Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ in Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    have : (⟨t₁, ht₁'⟩ : Q.obj _) = ⟨t₂, ht₂'⟩ :=
      (hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩ (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)
    simp_all
  · -- Let `x` be a compatible family of elements over `S`. We need to show it glues.
    intro x hx
    -- Let `𝒮` be the family of subsets consisting of the family of elements `x`.
    let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2)
    /- Let `Q` be the smallest `K`-subsheaf of `K` containing `𝒮`. This is `max u v`-small, because
    `𝒮` is `max u v`-small. -/
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    /- By assumption, `Q` is a `J`-sheaf, so the family of sections `x` glues and gives rise
    to an amalgamation of `x` in `F`. -/
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg => ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    exact ⟨t.val, ht.map Q.ι⟩

中文:
引理 Generates.isSheaf_of_对任意
  结论: (h : K.Generates J) (F : Cᵒᵖ ⥤ 类型 w)
  证明: by
  /- By assumption, the statement holds for `w = max u v`. The idea of the proof is
  to construct a suitable `Type max u v` valued subsheaf of `F` for each covering sieve `S` in
  `J` and every family of sections over `S` to check the necessary conditions.
  We explain existence below, uniqueness works similarly. -/
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2) union
      .range (fun (g : Z ⟶ X) => F.map g.op t₁) union .range (fun (g : Z ⟶ X) => F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
fun Z g hg => ⟨x g hg, .base .inl .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ in Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ in Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    have : (⟨t₁, ht₁'⟩ : Q.obj _) = ⟨t₂, ht₂'⟩ :=
      (hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩ (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)
    simp_all
  · -- Let `x` be a compatible family of elements over `S`. We need to show it glues.
    intro x hx
    -- Let `𝒮` be the family of subsets consisting of the family of elements `x`.
    let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2)
    /- Let `Q` be the smallest `K`-subsheaf of `K` containing `𝒮`. This is `max u v`-small, because
    `𝒮` is `max u v`-small. -/
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    /- By assumption, `Q` is a `J`-sheaf, so the family of sections `x` glues and gives rise
    to an amalgamation of `x` in `F`. -/
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg => ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    exact ⟨t.val, ht.map Q.ι⟩
-/
lemma Generates.isSheaf_of_forall (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : forall ⦃X : C⦄, forall R in K X, Presieve.IsSheafFor F R) :
    Presieve.IsSheaf J F := by
  /- By assumption, the statement holds for `w = max u v`. The idea of the proof is
  to construct a suitable `Type max u v` valued subsheaf of `F` for each covering sieve `S` in
  `J` and every family of sections over `S` to check the necessary conditions.
  We explain existence below, uniqueness works similarly. -/
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2) union
      .range (fun (g : Z ⟶ X) => F.map g.op t₁) union .range (fun (g : Z ⟶ X) => F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
fun Z g hg => ⟨x g hg, .base .inl .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ in Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ in Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    have : (⟨t₁, ht₁'⟩ : Q.obj _) = ⟨t₂, ht₂'⟩ :=
      (hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩ (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)
    simp_all
  · -- Let `x` be a compatible family of elements over `S`. We need to show it glues.
    intro x hx
    -- Let `𝒮` be the family of subsets consisting of the family of elements `x`.
    let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) => x _ g.2)
    /- Let `Q` be the smallest `K`-subsheaf of `K` containing `𝒮`. This is `max u v`-small, because
    `𝒮` is `max u v`-small. -/
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR => isSheafFor_subsheafify _ hR (H _ hR)
    /- By assumption, `Q` is a `J`-sheaf, so the family of sections `x` glues and gives rise
    to an amalgamation of `x` in `F`. -/
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg => ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    exact ⟨t.val, ht.map Q.ι⟩

/--
lemma `Generates.isSheaf_type_iff` / 引理 `Generates.isSheaf_type_iff`

English:
lemma Generates.isSheaf_type_iff
  given: (H : K.Generates J) {F : Cᵒᵖ ⥤ Type w}
  proof: by
  refine ⟨fun h X R hR => ?_, fun h => H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

中文:
引理 Generates.isSheaf_type_iff
  条件: (H : K.Generates J) {F : Cᵒᵖ ⥤ 类型 w}
  证明: by
  refine ⟨fun h X R hR => ?_, fun h => H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

Depends on / 依赖: H.isSheaf_of_forall, H.le_toPrecoverage, Presieve, Presieve.isSheafFor_iff_generate, isSheafFor_iff_generate, isSheaf_of_forall, le_toPrecoverage
-/
lemma Generates.isSheaf_type_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ Type w} :
    Presieve.IsSheaf J F ↔ forall ⦃X : C⦄, forall R in K X, Presieve.IsSheafFor F R := by
  refine ⟨fun h X R hR => ?_, fun h => H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

/--
lemma `Generates.toGrothendieck_eq` / 引理 `Generates.toGrothendieck_eq`

English:
lemma Generates.toGrothendieck_eq
  given: (H : K.Generates J)
  statement: K.toGrothendieck = J
  proof: by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)

中文:
引理 Generates.toGrothendieck_eq
  条件: (H : K.Generates J)
  结论: K.toGrothendieck = J
  证明: by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)

Depends on / 依赖: CategoryTheory, CategoryTheory.le_topology_of_closedSieves_isSheaf, H.isSheaf_type_iff, H.le_toPrecoverage, K.generate_mem_toGrothendieck, K.toGrothendieck, Presieve, Presieve.isSheafFor_iff_generate, classifier_isSheaf, generate_mem_toGrothendieck, isSheafFor_iff_generate, isSheaf_type_iff, le_antisymm, le_toPrecoverage, le_topology_of_closedSieves_isSheaf, toGrothendieck, toGrothendieck_le_iff_le_toPrecoverage
-/
lemma Generates.toGrothendieck_eq (H : K.Generates J) : K.toGrothendieck = J := by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)

/--
lemma `Generates.isSheaf_iff` / 引理 `Generates.isSheaf_iff`

English:
lemma Generates.isSheaf_iff
  given: (H : K.Generates J) {F : Cᵒᵖ ⥤ A}
  proof: by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

中文:
引理 Generates.isSheaf_iff
  条件: (H : K.Generates J) {F : Cᵒᵖ ⥤ A}
  证明: by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

Depends on / 依赖: H.isSheaf_type_iff, IsSheaf, Presheaf, Presheaf.IsSheaf, isSheaf_type_iff
-/
lemma Generates.isSheaf_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ A} :
    Presheaf.IsSheaf J F ↔ forall ⦃X : C⦄, forall R in K X, forall (M : A),
      Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) R := by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

end Precoverage

/--
lemma `Coverage.generates_toGrothendieck` / 引理 `Coverage.generates_toGrothendieck`

English:
lemma Coverage.generates_toGrothendieck
  given: (K : Coverage C)
  statement: K.Generates K.toGrothendieck where
  proof: by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage]; rw [← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]

中文:
引理 余verage.generates_toGrothendieck
  条件: (K : 余verage C)
  结论: K.Generates K.toGrothendieck where
  证明: by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage]; rw [← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_le_iff_le_toPrecoverage, Presieve, Presieve.isSheaf_coverage, isSheaf_coverage, isSheaf_of_forall_max, toGrothendieck_le_iff_le_toPrecoverage, toGrothendieck_toPrecoverage
-/
lemma Coverage.generates_toGrothendieck (K : Coverage C) : K.Generates K.toGrothendieck where
  le_toPrecoverage := by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage]; rw [← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]

/--
lemma `Coverage.generates_iff` / 引理 `Coverage.generates_iff`

English:
lemma Coverage.generates_iff
  given: {K : Coverage C}
  statement: K.Generates J ↔ K.toGrothendieck = J
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

中文:
引理 余verage.generates_iff
  条件: {K : 余verage C}
  结论: K.Generates J ↔ K.toGrothendieck = J
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

Depends on / 依赖: Coverage, Coverage.generates_toGrothendieck, Coverage.toGrothendieck_toPrecoverage, generates_toGrothendieck, h.toGrothendieck_eq, toGrothendieck_eq, toGrothendieck_toPrecoverage
-/
lemma Coverage.generates_iff {K : Coverage C} : K.Generates J ↔ K.toGrothendieck = J := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

end CategoryTheory
