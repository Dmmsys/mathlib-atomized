/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subfunctor.Sieves

/-!

# Subsheaf of types

We define the subsheaf of a type-valued presheaf.

## Main results

- `CategoryTheory.Subfunctor.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `CategoryTheory.Subfunctor.sheafify_isSheaf` :
  The sheafification is a sheaf
- `CategoryTheory.Subfunctor.sheafifyLift` :
  The descent of a map into a sheaf to the sheafification.
- `CategoryTheory.GrothendieckTopology.imageSheaf` : The image sheaf of a morphism.
- `CategoryTheory.GrothendieckTopology.imageFactorization` : The image sheaf as a
  `Limits.imageFactorization`.
-/

@[expose] public section


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subfunctor F)

/--
theorem `Subfunctor.isSeparated` / 定理 `Subfunctor.isSeparated`

English:
theorem Subfunctor.isSeparated
  given: {J : GrothendieckTopology C} (h : Presieve.IsSeparated J F)
  proof: fun _ S hS _ _ _ hx₁ hx₂ => Subtype.ext h S hS _ _ _ (hx₁.map G.ι) (hx₂.map G.ι)

中文:
定理 子函子.isSeparated
  条件: {J : Grothendieck拓扑 C} (h : Presieve.是分离 J F)
  证明: fun _ S hS _ _ _ hx₁ hx₂ => Subtype.ext h S hS _ _ _ (hx₁.map G.ι) (hx₂.map G.ι)

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem Subfunctor.isSeparated {J : GrothendieckTopology C} (h : Presieve.IsSeparated J F) :
    Presieve.IsSeparated J G.toFunctor :=
fun _ S hS _ _ _ hx₁ hx₂ => Subtype.ext h S hS _ _ _ (hx₁.map G.ι) (hx₂.map G.ι)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Subfunctor.sheafify` / `Subfunctor.sheafify` 的定义

English:
definition Subfunctor.sheafify
  signature: : Subfunctor F where
  body: { s | G.sieveOfSection s in J (unop U) }
  map := by
    rintro U V i s hs
    refine J.superset_covering ?_ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h ⊢
    rwa [← comp_apply, ← Functor.map_comp]

中文:
定义 子函子.sheafify
  签名: : 子函子 F where
  定义体: { s | G.sieveOfSection s in J (unop U) }
  map := by
    rintro U V i s hs
    refine J.superset_covering ?_ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h ⊢
    rwa [← comp_apply, ← Functor.map_comp]

Depends on / 依赖: G.sieveOfSection, sieveOfSection
-/
def Subfunctor.sheafify : Subfunctor F where
  obj U := { s | G.sieveOfSection s in J (unop U) }
  map := by
    rintro U V i s hs
    refine J.superset_covering ?_ (J.pullback_stable i.unop hs)
    intro _ _ h
    dsimp at h ⊢
    rwa [← comp_apply, ← Functor.map_comp]

/--
theorem `Subfunctor.le_sheafify` / 定理 `Subfunctor.le_sheafify`

English:
theorem Subfunctor.le_sheafify
  statement: G <= G.sheafify J
  proof: by
  intro U s hs
  change _ in J _
  convert! J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

中文:
定理 子函子.le_sheafify
  结论: G <= G.sheafify J
  证明: by
  intro U s hs
  change _ in J _
  convert! J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

Depends on / 依赖: G.map, J.top_mem, U.unop, convert, eq_top_iff, i.op, top_mem
-/
theorem Subfunctor.le_sheafify : G <= G.sheafify J := by
  intro U s hs
  change _ in J _
  convert! J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

variable {J}

/--
theorem `Subfunctor.eq_sheafify` / 定理 `Subfunctor.eq_sheafify`

English:
theorem Subfunctor.eq_sheafify
  given: (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toFunctor)
  proof: by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) :)

中文:
定理 子函子.eq_sheafify
  条件: (h : Presieve.是层 J F) (hG : Presieve.是层 J G.toFunctor)
  证明: by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) :)

Depends on / 依赖: G.family_of_elements_compatible, G.le_sheafify, Subtype, Subtype.val, amalgamate, antisymm, congr_arg, family_of_elements_compatible, isSeparatedFor, isSeparatedFor.ext, le_sheafify, valid_glue
-/
theorem Subfunctor.eq_sheafify (h : Presieve.IsSheaf J F) (hG : Presieve.IsSheaf J G.toFunctor) :
    G = G.sheafify J := by
  apply (G.le_sheafify J).antisymm
  intro U s hs
  suffices ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).1 = s by
    rw [← this]
    exact ((hG _ hs).amalgamate _ (G.family_of_elements_compatible s)).2
  apply (h _ hs).isSeparatedFor.ext
  intro V i hi
  exact (congr_arg Subtype.val ((hG _ hs).valid_glue (G.family_of_elements_compatible s) _ hi) :)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `Subfunctor.sheafify_isSheaf` / 定理 `Subfunctor.sheafify_isSheaf`

English:
theorem Subfunctor.sheafify_isSheaf
  given: (hF : Presieve.IsSheaf J F)
  proof: by
  refine (isSeparated _ hF.isSeparated).isSheaf fun U S hS x hx => ?_
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  dsimp [-Sieve.bind_apply] at *
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  have H : forall s, x''.IsAmalgamation s.1 -> x.IsAmalgamation s := by
    intro s H V i hi
    refine Subtype.ext ?_
    apply (hF _ (x i hi).2).isSeparatedFor.ext
    intro V' i' hi'
    have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
    have := H _ hi''
    rw [op_comp]; rw [F.map_comp] at this
    exact this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [Functor.map_comp]
    simpa using!
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine ⟨⟨t, _⟩, H ⟨t, ?_⟩ ht⟩
  refine J.superset_covering ?_ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ _ _ hi

中文:
定理 子函子.sheafify_isSheaf
  条件: (hF : Presieve.是层 J F)
  证明: by
  refine (isSeparated _ hF.isSeparated).isSheaf fun U S hS x hx => ?_
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  dsimp [-Sieve.bind_apply] at *
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  have H : forall s, x''.IsAmalgamation s.1 -> x.IsAmalgamation s := by
    intro s H V i hi
    refine Subtype.ext ?_
    apply (hF _ (x i hi).2).isSeparatedFor.ext
    intro V' i' hi'
    have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
    have := H _ hi''
    rw [op_comp]; rw [F.map_comp] at this
    exact this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [Functor.map_comp]
    simpa using!
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine ⟨⟨t, _⟩, H ⟨t, ?_⟩ ht⟩
  refine J.superset_covering ?_ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ _ _ hi

Depends on / 依赖: F.map, FamilyOfElements, G.sieveOfSection, IsAmalgamation, Presieve, Presieve.FamilyOfElements, Sieve.bind, Sieve.bind_apply, Subtype, Subtype.ext, bind_apply, hF.isSeparated, isSeparated, isSeparatedFor, isSeparatedFor.ext, isSheaf, sieveOfSection, x.IsAmalgamation
-/
theorem Subfunctor.sheafify_isSheaf (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (G.sheafify J).toFunctor := by
  refine (isSeparated _ hF.isSeparated).isSheaf fun U S hS x hx => ?_
  let S' := Sieve.bind S fun Y f hf => G.sieveOfSection (x f hf).1
  have := fun (V) (i : V ⟶ U) (hi : S' i) => hi
  choose W i₁ i₂ hi₂ h₁ h₂ using this
  dsimp [-Sieve.bind_apply] at *
  let x'' : Presieve.FamilyOfElements F S' := fun V i hi => F.map (i₁ V i hi).op (x _ (hi₂ V i hi))
  have H : forall s, x''.IsAmalgamation s.1 -> x.IsAmalgamation s := by
    intro s H V i hi
    refine Subtype.ext ?_
    apply (hF _ (x i hi).2).isSeparatedFor.ext
    intro V' i' hi'
    have hi'' : S' (i' ≫ i) := ⟨_, _, _, hi, hi', rfl⟩
    have := H _ hi''
    rw [op_comp]; rw [F.map_comp] at this
    exact this.trans (congr_arg Subtype.val (hx _ _ (hi₂ _ _ hi'') hi (h₂ _ _ hi'')))
  have : x''.Compatible := by
    intro V₁ V₂ V₃ g₁ g₂ g₃ g₄ S₁ S₂ e
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [Functor.map_comp]
    simpa using!
      congr_arg Subtype.val
        (hx (g₁ ≫ i₁ _ _ S₁) (g₂ ≫ i₁ _ _ S₂) (hi₂ _ _ S₁) (hi₂ _ _ S₂)
        (by simp only [Category.assoc, h₂, e]))
  obtain ⟨t, ht, ht'⟩ := hF _ (J.bind_covering hS fun V i hi => (x i hi).2) _ this
  refine ⟨⟨t, _⟩, H ⟨t, ?_⟩ ht⟩
  refine J.superset_covering ?_ (J.bind_covering hS fun V i hi => (x i hi).2)
  intro V i hi
  dsimp
  rw [ht _ hi]
  exact h₁ _ _ hi

/--
theorem `Subfunctor.eq_sheafify_iff` / 定理 `Subfunctor.eq_sheafify_iff`

English:
theorem Subfunctor.eq_sheafify_iff
  given: (h : Presieve.IsSheaf J F)
  proof: ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩

中文:
定理 子函子.eq_sheafify_iff
  条件: (h : Presieve.是层 J F)
  证明: ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩

Depends on / 依赖: G.eq_sheafify, G.sheafify_isSheaf, e.symm, eq_sheafify, sheafify_isSheaf
-/
theorem Subfunctor.eq_sheafify_iff (h : Presieve.IsSheaf J F) :
    G = G.sheafify J ↔ Presieve.IsSheaf J G.toFunctor :=
  ⟨fun e => e.symm ▸ G.sheafify_isSheaf h, G.eq_sheafify h⟩

/--
theorem `Subfunctor.isSheaf_iff` / 定理 `Subfunctor.isSheaf_iff`

English:
theorem Subfunctor.isSheaf_iff
  given: (h : Presieve.IsSheaf J F)
  proof: by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J <= G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩

中文:
定理 子函子.isSheaf_iff
  条件: (h : Presieve.是层 J F)
  证明: by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J <= G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩

Depends on / 依赖: Eq.ge, G.eq_sheafify_iff, G.le_sheafify, G.sheafify, antisymm, eq_sheafify_iff, le_sheafify, sheafify
-/
theorem Subfunctor.isSheaf_iff (h : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J G.toFunctor ↔
      forall (U) (s : F.obj U), G.sieveOfSection s in J (unop U) -> s in G.obj U := by
  rw [← G.eq_sheafify_iff h]
  change _ ↔ G.sheafify J <= G
  exact ⟨Eq.ge, (G.le_sheafify J).antisymm⟩

/--
theorem `Subfunctor.sheafify_sheafify` / 定理 `Subfunctor.sheafify_sheafify`

English:
theorem Subfunctor.sheafify_sheafify
  given: (h : Presieve.IsSheaf J F)
  proof: ((Subfunctor.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm

中文:
定理 子函子.sheafify_sheafify
  条件: (h : Presieve.是层 J F)
  证明: ((Subfunctor.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm

Depends on / 依赖: G.sheafify_isSheaf, Subfunctor, Subfunctor.eq_sheafify_iff, eq_sheafify_iff, sheafify_isSheaf
-/
theorem Subfunctor.sheafify_sheafify (h : Presieve.IsSheaf J F) :
    (G.sheafify J).sheafify J = G.sheafify J :=
  ((Subfunctor.eq_sheafify_iff _ h).mpr <| G.sheafify_isSheaf h).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Subfunctor.sheafifyLift` / `Subfunctor.sheafifyLift` 的定义

English:
definition Subfunctor.sheafifyLift
  signature: (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F')
  body: ↾fun s => (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).map f)
  naturality := by
    intro U V i
    ext s
    apply (h _ ((Subfunctor.sheafify J G).toFunctor.map i s).prop).isSeparatedFor.ext
    intro W j hj
    refine (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toFunctor.map i s).2)
      ((G.family_of_elements_compatible _).map _) _ hj).trans ?_
    dsimp
    simp only [← comp_apply, ← Functor.map_comp]
    change _ = F'.map (j ≫ i.unop).op _
    refine Eq.trans ?_ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).map f) (j ≫ i.unop) ?_).symm
    · simp [Presieve.FamilyOfElements.map, Subfunctor.familyOfElementsOfSection]
      rfl
    · dsimp [Presieve.FamilyOfElements.map] at hj ⊢
      rwa [Functor.map_comp, comp_apply]

中文:
定义 子函子.sheafifyLift
  签名: (f : G.toFunctor ⟶ F') (h : Presieve.是层 J F')
  定义体: ↾fun s => (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).map f)
  naturality := by
    intro U V i
    ext s
    apply (h _ ((Subfunctor.sheafify J G).toFunctor.map i s).prop).isSeparatedFor.ext
    intro W j hj
    refine (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toFunctor.map i s).2)
      ((G.family_of_elements_compatible _).map _) _ hj).trans ?_
    dsimp
    simp only [← comp_apply, ← Functor.map_comp]
    change _ = F'.map (j ≫ i.unop).op _
    refine Eq.trans ?_ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).map f) (j ≫ i.unop) ?_).symm
    · simp [Presieve.FamilyOfElements.map, Subfunctor.familyOfElementsOfSection]
      rfl
    · dsimp [Presieve.FamilyOfElements.map] at hj ⊢
      rwa [Functor.map_comp, comp_apply]

Depends on / 依赖: G.sieveOfSection, amalgamate, s.prop, sieveOfSection
-/
noncomputable def Subfunctor.sheafifyLift (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F') :
    (G.sheafify J).toFunctor ⟶ F' where
  app _ := ↾fun s => (h (G.sieveOfSection s.1) s.prop).amalgamate
    (_) ((G.family_of_elements_compatible s.1).map f)
  naturality := by
    intro U V i
    ext s
    apply (h _ ((Subfunctor.sheafify J G).toFunctor.map i s).prop).isSeparatedFor.ext
    intro W j hj
    refine (Presieve.IsSheafFor.valid_glue (h _ ((G.sheafify J).toFunctor.map i s).2)
      ((G.family_of_elements_compatible _).map _) _ hj).trans ?_
    dsimp
    simp only [← comp_apply, ← Functor.map_comp]
    change _ = F'.map (j ≫ i.unop).op _
    refine Eq.trans ?_ (Presieve.IsSheafFor.valid_glue (h _ s.2)
      ((G.family_of_elements_compatible s.1).map f) (j ≫ i.unop) ?_).symm
    · simp [Presieve.FamilyOfElements.map, Subfunctor.familyOfElementsOfSection]
      rfl
    · dsimp [Presieve.FamilyOfElements.map] at hj ⊢
      rwa [Functor.map_comp, comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Subfunctor.to_sheafifyLift` / 定理 `Subfunctor.to_sheafifyLift`

English:
theorem Subfunctor.to_sheafifyLift
  given: (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F')
  proof: by
  ext U s
  apply (h _ ((Subfunctor.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  intro V i hi
  have := elementwise_of% f.naturality
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : _ <= sheafify _ _)).app _ _).2)
    ((G.family_of_elements_compatible _).map _) _ _).trans (this _ _)

中文:
定理 子函子.to_sheafifyLift
  条件: (f : G.toFunctor ⟶ F') (h : Presieve.是层 J F')
  证明: by
  ext U s
  apply (h _ ((Subfunctor.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  intro V i hi
  have := elementwise_of% f.naturality
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : _ <= sheafify _ _)).app _ _).2)
    ((G.family_of_elements_compatible _).map _) _ _).trans (this _ _)

Depends on / 依赖: G.family_of_elements_compatible, G.le_sheafify, IsSheafFor, Presieve, Presieve.IsSheafFor.valid_glue, Subfunctor, Subfunctor.homOfLe, elementwise_of, f.naturality, family_of_elements_compatible, homOfLe, isSeparatedFor, isSeparatedFor.ext, le_sheafify, naturality, sheafify, valid_glue
-/
theorem Subfunctor.to_sheafifyLift (f : G.toFunctor ⟶ F') (h : Presieve.IsSheaf J F') :
    Subfunctor.homOfLe (G.le_sheafify J) ≫ G.sheafifyLift f h = f := by
  ext U s
  apply (h _ ((Subfunctor.homOfLe (G.le_sheafify J)).app U s).prop).isSeparatedFor.ext
  intro V i hi
  have := elementwise_of% f.naturality
  exact (Presieve.IsSheafFor.valid_glue (h _ ((homOfLe (_ : _ <= sheafify _ _)).app _ _).2)
    ((G.family_of_elements_compatible _).map _) _ _).trans (this _ _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `Subfunctor.to_sheafify_lift_unique` / 定理 `Subfunctor.to_sheafify_lift_unique`

English:
theorem Subfunctor.to_sheafify_lift_unique
  statement: (h : Presieve.IsSheaf J F')
  proof: by
  ext U s
  apply (h _ s.prop).isSeparatedFor.ext
  rintro V i hi
  dsimp
  rw [← dsimp% l₁.naturality_apply]; rw [← dsimp% l₂.naturality_apply]
  exact ConcreteCategory.congr_hom (congr_app e <| op V) ⟨_, hi⟩

中文:
定理 子函子.to_sheafify_lift_unique
  结论: (h : Presieve.是层 J F')
  证明: by
  ext U s
  apply (h _ s.prop).isSeparatedFor.ext
  rintro V i hi
  dsimp
  rw [← dsimp% l₁.naturality_apply]; rw [← dsimp% l₂.naturality_apply]
  exact ConcreteCategory.congr_hom (congr_app e <| op V) ⟨_, hi⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_app, congr_hom, isSeparatedFor, isSeparatedFor.ext, naturality_apply, s.prop
-/
theorem Subfunctor.to_sheafify_lift_unique (h : Presieve.IsSheaf J F')
    (l₁ l₂ : (G.sheafify J).toFunctor ⟶ F')
    (e : Subfunctor.homOfLe (G.le_sheafify J) ≫ l₁ = Subfunctor.homOfLe (G.le_sheafify J) ≫ l₂) :
    l₁ = l₂ := by
  ext U s
  apply (h _ s.prop).isSeparatedFor.ext
  rintro V i hi
  dsimp
  rw [← dsimp% l₁.naturality_apply]; rw [← dsimp% l₂.naturality_apply]
  exact ConcreteCategory.congr_hom (congr_app e <| op V) ⟨_, hi⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Subfunctor.sheafify_le` / 定理 `Subfunctor.sheafify_le`

English:
theorem Subfunctor.sheafify_le
  statement: (h : G <= G') (hF : Presieve.IsSheaf J F)
  proof: by
  intro U x hx
  convert! ((G.sheafifyLift (Subfunctor.homOfLe h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).isSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.toFunctor ⟶ G'.toFunctor => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subfunctor.homOfLe h) hG')
  convert! this.symm
  rw [← Subfunctor.nat_trans_naturality]
  rfl

中文:
定理 子函子.sheafify_le
  结论: (h : G <= G') (hF : Presieve.是层 J F)
  证明: by
  intro U x hx
  convert! ((G.sheafifyLift (Subfunctor.homOfLe h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).isSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.toFunctor ⟶ G'.toFunctor => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subfunctor.homOfLe h) hG')
  convert! this.symm
  rw [← Subfunctor.nat_trans_naturality]
  rfl

Depends on / 依赖: G.sheafifyLift, G.toFunctor, G.to_sheafifyLift, NatTrans, NatTrans.app, Subfunctor, Subfunctor.homOfLe, Subfunctor.nat_trans_naturality, congr_arg, convert, homOfLe, isSeparatedFor, isSeparatedFor.ext, nat_trans_naturality, sheafifyLift, this.symm, toFunctor, to_sheafifyLift
-/
theorem Subfunctor.sheafify_le (h : G <= G') (hF : Presieve.IsSheaf J F)
    (hG' : Presieve.IsSheaf J G'.toFunctor) : G.sheafify J <= G' := by
  intro U x hx
  convert! ((G.sheafifyLift (Subfunctor.homOfLe h) hG').app U ⟨x, hx⟩).2
  apply (hF _ hx).isSeparatedFor.ext
  intro V i hi
  have :=
    congr_arg (fun f : G.toFunctor ⟶ G'.toFunctor => (NatTrans.app f (op V) ⟨_, hi⟩).1)
      (G.to_sheafifyLift (Subfunctor.homOfLe h) hG')
  convert! this.symm
  rw [← Subfunctor.nat_trans_naturality]
  rfl

section Image

variable (J) in
/-- A morphism factors through the sheafification of the image presheaf. -/
@[simps! +dsimpLhs]
/--
Definition of `Subfunctor.toRangeSheafify` / `Subfunctor.toRangeSheafify` 的定义

English:
definition Subfunctor.toRangeSheafify
  signature: (f : F' ⟶ F)
  body: toRange f ≫ Subfunctor.homOfLe ((range f).le_sheafify J)

中文:
定义 子函子.toRangeSheafify
  签名: (f : F' ⟶ F)
  定义体: toRange f ≫ Subfunctor.homOfLe ((range f).le_sheafify J)

Depends on / 依赖: Subfunctor, Subfunctor.homOfLe, homOfLe, le_sheafify, toRange
-/
def Subfunctor.toRangeSheafify (f : F' ⟶ F) : F' ⟶ ((Subfunctor.range f).sheafify J).toFunctor :=
  toRange f ≫ Subfunctor.homOfLe ((range f).le_sheafify J)

/-- The image sheaf of a morphism between sheaves, defined to be the sheafification of
`image_presheaf`. -/
@[simps]
/--
Definition of `Sheaf.image` / `Sheaf.image` 的定义

English:
definition Sheaf.image
  signature: {F F' : Sheaf J (Type w)} (f : F ⟶ F')
  body: ⟨((Subfunctor.range f.1).sheafify J).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F'.2⟩

中文:
定义 层.像
  签名: {F F' : 层 J (类型 w)} (f : F ⟶ F')
  定义体: ⟨((Subfunctor.range f.1).sheafify J).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F'.2⟩

Depends on / 依赖: Subfunctor, Subfunctor.range, Subfunctor.sheafify_isSheaf, isSheaf_iff_isSheaf_of_type, sheafify, sheafify_isSheaf, toFunctor
-/
def Sheaf.image {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf J (Type w) :=
  ⟨((Subfunctor.range f.1).sheafify J).toFunctor, by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact F'.2⟩

/-- A morphism factors through the image sheaf. -/
@[simps]
/--
Definition of `Sheaf.toImage` / `Sheaf.toImage` 的定义

English:
definition Sheaf.toImage
  signature: {F F' : Sheaf J (Type w)} (f : F ⟶ F')
  body: ⟨Subfunctor.toRangeSheafify J f.1⟩

中文:
定义 层.toImage
  签名: {F F' : 层 J (类型 w)} (f : F ⟶ F')
  定义体: ⟨Subfunctor.toRangeSheafify J f.1⟩

Depends on / 依赖: Subfunctor, Subfunctor.toRangeSheafify, toRangeSheafify
-/
def Sheaf.toImage {F F' : Sheaf J (Type w)} (f : F ⟶ F') : F ⟶ Sheaf.image f :=
  ⟨Subfunctor.toRangeSheafify J f.1⟩

/-- The inclusion of the image sheaf to the target. -/
@[simps]
/--
Definition of `Sheaf.imageι` / `Sheaf.imageι` 的定义

English:
definition Sheaf.imageι
  signature: {F F' : Sheaf J (Type w)} (f : F ⟶ F')
  body: ⟨Subfunctor.ι _⟩

中文:
定义 层.imageι
  签名: {F F' : 层 J (类型 w)} (f : F ⟶ F')
  定义体: ⟨Subfunctor.ι _⟩

Depends on / 依赖: Subfunctor
-/
def Sheaf.imageι {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Sheaf.image f ⟶ F' :=
  ⟨Subfunctor.ι _⟩


set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `Sheaf.toImage_ι` / 定理 `Sheaf.toImage_ι`

English:
theorem Sheaf.toImage_ι
  given: {F F' : Sheaf J (Type w)} (f : F ⟶ F')
  proof: by
  ext1
  simp [Subfunctor.toRangeSheafify]

中文:
定理 层.toImage_ι
  条件: {F F' : 层 J (类型 w)} (f : F ⟶ F')
  证明: by
  ext1
  simp [Subfunctor.toRangeSheafify]

Depends on / 依赖: Subfunctor, Subfunctor.toRangeSheafify, toRangeSheafify
-/
theorem Sheaf.toImage_ι {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    toImage f ≫ imageι f = f := by
  ext1
  simp [Subfunctor.toRangeSheafify]

set_option backward.defeqAttrib.useBackward true in
instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Mono (Sheaf.imageι f) :=
  (sheafToPresheaf J _).mono_of_mono_map
    (by
      dsimp
      infer_instance)

set_option backward.isDefEq.respectTransparency.types false in
instance {F F' : Sheaf J (Type w)} (f : F ⟶ F') : Epi (Sheaf.toImage f) := by
  refine ⟨@fun G' g₁ g₂ e => ?_⟩
  ext U ⟨s, hx⟩
  apply ((isSheaf_iff_isSheaf_of_type J _).mp G'.2 _ hx).isSeparatedFor.ext
  rintro V i ⟨y, e'⟩
  change (g₁.hom.app _ ≫ G'.obj.map _) _ = (g₂.hom.app _ ≫ G'.obj.map _) _
  rw [← NatTrans.naturality]; rw [← NatTrans.naturality]
  have E : (Sheaf.toImage f).hom.app (op V) y = (Sheaf.image f).obj.map i.op ⟨s, hx⟩ :=
    Subtype.ext e'
  have := congr_arg (fun f : F ⟶ G' => f.hom.app _ y) e
  simp only [ObjectProperty.FullSubcategory.comp_hom, Sheaf.toImage_hom,
    NatTrans.comp_app, comp_apply, op_unop] at this E ⊢
  convert this <;> exact E.symm

/--
Definition of `imageMonoFactorization` / `imageMonoFactorization` 的定义

English:
definition imageMonoFactorization
  signature: {F F' : Sheaf J (Type w)} (f : F ⟶ F')
  body: Sheaf.image f
  m := Sheaf.imageι f
  e := Sheaf.toImage f

中文:
定义 imageMonoFactorization
  签名: {F F' : 层 J (类型 w)} (f : F ⟶ F')
  定义体: Sheaf.image f
  m := Sheaf.imageι f
  e := Sheaf.toImage f

Depends on / 依赖: Sheaf.image
-/
def imageMonoFactorization {F F' : Sheaf J (Type w)} (f : F ⟶ F') :
    Limits.MonoFactorisation f where
  I := Sheaf.image f
  m := Sheaf.imageι f
  e := Sheaf.toImage f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `imageFactorization` / `imageFactorization` 的定义

English:
definition imageFactorization
  signature: {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F')
  body: imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J (Type (max v u)) _).mp I.m_mono
        refine ⟨Subfunctor.homOfLe ?_ ≫ inv (Subfunctor.toRange I.m.1)⟩
        apply Subfunctor.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply Subfunctor.range_comp_le
        · rw [← isSheaf_iff_isSheaf_of_type]
          exact F'.2
        · apply Presieve.isSheaf_iso J (asIso <| Subfunctor.toRange I.m.1)
          rw [← isSheaf_iff_isSheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [imageMonoFactorization]
        generalize_proofs h
        rw [← Subfunctor.homOfLe_ι h]; rw [Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq]; rw [Subfunctor.toRange_ι] }

中文:
定义 imageFactorization
  签名: {F F' : 层 J (类型 (最大值 v u))} (f : F ⟶ F')
  定义体: imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J (Type (max v u)) _).mp I.m_mono
        refine ⟨Subfunctor.homOfLe ?_ ≫ inv (Subfunctor.toRange I.m.1)⟩
        apply Subfunctor.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply Subfunctor.range_comp_le
        · rw [← isSheaf_iff_isSheaf_of_type]
          exact F'.2
        · apply Presieve.isSheaf_iso J (asIso <| Subfunctor.toRange I.m.1)
          rw [← isSheaf_iff_isSheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [imageMonoFactorization]
        generalize_proofs h
        rw [← Subfunctor.homOfLe_ι h]; rw [Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq]; rw [Subfunctor.toRange_ι] }

Depends on / 依赖: imageMonoFactorization
-/
noncomputable def imageFactorization {F F' : Sheaf J (Type (max v u))} (f : F ⟶ F') :
    Limits.ImageFactorisation f where
  F := imageMonoFactorization f
  isImage :=
    { lift := fun I => by
        haveI M := (Sheaf.Hom.mono_iff_presheaf_mono J (Type (max v u)) _).mp I.m_mono
        refine ⟨Subfunctor.homOfLe ?_ ≫ inv (Subfunctor.toRange I.m.1)⟩
        apply Subfunctor.sheafify_le
        · conv_lhs => rw [← I.fac]
          apply Subfunctor.range_comp_le
        · rw [← isSheaf_iff_isSheaf_of_type]
          exact F'.2
        · apply Presieve.isSheaf_iso J (asIso <| Subfunctor.toRange I.m.1)
          rw [← isSheaf_iff_isSheaf_of_type]
          exact I.I.2
      lift_fac := fun I => by
        ext1
        dsimp [imageMonoFactorization]
        generalize_proofs h
        rw [← Subfunctor.homOfLe_ι h]; rw [Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq]; rw [Subfunctor.toRange_ι] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasImages (Sheaf J (Type max v u))
  body: ⟨fun f => ⟨⟨imageFactorization f⟩⟩⟩

中文:
实例 :
  签名: Limits.有Images (层 J (类型 最大值 v u))
  定义体: ⟨fun f => ⟨⟨imageFactorization f⟩⟩⟩

Depends on / 依赖: imageFactorization
-/
instance : Limits.HasImages (Sheaf J (Type max v u)) :=
  ⟨fun f => ⟨⟨imageFactorization f⟩⟩⟩

end Image

end CategoryTheory
