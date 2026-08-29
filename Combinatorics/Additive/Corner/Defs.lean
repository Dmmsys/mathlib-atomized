/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# Corners

This file defines corners, namely triples of the form `(x, y), (x, y + d), (x + d, y)`, and the
property of being corner-free.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Set

variable {G H : Type*}

section AddCommMonoid
variable [AddCommMonoid G] [AddCommMonoid H] {A B : Set (G × G)} {s : Set G} {t : Set H} {f : G -> H}
  {x₁ y₁ x₂ y₂ : G}

/-- A **corner** of a set `A` in an abelian group is a triple of points of the form
`(x, y), (x + d, y), (x, y + d)`. It is **nontrivial** if `d ≠ 0`.

Here we define it as triples `(x₁, y₁), (x₂, y₁), (x₁, y₂)` where `x₁ + y₂ = x₂ + y₁` in order for
the definition to make sense in commutative monoids, the motivating example being `ℕ`. -/
@[mk_iff]
/--
Definition of `IsCorner` / `IsCorner` 的定义

English:
structure IsCorner
  parameters: (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G)
  axioms and operations (4):
    - fst_fst_mem : (x₁, y₁) in A
    - fst_snd_mem : (x₁, y₂) in A
    - snd_fst_mem : (x₂, y₁) in A
    - add_eq_add : x₁ + y₂ = x₂ + y₁

中文:
结构 是余rner
  参数: (A : 集合 (G × G)) (x₁ y₁ x₂ y₂ : G)
  公理与运算 (4 个):
    - fst_fst_mem : (x₁, y₁) in A
    - fst_snd_mem : (x₁, y₂) in A
    - snd_fst_mem : (x₂, y₁) in A
    - add_eq_add : x₁ + y₂ = x₂ + y₁
-/
structure IsCorner (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G) : Prop where
  fst_fst_mem : (x₁, y₁) in A
  fst_snd_mem : (x₁, y₂) in A
  snd_fst_mem : (x₂, y₁) in A
  add_eq_add : x₁ + y₂ = x₂ + y₁

/--
Definition of `IsCornerFree` / `IsCornerFree` 的定义

English:
definition IsCornerFree
  signature: (A : Set (G × G))
  body: forall ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ -> x₁ = x₂

中文:
定义 IsCornerFree
  签名: (A : 集合 (G × G))
  定义体: forall ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ -> x₁ = x₂

Depends on / 依赖: IsCorner
-/
def IsCornerFree (A : Set (G × G)) : Prop := forall ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ -> x₁ = x₂

/--
lemma `isCornerFree_iff` / 引理 `isCornerFree_iff`

English:
lemma isCornerFree_iff
  given: (hAs : A subseteq s ×ˢ s)
  proof: hA hxy
  mpr hA _x₁ _y₁ _x₂ _y₂ hxy := hA (hAs hxy.fst_fst_mem).1 (hAs hxy.fst_fst_mem).2
    (hAs hxy.snd_fst_mem).1 (hAs hxy.fst_snd_mem).2 hxy

中文:
引理 isCornerFree_iff
  条件: (hAs : A subseteq s ×ˢ s)
  证明: hA hxy
  mpr hA _x₁ _y₁ _x₂ _y₂ hxy := hA (hAs hxy.fst_fst_mem).1 (hAs hxy.fst_fst_mem).2
    (hAs hxy.snd_fst_mem).1 (hAs hxy.fst_snd_mem).2 hxy
-/
lemma isCornerFree_iff (hAs : A subseteq s ×ˢ s) :
    IsCornerFree A ↔ forall ⦃x₁⦄, x₁ in s -> forall ⦃y₁⦄, y₁ in s -> forall ⦃x₂⦄, x₂ in s -> forall ⦃y₂⦄, y₂ in s ->
      IsCorner A x₁ y₁ x₂ y₂ -> x₁ = x₂ where
  mp hA _x₁ _ _y₁ _ _x₂ _ _y₂ _ hxy := hA hxy
  mpr hA _x₁ _y₁ _x₂ _y₂ hxy := hA (hAs hxy.fst_fst_mem).1 (hAs hxy.fst_fst_mem).2
    (hAs hxy.snd_fst_mem).1 (hAs hxy.fst_snd_mem).2 hxy

/--
lemma `IsCorner.mono` / 引理 `IsCorner.mono`

English:
lemma IsCorner.mono
  given: (hAB : A subseteq B) (hA : IsCorner A x₁ y₁ x₂ y₂)
  statement: IsCorner B x₁ y₁ x₂ y₂ where
  proof: hAB hA.fst_fst_mem
  fst_snd_mem := hAB hA.fst_snd_mem
  snd_fst_mem := hAB hA.snd_fst_mem
  add_eq_add := hA.add_eq_add

中文:
引理 是余rner.mono
  条件: (hAB : A subseteq B) (hA : 是余rner A x₁ y₁ x₂ y₂)
  结论: 是余rner B x₁ y₁ x₂ y₂ where
  证明: hAB hA.fst_fst_mem
  fst_snd_mem := hAB hA.fst_snd_mem
  snd_fst_mem := hAB hA.snd_fst_mem
  add_eq_add := hA.add_eq_add

Depends on / 依赖: fst_fst_mem, hA.fst_fst_mem
-/
lemma IsCorner.mono (hAB : A subseteq B) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner B x₁ y₁ x₂ y₂ where
  fst_fst_mem := hAB hA.fst_fst_mem
  fst_snd_mem := hAB hA.fst_snd_mem
  snd_fst_mem := hAB hA.snd_fst_mem
  add_eq_add := hA.add_eq_add

/--
lemma `IsCornerFree.mono` / 引理 `IsCornerFree.mono`

English:
lemma IsCornerFree.mono
  given: (hAB : A subseteq B) (hB : IsCornerFree B)
  statement: IsCornerFree A
  proof: fun _x₁ _y₁ _x₂ _y₂ hxyd => hB hxyd.mono hAB

中文:
引理 IsCornerFree.mono
  条件: (hAB : A subseteq B) (hB : IsCornerFree B)
  结论: IsCornerFree A
  证明: fun _x₁ _y₁ _x₂ _y₂ hxyd => hB hxyd.mono hAB

Depends on / 依赖: hxyd.mono
-/
lemma IsCornerFree.mono (hAB : A subseteq B) (hB : IsCornerFree B) : IsCornerFree A :=
fun _x₁ _y₁ _x₂ _y₂ hxyd => hB hxyd.mono hAB

/--
lemma `not_isCorner_empty` / 引理 `not_isCorner_empty`

English:
lemma not_isCorner_empty
  statement: ¬ IsCorner ∅ x₁ y₁ x₂ y₂
  proof: by simp [isCorner_iff]

中文:
引理 not_isCorner_empty
  结论: ¬ 是余rner ∅ x₁ y₁ x₂ y₂
  证明: by simp [isCorner_iff]
-/
@[simp] lemma not_isCorner_empty : ¬ IsCorner ∅ x₁ y₁ x₂ y₂ := by simp [isCorner_iff]

/--
lemma `Set.Subsingleton.isCornerFree` / 引理 `Set.Subsingleton.isCornerFree`

English:
lemma Set.Subsingleton.isCornerFree
  given: (hA : A.Subsingleton)
  statement: IsCornerFree A
  proof: fun _x₁ _y₁ _x₂ _y₂ hxyd => by simpa using hA hxyd.fst_fst_mem hxyd.snd_fst_mem

中文:
引理 集合.子单例.isCornerFree
  条件: (hA : A.子单例)
  结论: IsCornerFree A
  证明: fun _x₁ _y₁ _x₂ _y₂ hxyd => by simpa using hA hxyd.fst_fst_mem hxyd.snd_fst_mem
-/
@[simp] lemma Set.Subsingleton.isCornerFree (hA : A.Subsingleton) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxyd => by simpa using hA hxyd.fst_fst_mem hxyd.snd_fst_mem

/--
lemma `isCornerFree_empty` / 引理 `isCornerFree_empty`

English:
lemma isCornerFree_empty
  statement: IsCornerFree (∅ : Set (G × G))
  proof: subsingleton_empty.isCornerFree

中文:
引理 isCornerFree_empty
  结论: IsCornerFree (∅ : 集合 (G × G))
  证明: subsingleton_empty.isCornerFree

Depends on / 依赖: isCornerFree, subsingleton_empty, subsingleton_empty.isCornerFree
-/
lemma isCornerFree_empty : IsCornerFree (∅ : Set (G × G)) := subsingleton_empty.isCornerFree
/--
lemma `isCornerFree_singleton` / 引理 `isCornerFree_singleton`

English:
lemma isCornerFree_singleton
  given: (x : G × G)
  statement: IsCornerFree {x}
  proof: subsingleton_singleton.isCornerFree

中文:
引理 isCornerFree_singleton
  条件: (x : G × G)
  结论: IsCornerFree {x}
  证明: subsingleton_singleton.isCornerFree

Depends on / 依赖: isCornerFree, subsingleton_singleton, subsingleton_singleton.isCornerFree
-/
lemma isCornerFree_singleton (x : G × G) : IsCornerFree {x} := subsingleton_singleton.isCornerFree

/--
lemma `IsCorner.image` / 引理 `IsCorner.image`

English:
lemma IsCorner.image
  statement: (hf : IsAddFreimanHom 2 s t f) (hAs : (A : Set (G × G)) subseteq s ×ˢ s)
  proof: by
  obtain ⟨hx₁y₁, hx₁y₂, hx₂y₁, hxy⟩ := hA
  exact ⟨mem_image_of_mem _ hx₁y₁, mem_image_of_mem _ hx₁y₂, mem_image_of_mem _ hx₂y₁,
    hf.add_eq_add (hAs hx₁y₁).1 (hAs hx₁y₂).2 (hAs hx₂y₁).1 (hAs hx₁y₁).2 hxy⟩

中文:
引理 是余rner.像
  结论: (hf : 是加法Freiman态射 2 s t f) (hAs : (A : 集合 (G × G)) subseteq s ×ˢ s)
  证明: by
  obtain ⟨hx₁y₁, hx₁y₂, hx₂y₁, hxy⟩ := hA
  exact ⟨mem_image_of_mem _ hx₁y₁, mem_image_of_mem _ hx₁y₂, mem_image_of_mem _ hx₂y₁,
    hf.add_eq_add (hAs hx₁y₁).1 (hAs hx₁y₂).2 (hAs hx₂y₁).1 (hAs hx₁y₁).2 hxy⟩

Depends on / 依赖: add_eq_add, hf.add_eq_add, mem_image_of_mem
-/
lemma IsCorner.image (hf : IsAddFreimanHom 2 s t f) (hAs : (A : Set (G × G)) subseteq s ×ˢ s)
    (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) := by
  obtain ⟨hx₁y₁, hx₁y₂, hx₂y₁, hxy⟩ := hA
  exact ⟨mem_image_of_mem _ hx₁y₁, mem_image_of_mem _ hx₁y₂, mem_image_of_mem _ hx₂y₁,
    hf.add_eq_add (hAs hx₁y₁).1 (hAs hx₁y₂).2 (hAs hx₂y₁).1 (hAs hx₁y₁).2 hxy⟩

/--
lemma `IsCornerFree.of_image` / 引理 `IsCornerFree.of_image`

English:
lemma IsCornerFree.of_image
  statement: (hf : IsAddFreimanHom 2 s t f) (hf' : s.InjOn f)
  proof: fun _x₁ _y₁ _x₂ _y₂ hxy =>
hf' (hAs hxy.fst_fst_mem).1 (hAs hxy.snd_fst_mem).1 hA hxy.image hf hAs

中文:
引理 IsCornerFree.of_image
  结论: (hf : 是加法Freiman态射 2 s t f) (hf' : s.单射限制 f)
  证明: fun _x₁ _y₁ _x₂ _y₂ hxy =>
hf' (hAs hxy.fst_fst_mem).1 (hAs hxy.snd_fst_mem).1 hA hxy.image hf hAs

Depends on / 依赖: fst_fst_mem, hxy.fst_fst_mem, hxy.image, hxy.snd_fst_mem, snd_fst_mem
-/
lemma IsCornerFree.of_image (hf : IsAddFreimanHom 2 s t f) (hf' : s.InjOn f)
    (hAs : (A : Set (G × G)) subseteq s ×ˢ s) (hA : IsCornerFree (Prod.map f f '' A)) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxy =>
hf' (hAs hxy.fst_fst_mem).1 (hAs hxy.snd_fst_mem).1 hA hxy.image hf hAs

/--
lemma `isCorner_image` / 引理 `isCorner_image`

English:
lemma isCorner_image
  statement: (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s)
  proof: by
  have hf' := hf.bijOn.injOn.prodMap hf.bijOn.injOn
  rw [isCorner_iff]; rw [isCorner_iff]
  congr!
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₁)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₂)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₂ hy₁)
  · exact hf.add_eq_add hx₁ hy₂ hx₂

中文:
引理 isCorner_image
  结论: (hf : 是加法FreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s)
  证明: by
  have hf' := hf.bijOn.injOn.prodMap hf.bijOn.injOn
  rw [isCorner_iff]; rw [isCorner_iff]
  congr!
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₁)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₂)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₂ hy₁)
  · exact hf.add_eq_add hx₁ hy₂ hx₂

Depends on / 依赖: add_eq_add, hf.add_eq_add, hf.bijOn.injOn, hf.bijOn.injOn.prodMap, isCorner_iff, mem_image_iff, mk_mem_prod, prodMap
-/
lemma isCorner_image (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s)
    (hx₁ : x₁ in s) (hy₁ : y₁ in s) (hx₂ : x₂ in s) (hy₂ : y₂ in s) :
    IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) ↔ IsCorner A x₁ y₁ x₂ y₂ := by
  have hf' := hf.bijOn.injOn.prodMap hf.bijOn.injOn
  rw [isCorner_iff]; rw [isCorner_iff]
  congr!
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₁)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₂)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₂ hy₁)
  · exact hf.add_eq_add hx₁ hy₂ hx₂ hy₁

/--
lemma `isCornerFree_image` / 引理 `isCornerFree_image`

English:
lemma isCornerFree_image
  given: (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s)
  proof: by
  have : Prod.map f f '' A subseteq t ×ˢ t :=
    ((hf.bijOn.mapsTo.prodMap hf.bijOn.mapsTo).mono hAs Subset.rfl).image_subset
  rw [isCornerFree_iff hAs]; rw [isCornerFree_iff this]
  simp +contextual only [hf.bijOn.forall, isCorner_image hf hAs, hf.bijOn.injOn.eq_iff]

alias ⟨IsCorner.of_image,

中文:
引理 isCornerFree_image
  条件: (hf : 是加法FreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s)
  证明: by
  have : Prod.map f f '' A subseteq t ×ˢ t :=
    ((hf.bijOn.mapsTo.prodMap hf.bijOn.mapsTo).mono hAs Subset.rfl).image_subset
  rw [isCornerFree_iff hAs]; rw [isCornerFree_iff this]
  simp +contextual only [hf.bijOn.forall, isCorner_image hf hAs, hf.bijOn.injOn.eq_iff]

alias ⟨IsCorner.of_image,

Depends on / 依赖: Prod.map, Subset, Subset.rfl, contextual, eq_iff, hf.bijOn.forall, hf.bijOn.injOn.eq_iff, hf.bijOn.mapsTo, hf.bijOn.mapsTo.prodMap, image_subset, isCornerFree_iff, isCorner_image, mapsTo, prodMap, subseteq
-/
lemma isCornerFree_image (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s) :
    IsCornerFree (Prod.map f f '' A) ↔ IsCornerFree A := by
  have : Prod.map f f '' A subseteq t ×ˢ t :=
    ((hf.bijOn.mapsTo.prodMap hf.bijOn.mapsTo).mono hAs Subset.rfl).image_subset
  rw [isCornerFree_iff hAs]; rw [isCornerFree_iff this]
  simp +contextual only [hf.bijOn.forall, isCorner_image hf hAs, hf.bijOn.injOn.eq_iff]

alias ⟨IsCorner.of_image, _⟩ := isCorner_image
alias ⟨_, IsCornerFree.image⟩ := isCornerFree_image

end AddCommMonoid
