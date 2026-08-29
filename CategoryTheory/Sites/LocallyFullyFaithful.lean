/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Locally fully faithful functors into sites

## Main results

- `CategoryTheory.Functor.IsLocallyFull`:
  A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every
  `f : G.obj U ⟶ G.obj V`, the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
  in the image of `G` is a coverage of the topology on `D`.
- `CategoryTheory.Functor.IsLocallyFaithful`:
  A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
  whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
  `gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.

## References

* [caramello2020]: Olivia Caramello, *Denseness conditions, morphisms and equivalences of toposes*

-/

@[expose] public section

universe w vC vD uC uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/--
Definition of `Functor.imageSieve` / `Functor.imageSieve` 的定义

English:
definition Functor.imageSieve
  signature: {U V : C} (f : G.obj U ⟶ G.obj V)
  body: exists l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]

中文:
定义 Functor.imageSieve
  签名: {U V : C} (f : G.obj U ⟶ G.obj V)
  定义体: exists l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]

Depends on / 依赖: G.map
-/
def Functor.imageSieve {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows _ i := exists l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]
/--
lemma `Functor.imageSieve_map` / 引理 `Functor.imageSieve_map`

English:
lemma Functor.imageSieve_map
  given: {U V : C} (f : U ⟶ V)
  statement: G.imageSieve (G.map f) = ⊤
  proof: by
  ext W g; simpa using ⟨g ≫ f, by simp⟩

中文:
引理 Functor.imageSieve_map
  条件: {U V : C} (f : U ⟶ V)
  结论: G.imageSieve (G.map f) = ⊤
  证明: by
  ext W g; simpa using ⟨g ≫ f, by simp⟩
-/
lemma Functor.imageSieve_map {U V : C} (f : U ⟶ V) : G.imageSieve (G.map f) = ⊤ := by
  ext W g; simpa using ⟨g ≫ f, by simp⟩

/--
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms a sieve.
-/
@[simps]
/--
Definition of `Sieve.equalizer` / `Sieve.equalizer` 的定义

English:
definition Sieve.equalizer
  signature: {U V : C} (f₁ f₂ : U ⟶ V)
  body: i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]

中文:
定义 Sieve.equalizer
  签名: {U V : C} (f₁ f₂ : U ⟶ V)
  定义体: i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
-/
def Sieve.equalizer {U V : C} (f₁ f₂ : U ⟶ V) : Sieve U where
  arrows _ i := i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
/--
lemma `Sieve.equalizer_self` / 引理 `Sieve.equalizer_self`

English:
lemma Sieve.equalizer_self
  given: {U V : C} (f : U ⟶ V)
  statement: equalizer f f = ⊤
  proof: by ext; simp

中文:
引理 Sieve.equalizer_self
  条件: {U V : C} (f : U ⟶ V)
  结论: equalizer f f = ⊤
  证明: by ext; simp
-/
lemma Sieve.equalizer_self {U V : C} (f : U ⟶ V) : equalizer f f = ⊤ := by ext; simp

/--
lemma `Sieve.equalizer_eq_equalizerSieve` / 引理 `Sieve.equalizer_eq_equalizerSieve`

English:
lemma Sieve.equalizer_eq_equalizerSieve
  given: {U V : C} (f₁ f₂ : U ⟶ V)
  proof: rfl

中文:
引理 Sieve.equalizer_eq_equalizerSieve
  条件: {U V : C} (f₁ f₂ : U ⟶ V)
  证明: rfl

Depends on / 依赖: yoneda, yoneda.obj
-/
lemma Sieve.equalizer_eq_equalizerSieve {U V : C} (f₁ f₂ : U ⟶ V) :
    Sieve.equalizer f₁ f₂ = Presheaf.equalizerSieve (F := yoneda.obj _) f₁ f₂ := rfl

/--
lemma `Functor.imageSieve_eq_imageSieve` / 引理 `Functor.imageSieve_eq_imageSieve`

English:
lemma Functor.imageSieve_eq_imageSieve
  statement: {D : Type uD} [Category.{vC} D] (G : C ⥤ D) {U V : C}
  proof: rfl

中文:
引理 Functor.imageSieve_eq_imageSieve
  结论: {D : 类型uD} [Category.{vC} D] (G : C ⥤ D) {U V : C}
  证明: rfl
-/
lemma Functor.imageSieve_eq_imageSieve {D : Type uD} [Category.{vC} D] (G : C ⥤ D) {U V : C}
    (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f = Presheaf.imageSieve (yonedaMap G V) f := rfl

open Presieve Opposite

namespace Functor

/--
Definition of `IsLocallyFull` / `IsLocallyFull` 的定义

English:
class IsLocallyFull
  parameters: : Prop where
  axioms and operations (1):
    - functorPushforward_imageSieve_mem : forall {U V} (f : G.obj U ⟶ G.obj V), (G.imageSieve f).functorPushforward G in K _

中文:
类 IsLocallyFull
  参数: : 命题 where
  公理与运算 (1 个):
    - functorPushforward_imageSieve_mem : 对任意 {U V} (f : G.obj U ⟶ G.obj V), (G.imageSieve f).functorPushforward G in K _
-/
class IsLocallyFull : Prop where
  functorPushforward_imageSieve_mem : forall {U V} (f : G.obj U ⟶ G.obj V),
    (G.imageSieve f).functorPushforward G in K _

/--
Definition of `IsLocallyFaithful` / `IsLocallyFaithful` 的定义

English:
class IsLocallyFaithful
  parameters: : Prop where
  axioms and operations (1):
    - functorPushforward_equalizer_mem : forall {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ -> (Sieve.equalizer f₁ f₂).functorPushforward G in K _

中文:
类 IsLocallyFaithful
  参数: : 命题 where
  公理与运算 (1 个):
    - functorPushforward_equalizer_mem : 对任意 {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ -> (Sieve.equalizer f₁ f₂).functorPushforward G in K _
-/
class IsLocallyFaithful : Prop where
  functorPushforward_equalizer_mem : forall {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ ->
    (Sieve.equalizer f₁ f₂).functorPushforward G in K _

/--
lemma `functorPushforward_imageSieve_mem` / 引理 `functorPushforward_imageSieve_mem`

English:
lemma functorPushforward_imageSieve_mem
  given: [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V)
  proof: Functor.IsLocallyFull.functorPushforward_imageSieve_mem _

中文:
引理 functorPushforward_imageSieve_mem
  条件: [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V)
  证明: Functor.IsLocallyFull.functorPushforward_imageSieve_mem _

Depends on / 依赖: Functor, Functor.IsLocallyFull.functorPushforward_imageSieve_mem, IsLocallyFull, functorPushforward_imageSieve_mem
-/
lemma functorPushforward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) :
    (G.imageSieve f).functorPushforward G in K _ :=
  Functor.IsLocallyFull.functorPushforward_imageSieve_mem _

/--
lemma `functorPushforward_equalizer_mem` / 引理 `functorPushforward_equalizer_mem`

English:
lemma functorPushforward_equalizer_mem
  proof: Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

中文:
引理 functorPushforward_equalizer_mem
  证明: Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

Depends on / 依赖: Functor, Functor.IsLocallyFaithful.functorPushforward_equalizer_mem, IsLocallyFaithful, functorPushforward_equalizer_mem
-/
lemma functorPushforward_equalizer_mem
    [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
      (Sieve.equalizer f₁ f₂).functorPushforward G in K _ :=
  Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

variable {K}
variable {A : Type*} [Category* A] (G : C ⥤ D)

/--
theorem `IsLocallyFull.ext` / 定理 `IsLocallyFull.ext`

English:
theorem IsLocallyFull.ext
  statement: [G.IsLocallyFull K]
  proof: by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_imageSieve_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

中文:
定理 IsLocallyFull.ext
  结论: [G.IsLocallyFull K]
  证明: by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_imageSieve_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

Depends on / 依赖: G.functorPushforward_imageSieve_mem, functorPushforward_imageSieve_mem, isSeparatedFor, isSeparatedFor.ext, isSheaf_iff_isSheaf_of_type, property
-/
theorem IsLocallyFull.ext [G.IsLocallyFull K]
    (ℱ : Sheaf K Type*) {X Y : C} (i : G.obj X ⟶ G.obj Y)
    {s t : ℱ.obj.obj (op (G.obj X))}
    (h : forall ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y), G.map f = G.map j ≫ i ->
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_imageSieve_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

/--
theorem `IsLocallyFaithful.ext` / 定理 `IsLocallyFaithful.ext`

English:
theorem IsLocallyFaithful.ext
  statement: [G.IsLocallyFaithful K] (ℱ : Sheaf K Type*)
  proof: by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

中文:
定理 IsLocallyFaithful.ext
  结论: [G.IsLocallyFaithful K] (ℱ : Sheaf K 类型)
  证明: by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

Depends on / 依赖: G.functorPushforward_equalizer_mem, functorPushforward_equalizer_mem, isSeparatedFor, isSeparatedFor.ext, isSheaf_iff_isSheaf_of_type, property
-/
theorem IsLocallyFaithful.ext [G.IsLocallyFaithful K] (ℱ : Sheaf K Type*)
    {X Y : C} (i₁ i₂ : X ⟶ Y) (e : G.map i₁ = G.map i₂)
    {s t : ℱ.obj.obj (op (G.obj X))}
    (h : forall ⦃Z : C⦄ (j : Z ⟶ X), j ≫ i₁ = j ≫ i₂ ->
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

instance (priority := 900) IsLocallyFull.of_full [G.Full] : G.IsLocallyFull K where
  functorPushforward_imageSieve_mem f := by
    rw [← G.map_preimage f]
    simp only [Functor.imageSieve_map, Sieve.functorPushforward_top, GrothendieckTopology.top_mem]

instance (priority := 900) IsLocallyFaithful.of_faithful [G.Faithful] : G.IsLocallyFaithful K where
  functorPushforward_equalizer_mem f₁ f₂ e := by obtain rfl := G.map_injective e; simp

end CategoryTheory.Functor
