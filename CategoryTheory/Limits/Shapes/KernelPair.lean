/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `IsLimit (PullbackCone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

@[expose] public section


universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/--
Definition of `IsKernelPair` / `IsKernelPair` 的定义

English:
abbreviation IsKernelPair
  body: IsPullback a b f f

中文:
缩写 IsKernelPair
  定义体: IsPullback a b f f

Depends on / 依赖: IsPullback
-/
abbrev IsKernelPair :=
  IsPullback a b f f

namespace IsKernelPair

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (IsKernelPair f a b)
  body: ⟨fun P Q => by constructor⟩

中文:
实例 :
  签名: 子单例 (IsKernelPair f a b)
  定义体: ⟨fun P Q => by constructor⟩
-/
instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by constructor⟩

/--
theorem `id_of_mono` / 定理 `id_of_mono`

English:
theorem id_of_mono
  given: [Mono f]
  statement: IsKernelPair f (𝟙 _) (𝟙 _)
  proof: ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

中文:
定理 id_of_mono
  条件: [单态射 f]
  结论: IsKernelPair f (𝟙 _) (𝟙 _)
  证明: ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

Depends on / 依赖: PullbackCone, PullbackCone.isLimitMkIdId, isLimitMkIdId
-/
theorem id_of_mono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨⟨rfl⟩, ⟨PullbackCone.isLimitMkIdId _⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _))
  body: ⟨id_of_mono f⟩

中文:
实例 [单态射
  签名: f] : 可居 (IsKernelPair f (𝟙 _) (𝟙 _))
  定义体: ⟨id_of_mono f⟩

Depends on / 依赖: id_of_mono
-/
instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨id_of_mono f⟩

variable {f a b}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  body: PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  定义体: PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift, isLimit, k.isLimit
-/
noncomputable def lift {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    S ⟶ R :=
  PullbackCone.IsLimit.lift k.isLimit _ _ w

@[reassoc (attr := simp)]
/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  given: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  proof: PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]

中文:
引理 lift_fst
  条件: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  证明: PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift_fst, lift_fst
-/
lemma lift_fst {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ a = p :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
/--
lemma `lift_snd` / 引理 `lift_snd`

English:
lemma lift_snd
  given: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  proof: PullbackCone.IsLimit.lift_snd _ _ _ _

中文:
引理 lift_snd
  条件: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  证明: PullbackCone.IsLimit.lift_snd _ _ _ _

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.lift_snd, lift_snd
-/
lemma lift_snd {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    k.lift p q w ≫ b = q :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  body: ⟨k.lift p q w, by simp⟩

中文:
定义 lift'
  签名: {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f)
  定义体: ⟨k.lift p q w, by simp⟩

Depends on / 依赖: k.lift
-/
noncomputable def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
    { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  ⟨k.lift p q w, by simp⟩

/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  statement: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
  proof: { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

中文:
定理 cancel_right
  结论: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
  证明: { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

Depends on / 依赖: PullbackCone, PullbackCone.isLimitAux, PullbackCone.mk, WalkingCospan, WalkingCospan.left, WalkingCospan.right, big_k, big_k.isLimit.fac, big_k.isLimit.hom_ext, big_k.isLimit.lift, condition_assoc, equalizer_ext, hom_ext, isLimit, isLimitAux, reassoc_of, s.condition_assoc, s.fst, s.snd
-/
theorem cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁)
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  { w := comm
    isLimit' :=
      ⟨PullbackCone.isLimitAux' _ fun s => by
        let s' : PullbackCone (f₁ ≫ f₂) (f₁ ≫ f₂) :=
          PullbackCone.mk s.fst s.snd (s.condition_assoc _)
        refine ⟨big_k.isLimit.lift s', big_k.isLimit.fac _ WalkingCospan.left,
          big_k.isLimit.fac _ WalkingCospan.right, fun m₁ m₂ => ?_⟩
        apply big_k.isLimit.hom_ext
        refine (PullbackCone.mk a b ?_ : PullbackCone (f₁ ≫ f₂) _).equalizer_ext ?_ ?_
        · apply reassoc_of% comm
        · apply m₁.trans (big_k.isLimit.fac s' WalkingCospan.left).symm
        · apply m₂.trans (big_k.isLimit.fac s' WalkingCospan.right).symm⟩ }

/--
theorem `cancel_right_of_mono` / 定理 `cancel_right_of_mono`

English:
theorem cancel_right_of_mono
  statement: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
  proof: cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

中文:
定理 cancel_right_of_mono
  结论: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [单态射 f₂]
  证明: cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

Depends on / 依赖: big_k, big_k.w, cancel_mono, cancel_right
-/
theorem cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂]
    (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancel_right (by rw [← cancel_mono f₂, assoc, assoc, big_k.w]) big_k

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_of_mono` / 定理 `comp_of_mono`

English:
theorem comp_of_mono
  given: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b)
  proof: { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

中文:
定理 comp_of_mono
  条件: {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [单态射 f₂] (small_k : IsKernelPair f₁ a b)
  证明: { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

Depends on / 依赖: PullbackCone, PullbackCone.equalizer_ext, PullbackCone.isLimitAux, WalkingCospan, WalkingCospan.left, WalkingCospan.right, cancel_mono, condition, equalizer_ext, hom_ext, isLimit, isLimitAux, s.condition, s.fst, s.snd, small_k, small_k.cone, small_k.isLimit.hom_ext, small_k.lift, small_k.w_assoc
-/
theorem comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) :
    IsKernelPair (f₁ ≫ f₂) a b :=
  { w := by rw [small_k.w_assoc]
    isLimit' := ⟨by
      refine PullbackCone.isLimitAux _
        (fun s => small_k.lift s.fst s.snd (by rw [← cancel_mono f₂, assoc, s.condition, assoc]))
        (by simp) (by simp) ?_
      intro s m hm
      apply small_k.isLimit.hom_ext
      apply PullbackCone.equalizer_ext small_k.cone _ _
      · exact (hm WalkingCospan.left).trans (by simp)
      · exact (hm WalkingCospan.right).trans (by simp)⟩ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toCoequalizer` / `toCoequalizer` 的定义

English:
definition toCoequalizer
  signature: (k : IsKernelPair f a b) (r : RegularEpi f)
  body: by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

中文:
定义 toCoequalizer
  签名: (k : IsKernelPair f a b) (r : 正则满态射 f)
  定义体: by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.IsColimit.desc, Cofork.IsColimit.hom_ext, Cofork.IsColimit.mk, IsColimit, PullbackCone, PullbackCone.mk, WalkingCospan, WalkingCospan.left, WalkingCospan.right, condition, hom_ext, isColimit, isLimit, k.isLimit.fac, k.isLimit.lift, r.isColimit, r.left, r.right
-/
noncomputable def toCoequalizer (k : IsKernelPair f a b) (r : RegularEpi f) :
    IsColimit (Cofork.ofπ f k.w) := by
  let t := k.isLimit.lift (PullbackCone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.isLimit.fac _ WalkingCospan.left
  have kt : t ≫ b = r.right := k.isLimit.fac _ WalkingCospan.right
  refine Cofork.IsColimit.mk _
    (fun s => Cofork.IsColimit.desc r.isColimit s.π
      (by rw [← ht, assoc, s.condition, reassoc_of% kt]))
    (fun s => ?_) (fun s m w => ?_)
  · apply Cofork.IsColimit.π_desc' r.isColimit
  · apply Cofork.IsColimit.hom_ext r.isColimit
    exact w.trans (Cofork.IsColimit.π_desc' r.isColimit _ _).symm

/--
Definition of `toCoequalizer'` / `toCoequalizer'` 的定义

English:
definition toCoequalizer'
  signature: (k : IsKernelPair f a b) [IsRegularEpi f]
  body: toCoequalizer k IsRegularEpi.getStruct f

中文:
定义 toCoequalizer'
  签名: (k : IsKernelPair f a b) [是正则满态射 f]
  定义体: toCoequalizer k IsRegularEpi.getStruct f

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct, toCoequalizer
-/
noncomputable def toCoequalizer' (k : IsKernelPair f a b) [IsRegularEpi f] :
    IsColimit (Cofork.ofπ f k.w) :=
toCoequalizer k IsRegularEpi.getStruct f

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback` / 定理 `pullback`

English:
theorem pullback
  statement: {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
  proof: by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s (m : _ ⟶ pullback f (a₁ ≫ g)) hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · apply pullback.hom_ext
    · simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

中文:
定理 pullback
  结论: {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
  证明: by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s (m : _ ⟶ pullback f (a₁ ≫ g)) hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · apply pullback.hom_ext
    · simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g
-/
protected theorem pullback {X Y Z A : C} {g : Y ⟶ Z} {a₁ a₂ : A ⟶ Y} (h : IsKernelPair g a₁ a₂)
    (f : X ⟶ Z) [HasPullback f g] [HasPullback f (a₁ ≫ g)] :
    IsKernelPair (pullback.fst f g)
      (pullback.map f _ f _ (𝟙 X) a₁ (𝟙 Z) (by simp) <| Category.comp_id _)
      (pullback.map _ _ _ _ (𝟙 X) a₂ (𝟙 Z) (by simp) <| (Category.comp_id _).trans h.1.1) := by
  refine ⟨⟨by rw [pullback.lift_fst, pullback.lift_fst]⟩, ⟨PullbackCone.isLimitAux _
    (fun s => pullback.lift (s.fst ≫ pullback.fst _ _)
      (h.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_ ) ?_) (fun s => ?_)
        (fun s => ?_) (fun s (m : _ ⟶ pullback f (a₁ ≫ g)) hm => ?_)⟩⟩
  · simp_rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
  · simp only [assoc, lift_fst_assoc, pullback.condition]
  · ext <;> simp
  · ext
    · simp [s.condition]
    · simp
  · apply pullback.hom_ext
    · simpa using hm WalkingCospan.left =≫ pullback.fst f g
    · apply PullbackCone.IsLimit.hom_ext h.isLimit
      · simpa using hm WalkingCospan.left =≫ pullback.snd f g
      · simpa using hm WalkingCospan.right =≫ pullback.snd f g

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_of_isIso_fst` / 定理 `mono_of_isIso_fst`

English:
theorem mono_of_isIso_fst
  given: (h : IsKernelPair f a b) [IsIso a]
  statement: Mono f
  proof: by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp)
  rw [IsPullback.cone_fst]; rw [← IsIso.eq_comp_inv]; rw [Category.id_comp] at h₁
  rw [h₁]; rw [IsIso.inv_comp_eq]; rw [Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst]; rw [h₂]

中文:
定理 mono_of_isIso_fst
  条件: (h : IsKernelPair f a b) [是同构 a]
  结论: 单态射 f
  证明: by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp)
  rw [IsPullback.cone_fst]; rw [← IsIso.eq_comp_inv]; rw [Category.id_comp] at h₁
  rw [h₁]; rw [IsIso.inv_comp_eq]; rw [Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst]; rw [h₂]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, IsIso.eq_comp_inv, IsIso.inv_comp_eq, IsLimit, IsPullback, IsPullback.cone_fst, Limits, Limits.PullbackCone.IsLimit.lift, PullbackCone, comp_id, cone_fst, eq_comp_inv, h.isLimit, id_comp, inv_comp_eq, isLimit
-/
theorem mono_of_isIso_fst (h : IsKernelPair f a b) [IsIso a] : Mono f := by
  obtain ⟨l, h₁, h₂⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit (𝟙 _) (𝟙 _) (by simp)
  rw [IsPullback.cone_fst]; rw [← IsIso.eq_comp_inv]; rw [Category.id_comp] at h₁
  rw [h₁]; rw [IsIso.inv_comp_eq]; rw [Category.comp_id] at h₂
  constructor
  intro Z g₁ g₂ e
  obtain ⟨l', rfl, rfl⟩ := Limits.PullbackCone.IsLimit.lift' h.isLimit _ _ e
  rw [IsPullback.cone_fst]; rw [h₂]

/--
theorem `mono_of_eq_fst_snd'` / 定理 `mono_of_eq_fst_snd'`

English:
theorem mono_of_eq_fst_snd'
  given: (h : IsKernelPair f a a)
  statement: Mono f
  proof: ⟨fun g₁ g₂ e => (lift_fst h g₁ g₂ e).symm.trans lift_snd h g₁ g₂ e⟩

中文:
定理 mono_of_eq_fst_snd'
  条件: (h : IsKernelPair f a a)
  结论: 单态射 f
  证明: ⟨fun g₁ g₂ e => (lift_fst h g₁ g₂ e).symm.trans lift_snd h g₁ g₂ e⟩

Depends on / 依赖: lift_fst, lift_snd, symm.trans
-/
theorem mono_of_eq_fst_snd' (h : IsKernelPair f a a) : Mono f :=
⟨fun g₁ g₂ e => (lift_fst h g₁ g₂ e).symm.trans lift_snd h g₁ g₂ e⟩

/--
theorem `mono_of_eq_fst_snd` / 定理 `mono_of_eq_fst_snd`

English:
theorem mono_of_eq_fst_snd
  given: (h : IsKernelPair f a b) (e : a = b)
  statement: Mono f
  proof: by
  induction e; exact h.mono_of_eq_fst_snd'

中文:
定理 mono_of_eq_fst_snd
  条件: (h : IsKernelPair f a b) (e : a = b)
  结论: 单态射 f
  证明: by
  induction e; exact h.mono_of_eq_fst_snd'

Depends on / 依赖: h.mono_of_eq_fst_snd, mono_of_eq_fst_snd
-/
theorem mono_of_eq_fst_snd (h : IsKernelPair f a b) (e : a = b) : Mono f := by
  induction e; exact h.mono_of_eq_fst_snd'

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isIso_of_mono` / 定理 `isIso_of_mono`

English:
theorem isIso_of_mono
  given: (h : IsKernelPair f a b) [Mono f]
  statement: IsIso a
  proof: by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

中文:
定理 isIso_of_mono
  条件: (h : IsKernelPair f a b) [单态射 f]
  结论: 是同构 a
  证明: by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

Depends on / 依赖: Category, Category.comp_id, IsKernelPair, IsKernelPair.id_of_mono, WalkingCospan, WalkingCospan.left, comp_id, conePointUniqueUpToIso_inv_comp, h.isLimit, id_of_mono, infer_instance, isLimit, isLimit.conePointUniqueUpToIso_inv_comp, symm.trans
-/
theorem isIso_of_mono (h : IsKernelPair f a b) [Mono f] : IsIso a := by
  rw [←
    show _ = a from
      (Category.comp_id _).symm.trans
        ((IsKernelPair.id_of_mono f).isLimit.conePointUniqueUpToIso_inv_comp h.isLimit
          WalkingCospan.left)]
  infer_instance

/--
theorem `of_isIso_of_mono` / 定理 `of_isIso_of_mono`

English:
theorem of_isIso_of_mono
  given: [IsIso a] [Mono f]
  statement: IsKernelPair f a a
  proof: by
  change IsPullback _ _ _ _
  convert! (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _)⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

中文:
定理 of_isIso_of_mono
  条件: [是同构 a] [单态射 f]
  结论: IsKernelPair f a a
  证明: by
  change IsPullback _ _ _ _
  convert! (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _)⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

Depends on / 依赖: IsKernelPair, IsKernelPair.id_of_mono, IsPullback, IsPullback.of_horiz_isIso, all_goals, convert, id_of_mono, of_horiz_isIso, paste_vert
-/
theorem of_isIso_of_mono [IsIso a] [Mono f] : IsKernelPair f a a := by
  change IsPullback _ _ _ _
  convert! (IsPullback.of_horiz_isIso ⟨(rfl : a ≫ 𝟙 X = _)⟩).paste_vert (IsKernelPair.id_of_mono f)
  all_goals { simp }

/--
theorem `of_hasPullback` / 定理 `of_hasPullback`

English:
theorem of_hasPullback
  given: (f : X ⟶ Y) [HasPullback f f]
  proof: IsPullback.of_hasPullback f f

中文:
定理 of_hasPullback
  条件: (f : X ⟶ Y) [HasPullback f f]
  证明: IsPullback.of_hasPullback f f

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, of_hasPullback
-/
theorem of_hasPullback (f : X ⟶ Y) [HasPullback f f] :
    IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end IsKernelPair

/--
lemma `IsRegularEpi.exists_of_isKernelPair` / 引理 `IsRegularEpi.exists_of_isKernelPair`

English:
lemma IsRegularEpi.exists_of_isKernelPair
  statement: {X Y : C} (π : X ⟶ Y) [IsRegularEpi π] {Z : C}
  proof: ⟨h.toCoequalizer'.desc (Cofork.ofπ f w), Cofork.IsColimit.π_desc h.toCoequalizer'⟩

中文:
引理 是正则满态射.存在_of_isKernelPair
  结论: {X Y : C} (π : X ⟶ Y) [是正则满态射 π] {Z : C}
  证明: ⟨h.toCoequalizer'.desc (Cofork.ofπ f w), Cofork.IsColimit.π_desc h.toCoequalizer'⟩

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.of, IsColimit, h.toCoequalizer, toCoequalizer
-/
lemma IsRegularEpi.exists_of_isKernelPair {X Y : C} (π : X ⟶ Y) [IsRegularEpi π] {Z : C}
    {fst snd : Z ⟶ X} (h : IsKernelPair π fst snd) {W : C} (f : X ⟶ W) (w : fst ≫ f = snd ≫ f) :
    exists (g : Y ⟶ W), π ≫ g = f :=
  ⟨h.toCoequalizer'.desc (Cofork.ofπ f w), Cofork.IsColimit.π_desc h.toCoequalizer'⟩

end CategoryTheory
