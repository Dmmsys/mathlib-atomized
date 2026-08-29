/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Locality conditions on morphism properties

In this file we define locality conditions on morphism properties in a category. Let `K` be a
precoverage in a category `C` and `P` be a morphism property on `C` that respects isomorphisms.

We say that

- `P` is local at the target if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `Y`.
- `P` is local at the source if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a `K`-cover `{Uᵢ}` of `X`.

## TODOs

- Define source and target local closure of a morphism property.
-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (K : Precoverage C)

/--
Definition of `IsLocalAtTarget` / `IsLocalAtTarget` 的定义

English:
class IsLocalAtTarget
  parameters: (P : MorphismProperty C) (K : Precoverage C)
  extends: RespectsIso P
  axioms and operations (2):
    - pullbackSnd({X Y : C} {f : Y ⟶ X} {R : Presieve X} {U : C} {g : U ⟶ X} (hR : R in K X) (hg : R g) (hf : P f) [HasPullback f g]) : P (pullback.snd f g)
    - of_forall_pullbackSnd({X Y : C} {f : Y ⟶ X} {R : Presieve X} (hR : R in K X) (h : forall {U : C} {g : U ⟶ X} [HasPullback f g], R g -> P (pullback.snd f g))) : P f

中文:
类 IsLocalAtTarget
  参数: (P : Morphism命题erty C) (K : Precoverage C)
  继承: RespectsIso P
  公理与运算 (2 个):
    - pullbackSnd({X Y : C} {f : Y ⟶ X} {R : Presieve X} {U : C} {g : U ⟶ X} (hR : R in K X) (hg : R g) (hf : P f) [HasPullback f g]) : P (pullback.snd f g)
    - of_forall_pullbackSnd({X Y : C} {f : Y ⟶ X} {R : Presieve X} (hR : R in K X) (h : 对任意 {U : C} {g : U ⟶ X} [HasPullback f g], R g -> P (pullback.snd f g))) : P f
-/
class IsLocalAtTarget (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `f` restricted to `Uᵢ` for any
  `K`-cover `R` of `Y`. -/
  pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} {U : C} {g : U ⟶ X} (hR : R in K X)
    (hg : R g) (hf : P f) [HasPullback f g] :
    P (pullback.snd f g)
  /-- If `P` holds for `f` restricted to `Uᵢ` for all `i`, it also holds for `f : X ⟶ Y` for any
  `K`-cover `R` of `Y`. -/
  of_forall_pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hR : R in K X)
    (h : forall {U : C} {g : U ⟶ X} [HasPullback f g], R g -> P (pullback.snd f g)) :
    P f

namespace IsLocalAtTarget

variable {P : MorphismProperty C} {K L : Precoverage C}

/--
lemma `mk_of_iff` / 引理 `mk_of_iff`

English:
lemma mk_of_iff
  statement: [P.RespectsIso]
  proof: by grind
  of_forall_pullbackSnd := by grind

中文:
引理 mk_of_iff
  结论: [P.RespectsIso]
  证明: by grind
  of_forall_pullbackSnd := by grind

Depends on / 依赖: of_forall_pullbackSnd
-/
lemma mk_of_iff [P.RespectsIso]
    (H : forall ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve Y⦄, R in K Y ->
      (P f ↔ forall {U : C} (g : U ⟶ Y) [HasPullback f g], R g -> P (pullback.snd f g))) :
    P.IsLocalAtTarget K where
  pullbackSnd := by grind
  of_forall_pullbackSnd := by grind

/--
lemma `iff_of_forall_pullbackSnd` / 引理 `iff_of_forall_pullbackSnd`

English:
lemma iff_of_forall_pullbackSnd
  statement: [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y} (hR : R in K Y)
  proof: by
  grind [IsLocalAtTarget]

中文:
引理 iff_of_forall_pullbackSnd
  结论: [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y} (hR : R in K Y)
  证明: by
  grind [IsLocalAtTarget]

Depends on / 依赖: F.commShiftIso, F.mapZeroObject, F.map_distinguished, F.map_surjective, IsLocalAtTarget, T.mor, Triangle, commShiftIso, exists_zero, inv.app, isZero_zero, le_shift, mapIso, mapZeroObject, map_distinguished, map_surjective, shiftFunctor
-/
lemma iff_of_forall_pullbackSnd [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y} (hR : R in K Y)
    {f : X ⟶ Y} :
    P f ↔ forall {U : C} (g : U ⟶ Y) [HasPullback f g], R g -> P (pullback.snd f g) := by
  grind [IsLocalAtTarget]

/--
lemma `mk_of_iff_of_zeroHypercover` / 引理 `mk_of_iff_of_zeroHypercover`

English:
lemma mk_of_iff_of_zeroHypercover
  statement: [K.HasPullbacks] [P.RespectsIso]
  proof: by
  refine mk_of_iff fun X Y f R hR => ?_
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [H _ ⟨𝒰]; rw [hR⟩]
  have _ (i) : HasPullback (𝒰.f i) f := (Precoverage.hasPullbacks_of_mem _ hR).hasPullback ⟨i⟩
  refine ⟨fun h U g hfg => ?_, fun h i => h _ ⟨i⟩⟩
  rintro ⟨i⟩
  exact h i

中文:
引理 mk_of_iff_of_zeroHypercover
  结论: [K.HasPullbacks] [P.RespectsIso]
  证明: by
  refine mk_of_iff fun X Y f R hR => ?_
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [H _ ⟨𝒰]; rw [hR⟩]
  have _ (i) : HasPullback (𝒰.f i) f := (Precoverage.hasPullbacks_of_mem _ hR).hasPullback ⟨i⟩
  refine ⟨fun h U g hfg => ?_, fun h i => h _ ⟨i⟩⟩
  rintro ⟨i⟩
  exact h i

Depends on / 依赖: HasPullback, Precoverage, Precoverage.hasPullbacks_of_mem, R.exists_eq_preZeroHypercover, exists_eq_preZeroHypercover, hasPullback, hasPullbacks_of_mem, mk_of_iff
-/
lemma mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso]
    (H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      P f ↔ forall i, P (pullback.snd f (𝒰.f i))) :
    P.IsLocalAtTarget K := by
  refine mk_of_iff fun X Y f R hR => ?_
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [H _ ⟨𝒰]; rw [hR⟩]
  have _ (i) : HasPullback (𝒰.f i) f := (Precoverage.hasPullbacks_of_mem _ hR).hasPullback ⟨i⟩
  refine ⟨fun h U g hfg => ?_, fun h i => h _ ⟨i⟩⟩
  rintro ⟨i⟩
  exact h i

/--
lemma `mk_of_small` / 引理 `mk_of_small`

English:
lemma mk_of_small
  statement: [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K]
  proof: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

中文:
引理 mk_of_small
  结论: [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K]
  证明: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

Depends on / 依赖: F.essImage_, infer_instance, mk_of_iff_of_zeroHypercover, restrictIndexOfSmall
-/
lemma mk_of_small [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
        P f -> forall i, P (pullback.snd f (𝒰.f i)))
    (h₂ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y),
        (forall i, P (pullback.snd f (𝒰.f i))) -> P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

/--
lemma `mk_of_isStableUnderBaseChange` / 引理 `mk_of_isStableUnderBaseChange`

English:
lemma mk_of_isStableUnderBaseChange
  statement: [K.HasPullbacks] [P.IsStableUnderBaseChange]
  proof: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => P.pullback_snd _ _ hf, fun h => H _ 𝒰 h⟩

中文:
引理 mk_of_isStableUnderBaseChange
  结论: [K.HasPullbacks] [P.IsStableUnderBaseChange]
  证明: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => P.pullback_snd _ _ hf, fun h => H _ 𝒰 h⟩

Depends on / 依赖: P.pullback_snd, mk_of_iff_of_zeroHypercover, pullback_snd
-/
lemma mk_of_isStableUnderBaseChange [K.HasPullbacks] [P.IsStableUnderBaseChange]
    (H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      (forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) -> P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => P.pullback_snd _ _ hf, fun h => H _ 𝒰 h⟩

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: [IsLocalAtTarget P L] (hle : K <= L)
  statement: IsLocalAtTarget P K where
  proof: pullbackSnd (hle _ h) i hf
  of_forall_pullbackSnd hR h := of_forall_pullbackSnd (hle _ hR) h

中文:
引理 of_le
  条件: [IsLocalAtTarget P L] (hle : K <= L)
  结论: IsLocalAtTarget P K where
  证明: pullbackSnd (hle _ h) i hf
  of_forall_pullbackSnd hR h := of_forall_pullbackSnd (hle _ hR) h

Depends on / 依赖: pullbackSnd
-/
lemma of_le [IsLocalAtTarget P L] (hle : K <= L) : IsLocalAtTarget P K where
  pullbackSnd h i hf := pullbackSnd (hle _ h) i hf
  of_forall_pullbackSnd hR h := of_forall_pullbackSnd (hle _ hR) h

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: : IsLocalAtTarget (⊤ : MorphismProperty C) K where
  body: by simp
  of_forall_pullbackSnd := by simp

中文:
实例 top
  签名: : IsLocalAtTarget (⊤ : Morphism命题erty C) K where
  定义体: by simp
  of_forall_pullbackSnd := by simp

Depends on / 依赖: of_forall_pullbackSnd
-/
instance top : IsLocalAtTarget (⊤ : MorphismProperty C) K where
  pullbackSnd := by simp
  of_forall_pullbackSnd := by simp

variable [IsLocalAtTarget P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)

/--
lemma `of_isPullback` / 引理 `of_isPullback`

English:
lemma of_isPullback
  statement: {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
  proof: by
  have : HasPullback f (𝒰.f i) := h.hasPullback
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact pullbackSnd 𝒰.mem₀ ⟨i⟩ hf

中文:
引理 of_isPullback
  结论: {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
  证明: by
  have : HasPullback f (𝒰.f i) := h.hasPullback
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact pullbackSnd 𝒰.mem₀ ⟨i⟩ hf

Depends on / 依赖: HasPullback, P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, h.hasPullback, h.isoPullback.inv, h.isoPullback_inv_snd, hasPullback, isoPullback, isoPullback_inv_snd, pullbackSnd
-/
lemma of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
    (h : IsPullback fst snd f (𝒰.f i)) (hf : P f) :
    P snd := by
  have : HasPullback f (𝒰.f i) := h.hasPullback
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact pullbackSnd 𝒰.mem₀ ⟨i⟩ hf

/--
lemma `of_zeroHypercover` / 引理 `of_zeroHypercover`

English:
lemma of_zeroHypercover
  given: [K.HasPullbacks] (h : forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i)))
  proof: of_forall_pullbackSnd 𝒰.mem₀ (by rintro _ _ _ ⟨i⟩; exact h _)

中文:
引理 of_zeroHypercover
  条件: [K.HasPullbacks] (h : 对任意 (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i)))
  证明: of_forall_pullbackSnd 𝒰.mem₀ (by rintro _ _ _ ⟨i⟩; exact h _)

Depends on / 依赖: of_forall_pullbackSnd
-/
lemma of_zeroHypercover [K.HasPullbacks] (h : forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) :
    P f :=
  of_forall_pullbackSnd 𝒰.mem₀ (by rintro _ _ _ ⟨i⟩; exact h _)

/--
lemma `iff_of_zeroHypercover` / 引理 `iff_of_zeroHypercover`

English:
lemma iff_of_zeroHypercover
  given: [K.HasPullbacks]
  statement: P f ↔ forall i, P (pullback.snd f (𝒰.f i))
  proof: ⟨fun hf _ => pullbackSnd 𝒰.mem₀ ⟨_⟩ hf, fun h => of_zeroHypercover _ h⟩

中文:
引理 iff_of_zeroHypercover
  条件: [K.HasPullbacks]
  结论: P f ↔ 对任意 i, P (pullback.snd f (𝒰.f i))
  证明: ⟨fun hf _ => pullbackSnd 𝒰.mem₀ ⟨_⟩ hf, fun h => of_zeroHypercover _ h⟩

Depends on / 依赖: of_zeroHypercover, pullbackSnd
-/
lemma iff_of_zeroHypercover [K.HasPullbacks] : P f ↔ forall i, P (pullback.snd f (𝒰.f i)) :=
  ⟨fun hf _ => pullbackSnd 𝒰.mem₀ ⟨_⟩ hf, fun h => of_zeroHypercover _ h⟩

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K]
  body: ⟨pullbackSnd hR i h.1, pullbackSnd hR i h.2⟩
  of_forall_pullbackSnd hR h :=
    ⟨of_forall_pullbackSnd hR fun i => (h i).1, of_forall_pullbackSnd hR fun i => (h i).2⟩

中文:
实例 inf
  签名: (P Q : Morphism命题erty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K]
  定义体: ⟨pullbackSnd hR i h.1, pullbackSnd hR i h.2⟩
  of_forall_pullbackSnd hR h :=
    ⟨of_forall_pullbackSnd hR fun i => (h i).1, of_forall_pullbackSnd hR fun i => (h i).2⟩

Depends on / 依赖: pullbackSnd
-/
instance inf (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K] :
    IsLocalAtTarget (P ⊓ Q) K where
  pullbackSnd hR i h := ⟨pullbackSnd hR i h.1, pullbackSnd hR i h.2⟩
  of_forall_pullbackSnd hR h :=
    ⟨of_forall_pullbackSnd hR fun i => (h i).1, of_forall_pullbackSnd hR fun i => (h i).2⟩

end IsLocalAtTarget

set_option backward.defeqAttrib.useBackward true in
/--
lemma `of_zeroHypercover_target` / 引理 `of_zeroHypercover_target`

English:
lemma of_zeroHypercover_target
  statement: {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks]
  proof: by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

中文:
引理 of_zeroHypercover_target
  结论: {P : Morphism命题erty C} {K : Precoverage C} [K.HasPullbacks]
  证明: by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

Depends on / 依赖: IsLocalAtTarget, IsLocalAtTarget.iff_of_zeroHypercover, iff_of_zeroHypercover, restrictIndexOfSmall
-/
lemma of_zeroHypercover_target {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks]
    [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : forall i, P (pullback.snd f (𝒰.f i))) :
    P f := by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

/--
Definition of `IsLocalAtSource` / `IsLocalAtSource` 的定义

English:
class IsLocalAtSource
  parameters: (P : MorphismProperty C) (K : Precoverage C)
  extends: RespectsIso P
  axioms and operations (2):
    - comp({X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X) {U : C} (g : U ⟶ X) (hg : R g) (hf : P f)) : P (g ≫ f)
    - of_forall_comp({X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X)) : (forall ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f)) -> P f

中文:
类 IsLocalAtSource
  参数: (P : Morphism命题erty C) (K : Precoverage C)
  继承: RespectsIso P
  公理与运算 (2 个):
    - comp({X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X) {U : C} (g : U ⟶ X) (hg : R g) (hf : P f)) : P (g ≫ f)
    - of_forall_comp({X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X)) : (对任意 ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f)) -> P f
-/
class IsLocalAtSource (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `𝒰.f i ≫ f` for any `K`-cover `R` of `X`. -/
  comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X) {U : C} (g : U ⟶ X) (hg : R g)
    (hf : P f) : P (g ≫ f)
  /-- If `P` holds for `𝒰.f i ≫ f` for all `i`, it holds for `f : X ⟶ Y` for any `K`-cover
  `R` of X. -/
  of_forall_comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R in K X) :
    (forall ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f)) -> P f

namespace IsLocalAtSource

variable {P : MorphismProperty C} {K L : Precoverage C}

/--
lemma `mk_of_iff` / 引理 `mk_of_iff`

English:
lemma mk_of_iff
  statement: [P.RespectsIso]
  proof: by grind
  of_forall_comp hR h := by grind

中文:
引理 mk_of_iff
  结论: [P.RespectsIso]
  证明: by grind
  of_forall_comp hR h := by grind

Depends on / 依赖: of_forall_comp
-/
lemma mk_of_iff [P.RespectsIso]
    (H : forall {X Y : C} {f : X ⟶ Y} {R : Presieve X}, R in K X ->
      (P f ↔ forall ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f))) :
    P.IsLocalAtSource K where
  comp hR _ _ hg hf := by grind
  of_forall_comp hR h := by grind

/--
lemma `mk_of_iff_of_zeroHypercover` / 引理 `mk_of_iff_of_zeroHypercover`

English:
lemma mk_of_iff_of_zeroHypercover
  statement: [P.RespectsIso]
  proof: by
  refine .mk_of_iff fun {X Y} f R hR => ?_
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [H _ 𝒰]
  refine ⟨fun h U g => ?_, fun h i => h ⟨i⟩⟩
  rintro ⟨i⟩
  apply h

中文:
引理 mk_of_iff_of_zeroHypercover
  结论: [P.RespectsIso]
  证明: by
  refine .mk_of_iff fun {X Y} f R hR => ?_
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [H _ 𝒰]
  refine ⟨fun h U g => ?_, fun h i => h ⟨i⟩⟩
  rintro ⟨i⟩
  apply h

Depends on / 依赖: Precoverage, Precoverage.mem_iff_exists_zeroHypercover, mem_iff_exists_zeroHypercover, mk_of_iff
-/
lemma mk_of_iff_of_zeroHypercover [P.RespectsIso]
    (H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f ↔ forall i, P (𝒰.f i ≫ f)) :
    P.IsLocalAtSource K := by
  refine .mk_of_iff fun {X Y} f R hR => ?_
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [H _ 𝒰]
  refine ⟨fun h U g => ?_, fun h i => h ⟨i⟩⟩
  rintro ⟨i⟩
  apply h

/--
lemma `mk_of_small` / 引理 `mk_of_small`

English:
lemma mk_of_small
  statement: [P.RespectsIso] [Precoverage.Small.{w} K]
  proof: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

中文:
引理 mk_of_small
  结论: [P.RespectsIso] [Precoverage.Small.{w} K]
  证明: .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, Triangle, Triangle.isoMk, all_goals, contractible_distinguished, isomorphic_distinguished, mk_of_iff_of_zeroHypercover, restrictIndexOfSmall
-/
lemma mk_of_small [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f -> forall i, P (𝒰.f i ≫ f))
    (h₂ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X),
        (forall i, P (𝒰.f i ≫ f)) -> P f) :
    P.IsLocalAtSource K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 => ⟨fun hf _ => h₁ 𝒰 hf _,
    fun h => h₂ 𝒰.restrictIndexOfSmall fun _ => h _⟩

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: [IsLocalAtSource P L] (hle : K <= L)
  statement: IsLocalAtSource P K where
  proof: comp (hle _ hR) _
  of_forall_comp hR h := of_forall_comp (hle _ hR) h

中文:
引理 of_le
  条件: [IsLocalAtSource P L] (hle : K <= L)
  结论: IsLocalAtSource P K where
  证明: comp (hle _ hR) _
  of_forall_comp hR h := of_forall_comp (hle _ hR) h
-/
lemma of_le [IsLocalAtSource P L] (hle : K <= L) : IsLocalAtSource P K where
  comp hR _ _ := comp (hle _ hR) _
  of_forall_comp hR h := of_forall_comp (hle _ hR) h

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: : IsLocalAtSource (⊤ : MorphismProperty C) K where
  body: by simp
  of_forall_comp := by simp

中文:
实例 top
  签名: : IsLocalAtSource (⊤ : Morphism命题erty C) K where
  定义体: by simp
  of_forall_comp := by simp

Depends on / 依赖: of_forall_comp
-/
instance top : IsLocalAtSource (⊤ : MorphismProperty C) K where
  comp := by simp
  of_forall_comp := by simp

variable [IsLocalAtSource P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)

/--
lemma `of_zeroHypercover` / 引理 `of_zeroHypercover`

English:
lemma of_zeroHypercover
  given: (h : forall i, P (𝒰.f i ≫ f))
  statement: P f
  proof: of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _

中文:
引理 of_zeroHypercover
  条件: (h : 对任意 i, P (𝒰.f i ≫ f))
  结论: P f
  证明: of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _

Depends on / 依赖: of_forall_comp
-/
lemma of_zeroHypercover (h : forall i, P (𝒰.f i ≫ f)) : P f :=
  of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _

/--
lemma `iff_of_zeroHypercover` / 引理 `iff_of_zeroHypercover`

English:
lemma iff_of_zeroHypercover
  statement: P f ↔ forall i, P (𝒰.f i ≫ f)
  proof: ⟨fun hf i => comp 𝒰.mem₀ _ ⟨i⟩ hf,
    fun h => of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _⟩

中文:
引理 iff_of_zeroHypercover
  结论: P f ↔ 对任意 i, P (𝒰.f i ≫ f)
  证明: ⟨fun hf i => comp 𝒰.mem₀ _ ⟨i⟩ hf,
    fun h => of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _⟩

Depends on / 依赖: of_forall_comp
-/
lemma iff_of_zeroHypercover : P f ↔ forall i, P (𝒰.f i ≫ f) :=
  ⟨fun hf i => comp 𝒰.mem₀ _ ⟨i⟩ hf,
    fun h => of_forall_comp 𝒰.mem₀ fun U g => by rintro ⟨i⟩; exact h _⟩

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K]
  body: ⟨comp hR _ hg hf.left, comp hR _ hg hf.right⟩
  of_forall_comp hR h :=
    ⟨of_forall_comp hR fun _ _ hg => (h hg).1, of_forall_comp hR fun _ _ hg => (h hg).2⟩

中文:
实例 inf
  签名: (P Q : Morphism命题erty C) [IsLocalAtSource P K] [IsLocalAtSource Q K]
  定义体: ⟨comp hR _ hg hf.left, comp hR _ hg hf.right⟩
  of_forall_comp hR h :=
    ⟨of_forall_comp hR fun _ _ hg => (h hg).1, of_forall_comp hR fun _ _ hg => (h hg).2⟩

Depends on / 依赖: hf.left, hf.right
-/
instance inf (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K] :
    IsLocalAtSource (P ⊓ Q) K where
  comp hR _ _ hg hf := ⟨comp hR _ hg hf.left, comp hR _ hg hf.right⟩
  of_forall_comp hR h :=
    ⟨of_forall_comp hR fun _ _ hg => (h hg).1, of_forall_comp hR fun _ _ hg => (h hg).2⟩

end IsLocalAtSource

set_option backward.defeqAttrib.useBackward true in
/--
lemma `of_zeroHypercover_source` / 引理 `of_zeroHypercover_source`

English:
lemma of_zeroHypercover_source
  statement: {P : MorphismProperty C} {K : Precoverage C}
  proof: by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

中文:
引理 of_zeroHypercover_source
  结论: {P : Morphism命题erty C} {K : Precoverage C}
  证明: by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

Depends on / 依赖: IsLocalAtSource, IsLocalAtSource.iff_of_zeroHypercover, iff_of_zeroHypercover, restrictIndexOfSmall
-/
lemma of_zeroHypercover_source {P : MorphismProperty C} {K : Precoverage C}
    [P.IsLocalAtSource K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : forall i, P (𝒰.f i ≫ f)) :
    P f := by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

end MorphismProperty

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `eq_of_zeroHypercover_target` / 引理 `eq_of_zeroHypercover_target`

English:
lemma eq_of_zeroHypercover_target
  statement: [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
  proof: by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullback

中文:
引理 eq_of_zeroHypercover_target
  结论: [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
  证明: by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullback

Depends on / 依赖: Limits, Limits.eq_of_epi_equalizer, MorphismProperty, MorphismProperty.isomorphisms, condition, eq_of_epi_equalizer, equalizer, equalizerPullbackMapIso, iff_of_zeroHypercover_target, isomorphisms, pullback, pullback.condition, pullback.fst, pullback.snd
-/
lemma eq_of_zeroHypercover_target [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
    {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) {J : Precoverage C}
    (𝒰 : Precoverage.ZeroHypercover.{w} J S) [J.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms C).IsLocalAtTarget J]
    (H : forall i,
      pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq (H i)

end CategoryTheory
