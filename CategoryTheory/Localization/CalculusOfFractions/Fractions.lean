/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Lemmas on fractions

Let `W : MorphismProperty C`, and objects `X` and `Y` in `C`. In this file,
we introduce structures like `W.LeftFraction₂ X Y` which consists of two
left fractions with the "same denominator" which shall be important in
the construction of the preadditive structure on the localized category
when `C` is preadditive and `W` has a left calculus of fractions.

When `W` has a left calculus of fractions, we generalize the lemmas
`RightFraction.exists_leftFraction` as `RightFraction₂.exists_leftFraction₂`,
`Localization.exists_leftFraction` as `Localization.exists_leftFraction₂` and
`Localization.exists_leftFraction₃`, and
`LeftFraction.map_eq_iff` as `LeftFraction₂.map_eq_iff`.

## Implementation note

The lemmas in this file are phrased with data that is bundled into structures like
`LeftFraction₂` or `LeftFraction₃`. It could have been possible to phrase them
with "unbundled data". However, this would require introducing 4 or 5 variables instead
of one. It is also very convenient to use dot notation.
Many definitions have been made reducible so as to ease rewrites when this API is used.

-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W]

namespace MorphismProperty

/--
Definition of `LeftFraction₂` / `LeftFraction₂` 的定义

English:
structure LeftFraction₂
  parameters: (X Y : C)
  axioms and operations (5):
    - {Y' : C}
    - f : X ⟶ Y'
    - f' : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s

中文:
结构 LeftFraction₂
  参数: (X Y : C)
  公理与运算 (5 个):
    - {Y' : C}
    - f : X ⟶ Y'
    - f' : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s
-/
structure LeftFraction₂ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

instance {X Y : C} (z : W.LeftFraction₂ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/--
Definition of `LeftFraction₃` / `LeftFraction₃` 的定义

English:
structure LeftFraction₃
  parameters: (X Y : C)
  axioms and operations (6):
    - {Y' : C}
    - f : X ⟶ Y'
    - f' : X ⟶ Y'
    - f'' : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s

中文:
结构 LeftFraction₃
  参数: (X Y : C)
  公理与运算 (6 个):
    - {Y' : C}
    - f : X ⟶ Y'
    - f' : X ⟶ Y'
    - f'' : X ⟶ Y'
    - s : Y ⟶ Y'
    - hs : W s
-/
structure LeftFraction₃ (X Y : C) where
  /-- the auxiliary object of left fractions -/
  {Y' : C}
  /-- the numerator of the first left fraction -/
  f : X ⟶ Y'
  /-- the numerator of the second left fraction -/
  f' : X ⟶ Y'
  /-- the numerator of the third left fraction -/
  f'' : X ⟶ Y'
  /-- the denominator of the left fractions -/
  s : Y ⟶ Y'
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s

instance {X Y : C} (z : W.LeftFraction₃ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

/--
Definition of `RightFraction₂` / `RightFraction₂` 的定义

English:
structure RightFraction₂
  parameters: (X Y : C)
  axioms and operations (5):
    - {X' : C}
    - s : X' ⟶ X
    - hs : W s
    - f : X' ⟶ Y
    - f' : X' ⟶ Y

中文:
结构 RightFraction₂
  参数: (X Y : C)
  公理与运算 (5 个):
    - {X' : C}
    - s : X' ⟶ X
    - hs : W s
    - f : X' ⟶ Y
    - f' : X' ⟶ Y
-/
structure RightFraction₂ (X Y : C) where
  /-- the auxiliary object of right fractions -/
  {X' : C}
  /-- the denominator of the right fractions -/
  s : X' ⟶ X
  /-- the condition that the denominator belongs to the given morphism property -/
  hs : W s
  /-- the numerator of the first right fraction -/
  f : X' ⟶ Y
  /-- the numerator of the second right fraction -/
  f' : X' ⟶ Y

instance {X Y : C} (z : W.RightFraction₂ X Y) : IsIso (L.map z.s) :=
  Localization.inverts L W _ z.hs

variable {W}

/--
Definition of `LeftFraction₂Rel` / `LeftFraction₂Rel` 的定义

English:
definition LeftFraction₂Rel
  signature: {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y)
  body: exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)

中文:
定义 LeftFraction₂Rel
  签名: {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y)
  定义体: exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)
-/
def LeftFraction₂Rel {X Y : C} (z₁ z₂ : W.LeftFraction₂ X Y) : Prop :=
  exists (Z : C) (t₁ : z₁.Y' ⟶ Z) (t₂ : z₂.Y' ⟶ Z) (_ : z₁.s ≫ t₁ = z₂.s ≫ t₂)
    (_ : z₁.f ≫ t₁ = z₂.f ≫ t₂) (_ : z₁.f' ≫ t₁ = z₂.f' ≫ t₂), W (z₁.s ≫ t₁)

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

中文:
缩写 fst
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs
-/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

中文:
缩写 snd
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs
-/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  signature: : W.LeftFraction₂ X Y where
  body: φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs

中文:
缩写 symm
  签名: : W.LeftFraction₂ X Y where
  定义体: φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs
-/
abbrev symm : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f
  s := φ.s
  hs := φ.hs

end LeftFraction₂

namespace LeftFraction₃

variable {X Y : C} (φ : W.LeftFraction₃ X Y)

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

中文:
缩写 fst
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs
-/
abbrev fst : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f
  s := φ.s
  hs := φ.hs

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

中文:
缩写 snd
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs
-/
abbrev snd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/--
Definition of `thd` / `thd` 的定义

English:
abbreviation thd
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs

中文:
缩写 thd
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs
-/
abbrev thd : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f''
  s := φ.s
  hs := φ.hs

/--
Definition of `forgetFst` / `forgetFst` 的定义

English:
abbreviation forgetFst
  signature: : W.LeftFraction₂ X Y where
  body: φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs

中文:
缩写 forgetFst
  签名: : W.LeftFraction₂ X Y where
  定义体: φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs
-/
abbrev forgetFst : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f'
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/--
Definition of `forgetSnd` / `forgetSnd` 的定义

English:
abbreviation forgetSnd
  signature: : W.LeftFraction₂ X Y where
  body: φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs

中文:
缩写 forgetSnd
  签名: : W.LeftFraction₂ X Y where
  定义体: φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs
-/
abbrev forgetSnd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f''
  s := φ.s
  hs := φ.hs

/--
Definition of `forgetThd` / `forgetThd` 的定义

English:
abbreviation forgetThd
  signature: : W.LeftFraction₂ X Y where
  body: φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs

中文:
缩写 forgetThd
  签名: : W.LeftFraction₂ X Y where
  定义体: φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs
-/
abbrev forgetThd : W.LeftFraction₂ X Y where
  Y' := φ.Y'
  f := φ.f
  f' := φ.f'
  s := φ.s
  hs := φ.hs

end LeftFraction₃

namespace LeftFraction₂Rel

variable {X Y : C} {z₁ z₂ : W.LeftFraction₂ X Y}

/--
lemma `fst` / 引理 `fst`

English:
lemma fst
  given: (h : LeftFraction₂Rel z₁ z₂)
  statement: LeftFractionRel z₁.fst z₂.fst
  proof: by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩

中文:
引理 fst
  条件: (h : LeftFraction₂Rel z₁ z₂)
  结论: LeftFractionRel z₁.fst z₂.fst
  证明: by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩
-/
lemma fst (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.fst z₂.fst := by
  obtain ⟨Z, t₁, t₂, hst, hft, _, ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft, ht⟩

/--
lemma `snd` / 引理 `snd`

English:
lemma snd
  given: (h : LeftFraction₂Rel z₁ z₂)
  statement: LeftFractionRel z₁.snd z₂.snd
  proof: by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩

中文:
引理 snd
  条件: (h : LeftFraction₂Rel z₁ z₂)
  结论: LeftFractionRel z₁.snd z₂.snd
  证明: by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩
-/
lemma snd (h : LeftFraction₂Rel z₁ z₂) : LeftFractionRel z₁.snd z₂.snd := by
  obtain ⟨Z, t₁, t₂, hst, _, hft', ht⟩ := h
  exact ⟨Z, t₁, t₂, hst, hft', ht⟩

end LeftFraction₂Rel

namespace LeftFraction₂

variable (W)
variable [W.HasLeftCalculusOfFractions]

/--
lemma `map_eq_iff` / 引理 `map_eq_iff`

English:
lemma map_eq_iff
  given: {X Y : C} (φ ψ : W.LeftFraction₂ X Y)
  proof: by
  simp only [LeftFraction.map_eq_iff L W]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    obtain ⟨Z', t₁', t₂', hst', hft', ht'⟩ := h'
    dsimp at t₁ t₂ t₁' t₂' hst hft hst' hft' ht ht'
    have ⟨α, hα⟩ := (RightFraction.mk _ ht (φ.s ≫ t₁')).exists_leftFraction
    

中文:
引理 map_eq_iff
  条件: {X Y : C} (φ ψ : W.LeftFraction₂ X Y)
  证明: by
  simp only [LeftFraction.map_eq_iff L W]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    obtain ⟨Z', t₁', t₂', hst', hft', ht'⟩ := h'
    dsimp at t₁ t₂ t₁' t₂' hst hft hst' hft' ht ht'
    have ⟨α, hα⟩ := (RightFraction.mk _ ht (φ.s ≫ t₁')).exists_leftFraction
    

Depends on / 依赖: Category, Category.assoc, HasLeftCalculusOfFractions, HasLeftCalculusOfFractions.ext, LeftFraction, LeftFraction.map_eq_iff, RightFraction, RightFraction.mk, exists_leftFraction, map_eq_iff, reassoc_o, reassoc_of
-/
lemma map_eq_iff {X Y : C} (φ ψ : W.LeftFraction₂ X Y) :
    (φ.fst.map L (Localization.inverts _ _) = ψ.fst.map L (Localization.inverts _ _) ∧
    φ.snd.map L (Localization.inverts _ _) = ψ.snd.map L (Localization.inverts _ _)) ↔
      LeftFraction₂Rel φ ψ := by
  simp only [LeftFraction.map_eq_iff L W]
  constructor
  · intro ⟨h, h'⟩
    obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ := h
    obtain ⟨Z', t₁', t₂', hst', hft', ht'⟩ := h'
    dsimp at t₁ t₂ t₁' t₂' hst hft hst' hft' ht ht'
    have ⟨α, hα⟩ := (RightFraction.mk _ ht (φ.s ≫ t₁')).exists_leftFraction
    simp only [Category.assoc] at hα
    obtain ⟨Z'', u, hu, fac⟩ := HasLeftCalculusOfFractions.ext _ _ _ φ.hs hα
    have hα' : ψ.s ≫ t₂ ≫ α.f ≫ u = ψ.s ≫ t₂' ≫ α.s ≫ u := by
      rw [← reassoc_of% hst]; rw [← reassoc_of% hα]; rw [← reassoc_of% hst']
    obtain ⟨Z''', u', hu', fac'⟩ := HasLeftCalculusOfFractions.ext _ _ _ ψ.hs hα'
    simp only [Category.assoc] at fac fac'
    refine ⟨Z''', t₁' ≫ α.s ≫ u ≫ u', t₂' ≫ α.s ≫ u ≫ u', ?_, ?_, ?_, ?_⟩
    · rw [reassoc_of% hst']
    · rw [reassoc_of% fac, reassoc_of% hft, fac']
    · rw [reassoc_of% hft']
    · rw [← Category.assoc]
      exact W.comp_mem _ _ ht' (W.comp_mem _ _ α.hs (W.comp_mem _ _ hu hu'))
  · intro h
    exact ⟨h.fst, h.snd⟩

end LeftFraction₂

namespace RightFraction₂

variable {X Y : C}
variable (φ : W.RightFraction₂ X Y)

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: : W.RightFraction X Y where
  body: φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs

中文:
缩写 fst
  签名: : W.RightFraction X Y where
  定义体: φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs
-/
abbrev fst : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f
  s := φ.s
  hs := φ.hs

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: : W.RightFraction X Y where
  body: φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs

中文:
缩写 snd
  签名: : W.RightFraction X Y where
  定义体: φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs
-/
abbrev snd : W.RightFraction X Y where
  X' := φ.X'
  f := φ.f'
  s := φ.s
  hs := φ.hs

/--
lemma `exists_leftFraction₂` / 引理 `exists_leftFraction₂`

English:
lemma exists_leftFraction₂
  given: [W.HasLeftCalculusOfFractions]
  proof: by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_

中文:
引理 存在_leftFraction₂
  条件: [W.有LeftCalculusOfFractions]
  证明: by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_

Depends on / 依赖: RightFraction, RightFraction.mk, W.comp_mem, comp_mem, exists_leftFraction, fst.exists_leftFraction, reassoc_of, snd.exists_leftFraction
-/
lemma exists_leftFraction₂ [W.HasLeftCalculusOfFractions] :
    exists (ψ : W.LeftFraction₂ X Y), φ.f ≫ ψ.s = φ.s ≫ ψ.f ∧
      φ.f' ≫ ψ.s = φ.s ≫ ψ.f' := by
  obtain ⟨ψ₁, hψ₁⟩ := φ.fst.exists_leftFraction
  obtain ⟨ψ₂, hψ₂⟩ := φ.snd.exists_leftFraction
  obtain ⟨α, hα⟩ := (RightFraction.mk _ ψ₁.hs ψ₂.s).exists_leftFraction
  dsimp at hψ₁ hψ₂ hα
  refine ⟨LeftFraction₂.mk (ψ₁.f ≫ α.f) (ψ₂.f ≫ α.s) (ψ₂.s ≫ α.s)
      (W.comp_mem _ _ ψ₂.hs α.hs), ?_, ?_⟩
  · dsimp
    rw [hα]; rw [reassoc_of% hψ₁]
  · rw [reassoc_of% hψ₂]

end RightFraction₂

end MorphismProperty

namespace Localization

variable [W.HasLeftCalculusOfFractions]

open MorphismProperty

/--
lemma `exists_leftFraction₂` / 引理 `exists_leftFraction₂`

English:
lemma exists_leftFraction₂
  given: {X Y : C} (f f' : L.obj X ⟶ L.obj Y)
  proof: by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_

中文:
引理 存在_leftFraction₂
  条件: {X Y : C} (f f' : L.obj X ⟶ L.obj Y)
  证明: by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_

Depends on / 依赖: L.map, L.map_comp, LeftFraction, LeftFraction.map_comp_map_s, LeftFraction.map_comp_map_s_assoc, RightFraction, RightFraction.mk, W.LeftFraction, W.comp_mem, cancel_mono, comp_mem, exists_leftFraction, infer_instance, map_comp, map_comp_map_s, map_comp_map_s_assoc
-/
lemma exists_leftFraction₂ {X Y : C} (f f' : L.obj X ⟶ L.obj Y) :
    exists (φ : W.LeftFraction₂ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) := by
  have ⟨φ, hφ⟩ := exists_leftFraction L W f
  have ⟨φ', hφ'⟩ := exists_leftFraction L W f'
  obtain ⟨α, hα⟩ := (RightFraction.mk _ φ.hs φ'.s).exists_leftFraction
  let ψ : W.LeftFraction₂ X Y :=
    { Y' := α.Y'
      f := φ.f ≫ α.f
      f' := φ'.f ≫ α.s
      s := φ'.s ≫ α.s
      hs := W.comp_mem _ _ φ'.hs α.hs }
  have : IsIso (L.map (φ'.s ≫ α.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), LeftFraction.map_comp_map_s,
      hα, L.map_comp, hφ, LeftFraction.map_comp_map_s_assoc,
      L.map_comp]
  · rw [← cancel_mono (L.map (φ'.s ≫ α.s)), hφ']
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc]; rw [LeftFraction.map_comp_map_s]; rw [L.map_comp]

/--
lemma `exists_leftFraction₃` / 引理 `exists_leftFraction₃`

English:
lemma exists_leftFraction₃
  given: {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫

中文:
引理 存在_leftFraction₃
  条件: {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫

Depends on / 依赖: L.map, L.map_co, L.map_comp, LeftFraction, LeftFraction.map_comp_map_s, RightFraction, RightFraction.mk, W.LeftFraction, W.comp_mem, cancel_mono, comp_mem, exists_leftFraction, infer_instance, map_co, map_comp, map_comp_map_s
-/
lemma exists_leftFraction₃ {X Y : C} (f f' f'' : L.obj X ⟶ L.obj Y) :
    exists (φ : W.LeftFraction₃ X Y), f = φ.fst.map L (inverts L W) ∧
      f' = φ.snd.map L (inverts L W) ∧
      f'' = φ.thd.map L (inverts L W) := by
  obtain ⟨α, hα, hα'⟩ := exists_leftFraction₂ L W f f'
  have ⟨β, hβ⟩ := exists_leftFraction L W f''
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.s).exists_leftFraction
  dsimp at hγ
  let ψ : W.LeftFraction₃ X Y :=
    { Y' := γ.Y'
      f := α.f ≫ γ.f
      f' := α.f' ≫ γ.f
      f'' := β.f ≫ γ.s
      s := β.s ≫ γ.s
      hs := W.comp_mem _ _ β.hs γ.hs }
  have : IsIso (L.map (β.s ≫ γ.s)) := by
    rw [L.map_comp]
    infer_instance
  refine ⟨ψ, ?_, ?_, ?_⟩
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα, hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), LeftFraction.map_comp_map_s, hα', hγ,
      L.map_comp, LeftFraction.map_comp_map_s_assoc, L.map_comp]
  · rw [← cancel_mono (L.map (β.s ≫ γ.s)), hβ]
    nth_rw 1 [L.map_comp]
    rw [LeftFraction.map_comp_map_s_assoc]; rw [LeftFraction.map_comp_map_s]; rw [L.map_comp]

end Localization

/--
lemma `Functor.faithful_of_comp_of_hasLeftCalculusOfFractions` / 引理 `Functor.faithful_of_comp_of_hasLeftCalculusOfFractions`

English:
lemma Functor.faithful_of_comp_of_hasLeftCalculusOfFractions
  proof: by
  have := Localization.essSurj L W
  refine F.faithful_of_comp_essSurj L (fun X₁ X₂ f g hfg => ?_)
  obtain ⟨φ, rfl, rfl⟩ := Localization.exists_leftFraction₂ L W f g
  rw [← cancel_mono (L.map φ.s)]; rw [φ.fst.map_comp_map_s L]; rw [φ.snd.map_comp_map_s L]
  apply h
  simpa only [← F.map_comp, φ

中文:
引理 函子.faithful_of_comp_of_hasLeftCalculusOfFractions
  证明: by
  have := Localization.essSurj L W
  refine F.faithful_of_comp_essSurj L (fun X₁ X₂ f g hfg => ?_)
  obtain ⟨φ, rfl, rfl⟩ := Localization.exists_leftFraction₂ L W f g
  rw [← cancel_mono (L.map φ.s)]; rw [φ.fst.map_comp_map_s L]; rw [φ.snd.map_comp_map_s L]
  apply h
  simpa only [← F.map_comp, φ

Depends on / 依赖: F.faithful_of_comp_essSurj, F.map, F.map_comp, L.map, Localization, Localization.essSurj, Localization.exists_leftFraction, cancel_mono, essSurj, faithful_of_comp_essSurj, fst.map_comp_map_s, map_comp, map_comp_map_s, snd.map_comp_map_s
-/
lemma Functor.faithful_of_comp_of_hasLeftCalculusOfFractions
    {E : Type*} [Category* E] (F : D ⥤ E)
    [W.HasLeftCalculusOfFractions]
    (h : forall ⦃X₁ X₂ : C⦄ (f g : X₁ ⟶ X₂), F.map (L.map f) = F.map (L.map g) -> L.map f = L.map g) :
    F.Faithful := by
  have := Localization.essSurj L W
  refine F.faithful_of_comp_essSurj L (fun X₁ X₂ f g hfg => ?_)
  obtain ⟨φ, rfl, rfl⟩ := Localization.exists_leftFraction₂ L W f g
  rw [← cancel_mono (L.map φ.s)]; rw [φ.fst.map_comp_map_s L]; rw [φ.snd.map_comp_map_s L]
  apply h
  simpa only [← F.map_comp, φ.fst.map_comp_map_s, φ.snd.map_comp_map_s] using
    hfg =≫ F.map (L.map φ.s)

end CategoryTheory
