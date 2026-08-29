/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The preadditive category structure on the localized category

In this file, it is shown that if `W : MorphismProperty C` has a left calculus
of fractions, and `C` is preadditive, then the localized category is preadditive,
and the localization functor is additive.

Let `L : C ⥤ D` be a localization functor for `W`. We first construct an abelian
group structure on `L.obj X ⟶ L.obj Y` for `X` and `Y` in `C`. The addition
is defined using representatives of two morphisms in `L` as left fractions with
the same denominator thanks to the lemmas in
`CategoryTheory.Localization.CalculusOfFractions.Fractions`.
As `L` is essentially surjective, we finally transport these abelian group structures
to `X' ⟶ Y'` for all `X'` and `Y'` in `D`.

Preadditive category instances are defined on the categories `W.Localization`
(and `W.Localization'`) under the assumption that `W` has a left calculus of fractions.
(It would be easy to deduce from the results in this file that if `W` has a right calculus
of fractions, then the localized category can also be equipped with
a preadditive structure, but only one of these two constructions can be made an instance!)

-/

@[expose] public section

namespace CategoryTheory

open MorphismProperty Preadditive Limits Category

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] (L : C ⥤ D)
  {W : MorphismProperty C} [L.IsLocalization W]

namespace MorphismProperty

/--
Definition of `LeftFraction.neg` / `LeftFraction.neg` 的定义

English:
abbreviation LeftFraction.neg
  signature: {X Y : C} (φ : W.LeftFraction X Y)
  body: φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs

中文:
缩写 LeftFraction.neg
  签名: {X Y : C} (φ : W.LeftFraction X Y)
  定义体: φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs
-/
abbrev LeftFraction.neg {X Y : C} (φ : W.LeftFraction X Y) :
    W.LeftFraction X Y where
  Y' := φ.Y'
  f := -φ.f
  s := φ.s
  hs := φ.hs

namespace LeftFraction₂

variable {X Y : C} (φ : W.LeftFraction₂ X Y)

/--
Definition of `add` / `add` 的定义

English:
abbreviation add
  signature: : W.LeftFraction X Y where
  body: φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs

@[simp]

中文:
缩写 add
  签名: : W.LeftFraction X Y where
  定义体: φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs

@[simp]
-/
abbrev add : W.LeftFraction X Y where
  Y' := φ.Y'
  f := φ.f + φ.f'
  s := φ.s
  hs := φ.hs

@[simp]
/--
lemma `symm_add` / 引理 `symm_add`

English:
lemma symm_add
  statement: φ.symm.add = φ.add
  proof: by
  grind

@[simp]

中文:
引理 symm_add
  结论: φ.symm.add = φ.add
  证明: by
  grind

@[simp]
-/
lemma symm_add : φ.symm.add = φ.add := by
  grind

@[simp]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: (F : C ⥤ D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive]
  proof: by
  have := hF φ.s φ.hs
  rw [← cancel_mono (F.map φ.s)]; rw [add_comp]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [F.map_add]

中文:
引理 map_add
  条件: (F : C ⥤ D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive]
  证明: by
  have := hF φ.s φ.hs
  rw [← cancel_mono (F.map φ.s)]; rw [add_comp]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [F.map_add]

Depends on / 依赖: F.map, F.map_add, LeftFraction, LeftFraction.map_comp_map_s, add_comp, cancel_mono, map_add, map_comp_map_s
-/
lemma map_add (F : C ⥤ D) (hF : W.IsInvertedBy F) [Preadditive D] [F.Additive] :
    φ.add.map F hF = φ.fst.map F hF + φ.snd.map F hF := by
  have := hF φ.s φ.hs
  rw [← cancel_mono (F.map φ.s)]; rw [add_comp]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [F.map_add]

end LeftFraction₂

end MorphismProperty

variable (W)

namespace Localization

namespace Preadditive

section ImplementationDetails

/-! The definitions in this section (like `neg'` and `add'`) should never be used
directly. These are auxiliary definitions in order to construct the preadditive
structure `Localization.preadditive` (which is made irreducible). The user
should only rely on the fact that the localization functor is additive, as this
completely determines the preadditive structure on the localized category when
there is a calculus of left fractions. -/

variable [W.HasLeftCalculusOfFractions] {X Y Z : C}
variable {L}

/--
Definition of `neg'` / `neg'` 的定义

English:
definition neg'
  signature: (f : L.obj X ⟶ L.obj Y)
  body: (exists_leftFraction L W f).choose.neg.map L (inverts L W)

中文:
定义 neg'
  签名: (f : L.obj X ⟶ L.obj Y)
  定义体: (exists_leftFraction L W f).choose.neg.map L (inverts L W)

Depends on / 依赖: choose.neg.map, exists_leftFraction, inverts
-/
noncomputable def neg' (f : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction L W f).choose.neg.map L (inverts L W)

/--
lemma `neg'_eq` / 引理 `neg'_eq`

English:
lemma neg'_eq
  statement: (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y)
  proof: by
  obtain ⟨φ₀, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction X Y)
    (_ : f = φ₀.map L (inverts L W)),
      neg' W f = φ₀.neg.map L (inverts L W) :=
    ⟨_, (exists_leftFraction L W f).choose_spec, rfl⟩
  rw [MorphismProperty.LeftFraction.map_eq_iff] at hφ
  obtain ⟨Y', t₁, t₂, hst, hft, ht⟩ := hφ
  h

中文:
引理 neg'_eq
  结论: (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y)
  证明: by
  obtain ⟨φ₀, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction X Y)
    (_ : f = φ₀.map L (inverts L W)),
      neg' W f = φ₀.neg.map L (inverts L W) :=
    ⟨_, (exists_leftFraction L W f).choose_spec, rfl⟩
  rw [MorphismProperty.LeftFraction.map_eq_iff] at hφ
  obtain ⟨Y', t₁, t₂, hst, hft, ht⟩ := hφ
  h
-/
lemma neg'_eq (f : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction X Y)
    (hφ : f = φ.map L (inverts L W)) :
    neg' W f = φ.neg.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction X Y)
    (_ : f = φ₀.map L (inverts L W)),
      neg' W f = φ₀.neg.map L (inverts L W) :=
    ⟨_, (exists_leftFraction L W f).choose_spec, rfl⟩
  rw [MorphismProperty.LeftFraction.map_eq_iff] at hφ
  obtain ⟨Y', t₁, t₂, hst, hft, ht⟩ := hφ
  have := inverts L W _ ht
  rw [← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 1 [L.map_comp]
  rw [hφ₀]; rw [hst]; rw [LeftFraction.map_comp_map_s_assoc]; rw [L.map_comp]; rw [LeftFraction.map_comp_map_s_assoc]; rw [← L.map_comp]; rw [← L.map_comp]; rw [neg_comp]; rw [neg_comp]; rw [hft]

/--
Definition of `add'` / `add'` 的定义

English:
definition add'
  signature: (f₁ f₂ : L.obj X ⟶ L.obj Y)
  body: (exists_leftFraction₂ L W f₁ f₂).choose.add.map L (inverts L W)

中文:
定义 add'
  签名: (f₁ f₂ : L.obj X ⟶ L.obj Y)
  定义体: (exists_leftFraction₂ L W f₁ f₂).choose.add.map L (inverts L W)

Depends on / 依赖: choose.add.map, inverts
-/
noncomputable def add' (f₁ f₂ : L.obj X ⟶ L.obj Y) : L.obj X ⟶ L.obj Y :=
  (exists_leftFraction₂ L W f₁ f₂).choose.add.map L (inverts L W)

/--
lemma `add'_eq` / 引理 `add'_eq`

English:
lemma add'_eq
  statement: (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
  proof: by
  obtain ⟨φ₀, rfl, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction₂ X Y)
    (_ : f₁ = φ₀.fst.map L (inverts L W))
    (_ : f₂ = φ₀.snd.map L (inverts L W)),
    add' W f₁ f₂ = φ₀.add.map L (inverts L W) :=
    ⟨(exists_leftFraction₂ L W f₁ f₂).choose,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.1

中文:
引理 add'_eq
  结论: (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
  证明: by
  obtain ⟨φ₀, rfl, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction₂ X Y)
    (_ : f₁ = φ₀.fst.map L (inverts L W))
    (_ : f₂ = φ₀.snd.map L (inverts L W)),
    add' W f₁ f₂ = φ₀.add.map L (inverts L W) :=
    ⟨(exists_leftFraction₂ L W f₁ f₂).choose,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.1
-/
lemma add'_eq (f₁ f₂ : L.obj X ⟶ L.obj Y) (φ : W.LeftFraction₂ X Y)
    (hφ₁ : f₁ = φ.fst.map L (inverts L W))
    (hφ₂ : f₂ = φ.snd.map L (inverts L W)) :
    add' W f₁ f₂ = φ.add.map L (inverts L W) := by
  obtain ⟨φ₀, rfl, rfl, hφ₀⟩ : exists (φ₀ : W.LeftFraction₂ X Y)
    (_ : f₁ = φ₀.fst.map L (inverts L W))
    (_ : f₂ = φ₀.snd.map L (inverts L W)),
    add' W f₁ f₂ = φ₀.add.map L (inverts L W) :=
    ⟨(exists_leftFraction₂ L W f₁ f₂).choose,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.1,
      (exists_leftFraction₂ L W f₁ f₂).choose_spec.2, rfl⟩
  obtain ⟨Z, t₁, t₂, hst, hft, hft', ht⟩ := (LeftFraction₂.map_eq_iff L W φ₀ φ).1 ⟨hφ₁, hφ₂⟩
  have := inverts L W _ ht
  rw [hφ₀]; rw [← cancel_mono (L.map (φ₀.s ≫ t₁))]
  nth_rw 2 [hst]
  rw [L.map_comp]; rw [L.map_comp]; rw [LeftFraction.map_comp_map_s_assoc]; rw [LeftFraction.map_comp_map_s_assoc]; rw [← L.map_comp]; rw [← L.map_comp]; rw [add_comp]; rw [add_comp]; rw [hft]; rw [hft']

/--
lemma `add'_comm` / 引理 `add'_comm`

English:
lemma add'_comm
  given: (f₁ f₂ : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W f₂ f₁ α.symm h₂ h₁]; rw [α.symm_add]

中文:
引理 add'_comm
  条件: (f₁ f₂ : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W f₂ f₁ α.symm h₂ h₁]; rw [α.symm_add]
-/
lemma add'_comm (f₁ f₂ : L.obj X ⟶ L.obj Y) :
    add' W f₁ f₂ = add' W f₂ f₁ := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W f₂ f₁ α.symm h₂ h₁]; rw [α.symm_add]

/--
lemma `add'_zero` / 引理 `add'_zero`

English:
lemma add'_zero
  given: (f : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  rw [add'_eq W f (L.map 0) (LeftFraction₂.mk α.f 0 α.s α.hs) hα]; rw [hα]; swap
  · rw [← cancel_mono (L.map α.s), ← L.map_comp, Limits.zero_comp,
      LeftFraction.map_comp_map_s]
  dsimp [LeftFraction₂.add]
  rw [add_zero]

中文:
引理 add'_zero
  条件: (f : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  rw [add'_eq W f (L.map 0) (LeftFraction₂.mk α.f 0 α.s α.hs) hα]; rw [hα]; swap
  · rw [← cancel_mono (L.map α.s), ← L.map_comp, Limits.zero_comp,
      LeftFraction.map_comp_map_s]
  dsimp [LeftFraction₂.add]
  rw [add_zero]
-/
lemma add'_zero (f : L.obj X ⟶ L.obj Y) :
    add' W f (L.map 0) = f := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  rw [add'_eq W f (L.map 0) (LeftFraction₂.mk α.f 0 α.s α.hs) hα]; rw [hα]; swap
  · rw [← cancel_mono (L.map α.s), ← L.map_comp, Limits.zero_comp,
      LeftFraction.map_comp_map_s]
  dsimp [LeftFraction₂.add]
  rw [add_zero]

/--
lemma `zero_add'` / 引理 `zero_add'`

English:
lemma zero_add'
  given: (f : L.obj X ⟶ L.obj Y)
  proof: by
  rw [add'_comm]; rw [add'_zero]

中文:
引理 zero_add'
  条件: (f : L.obj X ⟶ L.obj Y)
  证明: by
  rw [add'_comm]; rw [add'_zero]

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, _comm, _zero, coyoneda, coyoneda.obj, e.symm, evaluation, freeYoneda, freeYonedaHomEquiv, freeYonedaHomEquiv.trans, ofComponents, preservesColimitsOfShape_of_isCardinalPresentable, preservesColimitsOfShape_of_natIso, uliftFunctor
-/
lemma zero_add' (f : L.obj X ⟶ L.obj Y) :
    add' W (L.map 0) f = f := by
  rw [add'_comm]; rw [add'_zero]

/--
lemma `neg'_add'_self` / 引理 `neg'_add'_self`

English:
lemma neg'_add'_self
  given: (f : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨α, rfl⟩ := exists_leftFraction L W f
  rw [add'_eq W _ _ (LeftFraction₂.mk (-α.f) α.f α.s α.hs) (neg'_eq W _ _ rfl) rfl]
  simp only [← cancel_mono (L.map α.s), LeftFraction.map_comp_map_s, ← L.map_comp,
    Limits.zero_comp, neg_add_cancel]

中文:
引理 neg'_add'_self
  条件: (f : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨α, rfl⟩ := exists_leftFraction L W f
  rw [add'_eq W _ _ (LeftFraction₂.mk (-α.f) α.f α.s α.hs) (neg'_eq W _ _ rfl) rfl]
  simp only [← cancel_mono (L.map α.s), LeftFraction.map_comp_map_s, ← L.map_comp,
    Limits.zero_comp, neg_add_cancel]

Depends on / 依赖: Equiv.toIso, Equiv.ulift.symm, NatIso, NatIso.ofComponents, coyoneda, coyoneda.obj, e.symm, evaluation, ofComponents, preservesColimitsOfShape_of_natIso, uliftFunctor, uliftYoneda, uliftYonedaEquiv, uliftYonedaEquiv.trans
-/
lemma neg'_add'_self (f : L.obj X ⟶ L.obj Y) :
    add' W (neg' W f) f = L.map 0 := by
  obtain ⟨α, rfl⟩ := exists_leftFraction L W f
  rw [add'_eq W _ _ (LeftFraction₂.mk (-α.f) α.f α.s α.hs) (neg'_eq W _ _ rfl) rfl]
  simp only [← cancel_mono (L.map α.s), LeftFraction.map_comp_map_s, ← L.map_comp,
    Limits.zero_comp, neg_add_cancel]

/--
lemma `add'_assoc` / 引理 `add'_assoc`

English:
lemma add'_assoc
  given: (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y)
  proof: by
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_leftFraction₃ L W f₁ f₂ f₃
  rw [add'_eq W f₁ f₂ α.forgetThd h₁ h₂]; rw [add'_eq W f₂ f₃ α.forgetFst h₂ h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk (α.f + α.f') α.f'' α.s α.hs) rfl h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk α.f (α.f' + α.f'') α.s α.hs) h₁ rfl]
  dsim

中文:
引理 add'_assoc
  条件: (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y)
  证明: by
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_leftFraction₃ L W f₁ f₂ f₃
  rw [add'_eq W f₁ f₂ α.forgetThd h₁ h₂]; rw [add'_eq W f₂ f₃ α.forgetFst h₂ h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk (α.f + α.f') α.f'' α.s α.hs) rfl h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk α.f (α.f' + α.f'') α.s α.hs) h₁ rfl]
  dsim
-/
lemma add'_assoc (f₁ f₂ f₃ : L.obj X ⟶ L.obj Y) :
    add' W (add' W f₁ f₂) f₃ = add' W f₁ (add' W f₂ f₃) := by
  obtain ⟨α, h₁, h₂, h₃⟩ := exists_leftFraction₃ L W f₁ f₂ f₃
  rw [add'_eq W f₁ f₂ α.forgetThd h₁ h₂]; rw [add'_eq W f₂ f₃ α.forgetFst h₂ h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk (α.f + α.f') α.f'' α.s α.hs) rfl h₃]; rw [add'_eq W _ _ (LeftFraction₂.mk α.f (α.f' + α.f'') α.s α.hs) h₁ rfl]
  dsimp [LeftFraction₂.add]
  rw [add_assoc]

@[reassoc (attr := simp)]
/--
lemma `add'_comp` / 引理 `add'_comp`

English:
lemma add'_comp
  given: (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z)
  proof: by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  obtain ⟨β, hβ⟩ := exists_leftFraction L W g
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.f).exists_leftFraction
  dsimp at hγ
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W (f₁ ≫ g) (f₂ ≫ g)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f' ≫ γ.f) (

中文:
引理 add'_comp
  条件: (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z)
  证明: by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  obtain ⟨β, hβ⟩ := exists_leftFraction L W g
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.f).exists_leftFraction
  dsimp at hγ
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W (f₁ ≫ g) (f₂ ≫ g)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f' ≫ γ.f) (

Depends on / 依赖: IsCardinalLocallyPresentable, IsCardinalLocallyPresentable.iff_exists_isStrongGenerator, iff_exists_isStrongGenerator, infer_instance, isCardinalPresentable_iff, isStrongGenerator
-/
lemma add'_comp (f₁ f₂ : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    add' W f₁ f₂ ≫ g = add' W (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨α, h₁, h₂⟩ := exists_leftFraction₂ L W f₁ f₂
  obtain ⟨β, hβ⟩ := exists_leftFraction L W g
  obtain ⟨γ, hγ⟩ := (RightFraction.mk _ α.hs β.f).exists_leftFraction
  dsimp at hγ
  rw [add'_eq W f₁ f₂ α h₁ h₂]; rw [add'_eq W (f₁ ≫ g) (f₂ ≫ g)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f' ≫ γ.f) (β.s ≫ γ.s)
    (W.comp_mem _ _ β.hs γ.hs))]; rotate_left
  · rw [h₁, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  · rw [h₂, hβ]
    exact LeftFraction.map_comp_map_eq_map _ _ _ hγ _
  rw [hβ]; rw [LeftFraction.map_comp_map_eq_map _ _ γ hγ]
  dsimp [LeftFraction₂.add]
  rw [add_comp]

@[reassoc (attr := simp)]
/--
lemma `comp_add'` / 引理 `comp_add'`

English:
lemma comp_add'
  given: (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z)
  proof: by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_leftFraction₂ L W g₁ g₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (RightFraction₂.mk _ α.hs β.f β.f').exists_leftFraction₂
  dsimp at hγ₁ hγ₂
  rw [add'_eq W g₁ g₂ β hβ₁ hβ₂]; rw [add'_eq W (f ≫ g₁) (f ≫ g₂)
    (LeftFraction₂.mk (α.f

中文:
引理 comp_add'
  条件: (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z)
  证明: by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_leftFraction₂ L W g₁ g₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (RightFraction₂.mk _ α.hs β.f β.f').exists_leftFraction₂
  dsimp at hγ₁ hγ₂
  rw [add'_eq W g₁ g₂ β hβ₁ hβ₂]; rw [add'_eq W (f ≫ g₁) (f ≫ g₂)
    (LeftFraction₂.mk (α.f

Depends on / 依赖: IsLocallyPresentable, IsLocallyPresentable.exists_cardinal, LeftFraction, LeftFraction.map_comp_map_eq_m, LeftFraction.map_comp_map_eq_map, W.comp_mem, comp_mem, exists_cardinal, exists_leftFraction, map_comp_map_eq_m, map_comp_map_eq_map
-/
lemma comp_add' (f : L.obj X ⟶ L.obj Y) (g₁ g₂ : L.obj Y ⟶ L.obj Z) :
    f ≫ add' W g₁ g₂ = add' W (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨α, hα⟩ := exists_leftFraction L W f
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_leftFraction₂ L W g₁ g₂
  obtain ⟨γ, hγ₁, hγ₂⟩ := (RightFraction₂.mk _ α.hs β.f β.f').exists_leftFraction₂
  dsimp at hγ₁ hγ₂
  rw [add'_eq W g₁ g₂ β hβ₁ hβ₂]; rw [add'_eq W (f ≫ g₁) (f ≫ g₂)
    (LeftFraction₂.mk (α.f ≫ γ.f) (α.f ≫ γ.f') (β.s ≫ γ.s) (W.comp_mem _ _ β.hs γ.hs))
    (by simpa only [hα]; rw [hβ₁] using! LeftFraction.map_comp_map_eq_map α β.fst γ.fst hγ₁ L)
    (by simpa only [hα, hβ₂] using! LeftFraction.map_comp_map_eq_map α β.snd γ.snd hγ₂ L),
    hα, LeftFraction.map_comp_map_eq_map α β.add γ.add
      (by simp only [add_comp, hγ₁, hγ₂, comp_add])]
  dsimp [LeftFraction₂.add]
  rw [comp_add]

@[simp]
/--
lemma `add'_map` / 引理 `add'_map`

English:
lemma add'_map
  given: (f₁ f₂ : X ⟶ Y)
  proof: (add'_eq W (L.map f₁) (L.map f₂) (LeftFraction₂.mk f₁ f₂ (𝟙 _) (W.id_mem _))
    (LeftFraction.map_ofHom _ _ _ _).symm (LeftFraction.map_ofHom _ _ _ _).symm).trans
    (LeftFraction.map_ofHom _ _ _ _)

中文:
引理 add'_map
  条件: (f₁ f₂ : X ⟶ Y)
  证明: (add'_eq W (L.map f₁) (L.map f₂) (LeftFraction₂.mk f₁ f₂ (𝟙 _) (W.id_mem _))
    (LeftFraction.map_ofHom _ _ _ _).symm (LeftFraction.map_ofHom _ _ _ _).symm).trans
    (LeftFraction.map_ofHom _ _ _ _)
-/
lemma add'_map (f₁ f₂ : X ⟶ Y) :
    add' W (L.map f₁) (L.map f₂) = L.map (f₁ + f₂) :=
  (add'_eq W (L.map f₁) (L.map f₂) (LeftFraction₂.mk f₁ f₂ (𝟙 _) (W.id_mem _))
    (LeftFraction.map_ofHom _ _ _ _).symm (LeftFraction.map_ofHom _ _ _ _).symm).trans
    (LeftFraction.map_ofHom _ _ _ _)

variable (L X Y)

/-- The abelian group structure on `L.obj X ⟶ L.obj Y` when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/--
Definition of `addCommGroup'` / `addCommGroup'` 的定义

English:
definition addCommGroup'
  signature: : AddCommGroup (L.obj X ⟶ L.obj Y)
  body: by
  letI : Zero (L.obj X ⟶ L.obj Y) := ⟨L.map 0⟩
  letI : Add (L.obj X ⟶ L.obj Y) := ⟨add' W⟩
  letI : Neg (L.obj X ⟶ L.obj Y) := ⟨neg' W⟩
  exact
    { add_assoc := add'_assoc _
      add_zero := add'_zero _
      add_comm := add'_comm _
      zero_add := zero_add' _
      neg_add_cancel := neg'_a

中文:
定义 addCommGroup'
  签名: : AddCommGroup (L.obj X ⟶ L.obj Y)
  定义体: by
  letI : Zero (L.obj X ⟶ L.obj Y) := ⟨L.map 0⟩
  letI : Add (L.obj X ⟶ L.obj Y) := ⟨add' W⟩
  letI : Neg (L.obj X ⟶ L.obj Y) := ⟨neg' W⟩
  exact
    { add_assoc := add'_assoc _
      add_zero := add'_zero _
      add_comm := add'_comm _
      zero_add := zero_add' _
      neg_add_cancel := neg'_a

Depends on / 依赖: L.map, L.obj, _add, _assoc, _comm, _self, _zero, add_assoc, add_comm, add_zero, h.isCardinalPresentable, isCardinalPresentable, isCardinalPresentable_iff, neg_add_cancel, nsmulRec, zero_add, zsmulRec
-/
noncomputable def addCommGroup' : AddCommGroup (L.obj X ⟶ L.obj Y) := by
  letI : Zero (L.obj X ⟶ L.obj Y) := ⟨L.map 0⟩
  letI : Add (L.obj X ⟶ L.obj Y) := ⟨add' W⟩
  letI : Neg (L.obj X ⟶ L.obj Y) := ⟨neg' W⟩
  exact
    { add_assoc := add'_assoc _
      add_zero := add'_zero _
      add_comm := add'_comm _
      zero_add := zero_add' _
      neg_add_cancel := neg'_add'_self _
      nsmul := nsmulRec
      zsmul := zsmulRec }

variable {X Y}

variable {L}
variable {X' Y' Z' : D} (eX : L.obj X ≅ X') (eY : L.obj Y ≅ Y') (eZ : L.obj Z ≅ Z')

/-- The bijection `(X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y)` induced by isomorphisms
`eX : L.obj X ≅ X'` and `eY : L.obj Y ≅ Y'`. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where
  body: eX.hom ≫ f ≫ eY.inv
  invFun g := eX.inv ≫ g ≫ eY.hom
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 homEquiv
  签名: : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where
  定义体: eX.hom ≫ f ≫ eY.inv
  invFun g := eX.inv ≫ g ≫ eY.hom
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: eX.hom, eY.inv
-/
def homEquiv : (X' ⟶ Y') ≃ (L.obj X ⟶ L.obj Y) where
  toFun f := eX.hom ≫ f ≫ eY.inv
  invFun g := eX.inv ≫ g ≫ eY.hom
  left_inv _ := by simp
  right_inv _ := by simp

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (f₁ f₂ : X' ⟶ Y')
  body: (homEquiv eX eY).symm (add' W (homEquiv eX eY f₁) (homEquiv eX eY f₂))

@[reassoc]

中文:
定义 add
  签名: (f₁ f₂ : X' ⟶ Y')
  定义体: (homEquiv eX eY).symm (add' W (homEquiv eX eY f₁) (homEquiv eX eY f₂))

@[reassoc]

Depends on / 依赖: homEquiv
-/
noncomputable def add (f₁ f₂ : X' ⟶ Y') : X' ⟶ Y' :=
  (homEquiv eX eY).symm (add' W (homEquiv eX eY f₁) (homEquiv eX eY f₂))

@[reassoc]
/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  given: (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z')
  proof: by
  obtain ⟨g, rfl⟩ := (homEquiv eY eZ).symm.surjective g
  simp [add]

@[reassoc]

中文:
引理 add_comp
  条件: (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z')
  证明: by
  obtain ⟨g, rfl⟩ := (homEquiv eY eZ).symm.surjective g
  simp [add]

@[reassoc]

Depends on / 依赖: homEquiv, surjective, symm.surjective
-/
lemma add_comp (f₁ f₂ : X' ⟶ Y') (g : Y' ⟶ Z') :
    add W eX eY f₁ f₂ ≫ g = add W eX eZ (f₁ ≫ g) (f₂ ≫ g) := by
  obtain ⟨g, rfl⟩ := (homEquiv eY eZ).symm.surjective g
  simp [add]

@[reassoc]
/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  given: (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z')
  proof: by
  obtain ⟨f, rfl⟩ := (homEquiv eX eY).symm.surjective f
  simp [add]

中文:
引理 comp_add
  条件: (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z')
  证明: by
  obtain ⟨f, rfl⟩ := (homEquiv eX eY).symm.surjective f
  simp [add]

Depends on / 依赖: homEquiv, surjective, symm.surjective
-/
lemma comp_add (f : X' ⟶ Y') (g₁ g₂ : Y' ⟶ Z') :
    f ≫ add W eY eZ g₁ g₂ = add W eX eZ (f ≫ g₁) (f ≫ g₂) := by
  obtain ⟨f, rfl⟩ := (homEquiv eX eY).symm.surjective f
  simp [add]

/--
lemma `add_eq_add` / 引理 `add_eq_add`

English:
lemma add_eq_add
  statement: {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y')
  proof: by
  have h₁ := comp_add W eX' eX eY (𝟙 _) f₁ f₂
  have h₂ := add_comp W eX' eY eY' f₁ f₂ (𝟙 _)
  simp only [id_comp] at h₁
  simp only [comp_id] at h₂
  rw [h₁]; rw [h₂]

中文:
引理 add_eq_add
  结论: {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y')
  证明: by
  have h₁ := comp_add W eX' eX eY (𝟙 _) f₁ f₂
  have h₂ := add_comp W eX' eY eY' f₁ f₂ (𝟙 _)
  simp only [id_comp] at h₁
  simp only [comp_id] at h₂
  rw [h₁]; rw [h₂]

Depends on / 依赖: add_comp, comp_add, comp_id, id_comp
-/
lemma add_eq_add {X'' Y'' : C} (eX' : L.obj X'' ≅ X') (eY' : L.obj Y'' ≅ Y')
    (f₁ f₂ : X' ⟶ Y') :
    add W eX eY f₁ f₂ = add W eX' eY' f₁ f₂ := by
  have h₁ := comp_add W eX' eX eY (𝟙 _) f₁ f₂
  have h₂ := add_comp W eX' eY eY' f₁ f₂ (𝟙 _)
  simp only [id_comp] at h₁
  simp only [comp_id] at h₂
  rw [h₁]; rw [h₂]

variable (L X' Y') in
/-- The abelian group structure on morphisms in `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/--
Definition of `addCommGroup` / `addCommGroup` 的定义

English:
definition addCommGroup
  signature: : AddCommGroup (X' ⟶ Y')
  body: by
  have := Localization.essSurj L W
  letI := addCommGroup' L W (L.objPreimage X') (L.objPreimage Y')
  exact Equiv.addCommGroup (homEquiv (L.objObjPreimageIso X') (L.objObjPreimageIso Y'))

中文:
定义 addCommGroup
  签名: : AddCommGroup (X' ⟶ Y')
  定义体: by
  have := Localization.essSurj L W
  letI := addCommGroup' L W (L.objPreimage X') (L.objPreimage Y')
  exact Equiv.addCommGroup (homEquiv (L.objObjPreimageIso X') (L.objObjPreimageIso Y'))

Depends on / 依赖: Equiv.addCommGroup, L.objObjPreimageIso, L.objPreimage, Localization, Localization.essSurj, addCommGroup, essSurj, homEquiv, objObjPreimageIso, objPreimage
-/
noncomputable def addCommGroup : AddCommGroup (X' ⟶ Y') := by
  have := Localization.essSurj L W
  letI := addCommGroup' L W (L.objPreimage X') (L.objPreimage Y')
  exact Equiv.addCommGroup (homEquiv (L.objObjPreimageIso X') (L.objObjPreimageIso Y'))

/--
lemma `add_eq` / 引理 `add_eq`

English:
lemma add_eq
  given: (f₁ f₂ : X' ⟶ Y')
  proof: addCommGroup L W X' Y'
    f₁ + f₂ = add W eX eY f₁ f₂ := by
  apply add_eq_add

中文:
引理 add_eq
  条件: (f₁ f₂ : X' ⟶ Y')
  证明: addCommGroup L W X' Y'
    f₁ + f₂ = add W eX eY f₁ f₂ := by
  apply add_eq_add

Depends on / 依赖: addCommGroup
-/
lemma add_eq (f₁ f₂ : X' ⟶ Y') :
    letI := addCommGroup L W X' Y'
    f₁ + f₂ = add W eX eY f₁ f₂ := by
  apply add_eq_add

variable (L)

/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: (f₁ f₂ : X ⟶ Y)
  proof: addCommGroup L W (L.obj X) (L.obj Y)
    L.map (f₁ + f₂) = L.map f₁ + L.map f₂ := by
  rw [add_eq W (Iso.refl _) (Iso.refl _) (L.map f₁) (L.map f₂)]
  simp [add]

中文:
引理 map_add
  条件: (f₁ f₂ : X ⟶ Y)
  证明: addCommGroup L W (L.obj X) (L.obj Y)
    L.map (f₁ + f₂) = L.map f₁ + L.map f₂ := by
  rw [add_eq W (Iso.refl _) (Iso.refl _) (L.map f₁) (L.map f₂)]
  simp [add]

Depends on / 依赖: L.obj, addCommGroup
-/
lemma map_add (f₁ f₂ : X ⟶ Y) :
    letI := addCommGroup L W (L.obj X) (L.obj Y)
    L.map (f₁ + f₂) = L.map f₁ + L.map f₂ := by
  rw [add_eq W (Iso.refl _) (Iso.refl _) (L.map f₁) (L.map f₂)]
  simp [add]

end ImplementationDetails

end Preadditive

variable [W.HasLeftCalculusOfFractions]

/-- The preadditive structure on `D`, when `L : C ⥤ D` is a localization
functor, `C` is preadditive and there is a left calculus of fractions. -/
@[instance_reducible]
/--
Definition of `preadditive` / `preadditive` 的定义

English:
definition preadditive
  signature: : Preadditive D where
  body: Preadditive.addCommGroup L W
  add_comp _ _ _ _ _ _ := by apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by apply Preadditive.comp_add

中文:
定义 preadditive
  签名: : Preadditive D where
  定义体: Preadditive.addCommGroup L W
  add_comp _ _ _ _ _ _ := by apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by apply Preadditive.comp_add

Depends on / 依赖: Preadditive, Preadditive.addCommGroup, addCommGroup
-/
noncomputable def preadditive : Preadditive D where
  homGroup := Preadditive.addCommGroup L W
  add_comp _ _ _ _ _ _ := by apply Preadditive.add_comp
  comp_add _ _ _ _ _ _ := by apply Preadditive.comp_add

/--
lemma `functor_additive` / 引理 `functor_additive`

English:
lemma functor_additive
  proof: preadditive L W
    L.Additive :=
  letI := preadditive L W
  ⟨by apply Preadditive.map_add⟩

中文:
引理 functor_additive
  证明: preadditive L W
    L.Additive :=
  letI := preadditive L W
  ⟨by apply Preadditive.map_add⟩

Depends on / 依赖: preadditive
-/
lemma functor_additive :
    letI := preadditive L W
    L.Additive :=
  letI := preadditive L W
  ⟨by apply Preadditive.map_add⟩

attribute [irreducible] preadditive

set_option backward.isDefEq.respectTransparency false in
include W in
/--
lemma `functor_additive_iff` / 引理 `functor_additive_iff`

English:
lemma functor_additive_iff
  statement: {E : Type*} [Category* E] [Preadditive E] [Preadditive D] [L.Additive]
  proof: by
  constructor
  · intro
    infer_instance
  · intro h
    suffices forall ⦃X Y : C⦄ (f g : L.obj X ⟶ L.obj Y), G.map (f + g) = G.map f + G.map g by
      refine ⟨fun {X Y f g} => ?_⟩
      have hL := essSurj L W
      have eq := this ((L.objObjPreimageIso X).hom ≫ f ≫ (L.objObjPreimageIso Y).inv

中文:
引理 functor_additive_iff
  结论: {E : 类型} [Category* E] [Preadditive E] [Preadditive D] [L.Additive]
  证明: by
  constructor
  · intro
    infer_instance
  · intro h
    suffices forall ⦃X Y : C⦄ (f g : L.obj X ⟶ L.obj Y), G.map (f + g) = G.map f + G.map g by
      refine ⟨fun {X Y f g} => ?_⟩
      have hL := essSurj L W
      have eq := this ((L.objObjPreimageIso X).hom ≫ f ≫ (L.objObjPreimageIso Y).inv

Depends on / 依赖: Functor, Functor.map_comp, G.map, L.obj, L.objObjPreimageIso, add_comp, comp_add, essSurj, infer_instance, map_comp, objObjPreimageIso
-/
lemma functor_additive_iff {E : Type*} [Category* E] [Preadditive E] [Preadditive D] [L.Additive]
    (G : D ⥤ E) :
    G.Additive ↔ (L ⋙ G).Additive := by
  constructor
  · intro
    infer_instance
  · intro h
    suffices forall ⦃X Y : C⦄ (f g : L.obj X ⟶ L.obj Y), G.map (f + g) = G.map f + G.map g by
      refine ⟨fun {X Y f g} => ?_⟩
      have hL := essSurj L W
      have eq := this ((L.objObjPreimageIso X).hom ≫ f ≫ (L.objObjPreimageIso Y).inv)
        ((L.objObjPreimageIso X).hom ≫ g ≫ (L.objObjPreimageIso Y).inv)
      rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [← comp_add]; rw [← comp_add]; rw [← add_comp]; rw [← add_comp]; rw [Functor.map_comp]; rw [Functor.map_comp] at eq
      rw [← cancel_mono (G.map (L.objObjPreimageIso Y).inv)]; rw [← cancel_epi (G.map (L.objObjPreimageIso X).hom)]; rw [eq]
    intro X Y f g
    obtain ⟨φ, rfl, rfl⟩ := exists_leftFraction₂ L W f g
    rw [← φ.map_add L (inverts L W)]; rw [← cancel_mono (G.map (L.map φ.s))]; rw [← G.map_comp]; rw [add_comp]; rw [← G.map_comp]; rw [← G.map_comp]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [LeftFraction.map_comp_map_s]; rw [← Functor.comp_map]; rw [Functor.map_add]; rw [Functor.comp_map]; rw [Functor.comp_map]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive W.Localization
  body: preadditive W.Q W

中文:
实例 :
  签名: Preadditive W.Localization
  定义体: preadditive W.Q W

Depends on / 依赖: preadditive
-/
noncomputable instance : Preadditive W.Localization := preadditive W.Q W
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.Q.Additive
  body: functor_additive W.Q W

中文:
实例 :
  签名: W.Q.Additive
  定义体: functor_additive W.Q W

Depends on / 依赖: functor_additive
-/
instance : W.Q.Additive := functor_additive W.Q W
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : HasZeroObject W.Localization
  body: W.Q.hasZeroObject_of_additive

中文:
实例 [HasZeroObject
  签名: C] : HasZeroObject W.Localization
  定义体: W.Q.hasZeroObject_of_additive

Depends on / 依赖: W.Q.hasZeroObject_of_additive, hasZeroObject_of_additive
-/
instance [HasZeroObject C] : HasZeroObject W.Localization := W.Q.hasZeroObject_of_additive

variable [W.HasLocalization]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive W.Localization'
  body: preadditive W.Q' W

中文:
实例 :
  签名: Preadditive W.Localization'
  定义体: preadditive W.Q' W

Depends on / 依赖: preadditive
-/
noncomputable instance : Preadditive W.Localization' := preadditive W.Q' W
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.Q'.Additive
  body: functor_additive W.Q' W

中文:
实例 :
  签名: W.Q'.Additive
  定义体: functor_additive W.Q' W

Depends on / 依赖: functor_additive
-/
instance : W.Q'.Additive := functor_additive W.Q' W
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : HasZeroObject W.Localization'
  body: W.Q'.hasZeroObject_of_additive

中文:
实例 [HasZeroObject
  签名: C] : HasZeroObject W.Localization'
  定义体: W.Q'.hasZeroObject_of_additive

Depends on / 依赖: hasZeroObject_of_additive
-/
instance [HasZeroObject C] : HasZeroObject W.Localization' := W.Q'.hasZeroObject_of_additive

end Localization

/--
lemma `Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions` / 引理 `Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions`

English:
lemma Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions
  proof: faithful_of_comp_of_hasLeftCalculusOfFractions L W F
    (fun X₁ X₂ f g hfg => by
      rw [← sub_eq_zero]; rw [← L.map_sub]
      exact h _ (by rw [L.map_sub, F.map_sub, hfg, sub_self]))

中文:
引理 Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions
  证明: faithful_of_comp_of_hasLeftCalculusOfFractions L W F
    (fun X₁ X₂ f g hfg => by
      rw [← sub_eq_zero]; rw [← L.map_sub]
      exact h _ (by rw [L.map_sub, F.map_sub, hfg, sub_self]))

Depends on / 依赖: F.map_sub, HasCardinalLT, HasCardinalLT.exists_regular_cardinal, IsRegular, L.map_sub, exists_regular_cardinal, faithful_of_comp_of_hasLeftCalculusOfFractions, hX.isCardinalPresentable, isCardinalPresentable, isPresentable_of_isCardinalPresentable, map_sub, sub_eq_zero, sub_self
-/
lemma Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions
    {E : Type*} [Category* E] (F : D ⥤ E)
    [W.HasLeftCalculusOfFractions]
    [Preadditive D] [Preadditive E] [L.Additive] [F.Additive]
    (h : forall ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂), F.map (L.map f) = 0 -> L.map f = 0) :
    Faithful F :=
  faithful_of_comp_of_hasLeftCalculusOfFractions L W F
    (fun X₁ X₂ f g hfg => by
      rw [← sub_eq_zero]; rw [← L.map_sub]
      exact h _ (by rw [L.map_sub, F.map_sub, hfg, sub_self]))

end CategoryTheory
