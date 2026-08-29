/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Factoring through subobjects

The predicate `h : P.Factors f`, for `P : Subobject Y` and `f : X ⟶ Y`
asserts the existence of some `P.factorThru f : X ⟶ (P : C)` making the obvious diagram commute.

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

/--
Definition of `Factors` / `Factors` 的定义

English:
definition Factors
  signature: {X Y : C} (P : MonoOver Y) (f : X ⟶ Y)
  body: exists g : X ⟶ (P : C), g ≫ P.arrow = f

中文:
定义 Factors
  签名: {X Y : C} (P : MonoOver Y) (f : X ⟶ Y)
  定义体: exists g : X ⟶ (P : C), g ≫ P.arrow = f

Depends on / 依赖: P.arrow
-/
def Factors {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) : Prop :=
  exists g : X ⟶ (P : C), g ≫ P.arrow = f

/--
theorem `factors_congr` / 定理 `factors_congr`

English:
theorem factors_congr
  given: {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g)
  proof: ⟨fun ⟨u, hu⟩ => ⟨u ≫ ((MonoOver.forget _).map e.hom).left, by simp [hu]⟩, fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by simp [hu]⟩⟩

中文:
定理 factors_congr
  条件: {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g)
  证明: ⟨fun ⟨u, hu⟩ => ⟨u ≫ ((MonoOver.forget _).map e.hom).left, by simp [hu]⟩, fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by simp [hu]⟩⟩

Depends on / 依赖: MonoOver, MonoOver.forget, e.hom, e.inv, forget
-/
theorem factors_congr {X : C} {f g : MonoOver X} {Y : C} (h : Y ⟶ X) (e : f ≅ g) :
    f.Factors h ↔ g.Factors h :=
  ⟨fun ⟨u, hu⟩ => ⟨u ≫ ((MonoOver.forget _).map e.hom).left, by simp [hu]⟩, fun ⟨u, hu⟩ =>
    ⟨u ≫ ((MonoOver.forget _).map e.inv).left, by simp [hu]⟩⟩

/--
Definition of `factorThru` / `factorThru` 的定义

English:
definition factorThru
  signature: {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f)
  body: Classical.choose h

中文:
定义 factorThru
  签名: {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def factorThru {X Y : C} (P : MonoOver Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ (P : C) :=
  Classical.choose h

end MonoOver

namespace Subobject

/--
Definition of `Factors` / `Factors` 的定义

English:
definition Factors
  signature: {X Y : C} (P : Subobject Y) (f : X ⟶ Y)
  body: Quotient.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.hom.hom.left, by rw [Category.assoc, Over.w h.hom.hom, w]⟩
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.inv.hom.left, by rw [Category.assoc, Over.w h.inv.hom, w]⟩)

@[simp]

中文:
定义 Factors
  签名: {X Y : C} (P : Subobject Y) (f : X ⟶ Y)
  定义体: Quotient.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.hom.hom.left, by rw [Category.assoc, Over.w h.hom.hom, w]⟩
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.inv.hom.left, by rw [Category.assoc, Over.w h.inv.hom, w]⟩)

@[simp]

Depends on / 依赖: Category, Category.assoc, Factors, Over.w, P.Factors, Quotient, Quotient.liftOn, h.hom.hom, h.hom.hom.left, h.inv.hom, h.inv.hom.left, liftOn, propext
-/
def Factors {X Y : C} (P : Subobject Y) (f : X ⟶ Y) : Prop :=
  Quotient.liftOn' P (fun P => P.Factors f)
    (by
      rintro P Q ⟨h⟩
      apply propext
      constructor
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.hom.hom.left, by rw [Category.assoc, Over.w h.hom.hom, w]⟩
      · rintro ⟨i, w⟩
        exact ⟨i ≫ h.inv.hom.left, by rw [Category.assoc, Over.w h.inv.hom, w]⟩)

@[simp]
/--
theorem `mk_factors_iff` / 定理 `mk_factors_iff`

English:
theorem mk_factors_iff
  given: {X Y Z : C} (f : Y ⟶ X) [Mono f] (g : Z ⟶ X)
  proof: Iff.rfl

中文:
定理 mk_factors_iff
  条件: {X Y Z : C} (f : Y ⟶ X) [单态射 f] (g : Z ⟶ X)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_factors_iff {X Y Z : C} (f : Y ⟶ X) [Mono f] (g : Z ⟶ X) :
    (Subobject.mk f).Factors g ↔ (MonoOver.mk f).Factors g :=
  Iff.rfl

/--
theorem `mk_factors_self` / 定理 `mk_factors_self`

English:
theorem mk_factors_self
  given: (f : X ⟶ Y) [Mono f]
  statement: (mk f).Factors f
  proof: ⟨𝟙 _, by simp⟩

中文:
定理 mk_factors_self
  条件: (f : X ⟶ Y) [单态射 f]
  结论: (mk f).Factors f
  证明: ⟨𝟙 _, by simp⟩
-/
theorem mk_factors_self (f : X ⟶ Y) [Mono f] : (mk f).Factors f :=
  ⟨𝟙 _, by simp⟩

/--
theorem `factors_iff` / 定理 `factors_iff`

English:
theorem factors_iff
  given: {X Y : C} (P : Subobject Y) (f : X ⟶ Y)
  proof: Quot.inductionOn P fun _ => MonoOver.factors_congr _ (representativeIso _).symm

中文:
定理 factors_iff
  条件: {X Y : C} (P : Subobject Y) (f : X ⟶ Y)
  证明: Quot.inductionOn P fun _ => MonoOver.factors_congr _ (representativeIso _).symm

Depends on / 依赖: MonoOver, MonoOver.factors_congr, Quot.inductionOn, factors_congr, inductionOn, representativeIso
-/
theorem factors_iff {X Y : C} (P : Subobject Y) (f : X ⟶ Y) :
    P.Factors f ↔ (representative.obj P).Factors f :=
  Quot.inductionOn P fun _ => MonoOver.factors_congr _ (representativeIso _).symm

/--
theorem `factors_self` / 定理 `factors_self`

English:
theorem factors_self
  given: {X : C} (P : Subobject X)
  statement: P.Factors P.arrow
  proof: (factors_iff _ _).mpr ⟨𝟙 (P : C), by simp⟩

中文:
定理 factors_self
  条件: {X : C} (P : Subobject X)
  结论: P.Factors P.arrow
  证明: (factors_iff _ _).mpr ⟨𝟙 (P : C), by simp⟩

Depends on / 依赖: factors_iff
-/
theorem factors_self {X : C} (P : Subobject X) : P.Factors P.arrow :=
  (factors_iff _ _).mpr ⟨𝟙 (P : C), by simp⟩

/--
theorem `factors_comp_arrow` / 定理 `factors_comp_arrow`

English:
theorem factors_comp_arrow
  given: {X Y : C} {P : Subobject Y} (f : X ⟶ P)
  statement: P.Factors (f ≫ P.arrow)
  proof: (factors_iff _ _).mpr ⟨f, rfl⟩

中文:
定理 factors_comp_arrow
  条件: {X Y : C} {P : Subobject Y} (f : X ⟶ P)
  结论: P.Factors (f ≫ P.arrow)
  证明: (factors_iff _ _).mpr ⟨f, rfl⟩

Depends on / 依赖: factors_iff
-/
theorem factors_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) : P.Factors (f ≫ P.arrow) :=
  (factors_iff _ _).mpr ⟨f, rfl⟩

/--
theorem `factors_of_factors_right` / 定理 `factors_of_factors_right`

English:
theorem factors_of_factors_right
  statement: {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
  proof: by
  induction P using Quotient.ind'
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ≫ g, by simp⟩

中文:
定理 factors_of_factors_right
  结论: {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
  证明: by
  induction P using Quotient.ind'
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ≫ g, by simp⟩

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem factors_of_factors_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) {g : Y ⟶ Z}
    (h : P.Factors g) : P.Factors (f ≫ g) := by
  induction P using Quotient.ind'
  obtain ⟨g, rfl⟩ := h
  exact ⟨f ≫ g, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factors_zero` / 定理 `factors_zero`

English:
theorem factors_zero
  given: [HasZeroMorphisms C] {X Y : C} {P : Subobject Y}
  statement: P.Factors (0 : X ⟶ Y)
  proof: (factors_iff _ _).mpr ⟨0, by simp⟩

中文:
定理 factors_zero
  条件: [有ZeroMorphisms C] {X Y : C} {P : Subobject Y}
  结论: P.Factors (0 : X ⟶ Y)
  证明: (factors_iff _ _).mpr ⟨0, by simp⟩

Depends on / 依赖: factors_iff
-/
theorem factors_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} : P.Factors (0 : X ⟶ Y) :=
  (factors_iff _ _).mpr ⟨0, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `factors_of_le` / 定理 `factors_of_le`

English:
theorem factors_of_le
  given: {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P <= Q)
  proof: by
  simp only [factors_iff]
  exact fun ⟨u, hu⟩ => ⟨u ≫ ofLE _ _ h, by simp [← hu]⟩

中文:
定理 factors_of_le
  条件: {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P <= Q)
  证明: by
  simp only [factors_iff]
  exact fun ⟨u, hu⟩ => ⟨u ≫ ofLE _ _ h, by simp [← hu]⟩

Depends on / 依赖: factors_iff
-/
theorem factors_of_le {Y Z : C} {P Q : Subobject Y} (f : Z ⟶ Y) (h : P <= Q) :
    P.Factors f -> Q.Factors f := by
  simp only [factors_iff]
  exact fun ⟨u, hu⟩ => ⟨u ≫ ofLE _ _ h, by simp [← hu]⟩

/--
Definition of `factorThru` / `factorThru` 的定义

English:
definition factorThru
  signature: {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f)
  body: Classical.choose ((factors_iff _ _).mp h)

@[reassoc (attr := simp)]

中文:
定义 factorThru
  签名: {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f)
  定义体: Classical.choose ((factors_iff _ _).mp h)

@[reassoc (attr := simp)]

Depends on / 依赖: Classical, Classical.choose, factors_iff
-/
def factorThru {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) : X ⟶ P :=
  Classical.choose ((factors_iff _ _).mp h)

@[reassoc (attr := simp)]
/--
theorem `factorThru_arrow` / 定理 `factorThru_arrow`

English:
theorem factorThru_arrow
  given: {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f)
  proof: Classical.choose_spec ((factors_iff _ _).mp h)

@[simp]

中文:
定理 factorThru_arrow
  条件: {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f)
  证明: Classical.choose_spec ((factors_iff _ _).mp h)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, factors_iff
-/
theorem factorThru_arrow {X Y : C} (P : Subobject Y) (f : X ⟶ Y) (h : Factors P f) :
    P.factorThru f h ≫ P.arrow = f :=
  Classical.choose_spec ((factors_iff _ _).mp h)

@[simp]
/--
theorem `factorThru_self` / 定理 `factorThru_self`

English:
theorem factorThru_self
  given: {X : C} (P : Subobject X) (h)
  statement: P.factorThru P.arrow h = 𝟙 (P : C)
  proof: by
  ext
  simp

@[simp]

中文:
定理 factorThru_self
  条件: {X : C} (P : Subobject X) (h)
  结论: P.factorThru P.arrow h = 𝟙 (P : C)
  证明: by
  ext
  simp

@[simp]
-/
theorem factorThru_self {X : C} (P : Subobject X) (h) : P.factorThru P.arrow h = 𝟙 (P : C) := by
  ext
  simp

@[simp]
/--
theorem `factorThru_mk_self` / 定理 `factorThru_mk_self`

English:
theorem factorThru_mk_self
  given: (f : X ⟶ Y) [Mono f]
  proof: by
  ext
  simp

@[simp]

中文:
定理 factorThru_mk_self
  条件: (f : X ⟶ Y) [单态射 f]
  证明: by
  ext
  simp

@[simp]
-/
theorem factorThru_mk_self (f : X ⟶ Y) [Mono f] :
    (mk f).factorThru f (mk_factors_self f) = (underlyingIso f).inv := by
  ext
  simp

@[simp]
/--
theorem `factorThru_comp_arrow` / 定理 `factorThru_comp_arrow`

English:
theorem factorThru_comp_arrow
  given: {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h)
  proof: by
  ext
  simp

@[simp]

中文:
定理 factorThru_comp_arrow
  条件: {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h)
  证明: by
  ext
  simp

@[simp]
-/
theorem factorThru_comp_arrow {X Y : C} {P : Subobject Y} (f : X ⟶ P) (h) :
    P.factorThru (f ≫ P.arrow) h = f := by
  ext
  simp

@[simp]
/--
theorem `factorThru_eq_zero` / 定理 `factorThru_eq_zero`

English:
theorem factorThru_eq_zero
  statement: [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y}
  proof: by
  fconstructor
  · intro w
    replace w := w =≫ P.arrow
    simpa using w
  · rintro rfl
    ext
    simp

中文:
定理 factorThru_eq_zero
  结论: [有ZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y}
  证明: by
  fconstructor
  · intro w
    replace w := w =≫ P.arrow
    simpa using w
  · rintro rfl
    ext
    simp

Depends on / 依赖: P.arrow, fconstructor, replace
-/
theorem factorThru_eq_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y} {f : X ⟶ Y}
    {h : Factors P f} : P.factorThru f h = 0 ↔ f = 0 := by
  fconstructor
  · intro w
    replace w := w =≫ P.arrow
    simpa using w
  · rintro rfl
    ext
    simp

/--
theorem `factorThru_right` / 定理 `factorThru_right`

English:
theorem factorThru_right
  given: {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g)
  proof: by
  apply (cancel_mono P.arrow).mp
  simp

@[simp]

中文:
定理 factorThru_right
  条件: {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g)
  证明: by
  apply (cancel_mono P.arrow).mp
  simp

@[simp]

Depends on / 依赖: P.arrow, cancel_mono
-/
theorem factorThru_right {X Y Z : C} {P : Subobject Z} (f : X ⟶ Y) (g : Y ⟶ Z) (h : P.Factors g) :
    f ≫ P.factorThru g h = P.factorThru (f ≫ g) (factors_of_factors_right f h) := by
  apply (cancel_mono P.arrow).mp
  simp

@[simp]
/--
theorem `factorThru_zero` / 定理 `factorThru_zero`

English:
theorem factorThru_zero
  statement: [HasZeroMorphisms C] {X Y : C} {P : Subobject Y}
  proof: by simp

中文:
定理 factorThru_zero
  结论: [有ZeroMorphisms C] {X Y : C} {P : Subobject Y}
  证明: by simp
-/
theorem factorThru_zero [HasZeroMorphisms C] {X Y : C} {P : Subobject Y}
    (h : P.Factors (0 : X ⟶ Y)) : P.factorThru 0 h = 0 := by simp

-- `h` is an explicit argument here so we can use
-- `rw factorThru_ofLE h`, obtaining a subgoal `P.Factors f`.
-- (While the reverse direction looks plausible as a simp lemma, it seems to be unproductive.)
/--
theorem `factorThru_ofLE` / 定理 `factorThru_ofLE`

English:
theorem factorThru_ofLE
  given: {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P <= Q) (w : P.Factors f)
  proof: by
  ext
  simp

中文:
定理 factorThru_ofLE
  条件: {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P <= Q) (w : P.Factors f)
  证明: by
  ext
  simp
-/
theorem factorThru_ofLE {Y Z : C} {P Q : Subobject Y} {f : Z ⟶ Y} (h : P <= Q) (w : P.Factors f) :
    Q.factorThru f (factors_of_le f h w) = P.factorThru f w ≫ ofLE P Q h := by
  ext
  simp

/--
theorem `le_of_factors` / 定理 `le_of_factors`

English:
theorem le_of_factors
  given: {P Q : Subobject Y} (h : Q.Factors P.arrow)
  statement: P <= Q
  proof: le_of_comm (Q.factorThru P.arrow h) (Q.factorThru_arrow P.arrow h)

中文:
定理 le_of_factors
  条件: {P Q : Subobject Y} (h : Q.Factors P.arrow)
  结论: P <= Q
  证明: le_of_comm (Q.factorThru P.arrow h) (Q.factorThru_arrow P.arrow h)

Depends on / 依赖: P.arrow, Q.factorThru, Q.factorThru_arrow, factorThru, factorThru_arrow, le_of_comm
-/
theorem le_of_factors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P <= Q :=
  le_of_comm (Q.factorThru P.arrow h) (Q.factorThru_arrow P.arrow h)

/--
Definition of `homOfFactors` / `homOfFactors` 的定义

English:
definition homOfFactors
  signature: {P Q : Subobject Y} (h : Q.Factors P.arrow)
  body: homOfLE le_of_factors h

中文:
定义 homOfFactors
  签名: {P Q : Subobject Y} (h : Q.Factors P.arrow)
  定义体: homOfLE le_of_factors h

Depends on / 依赖: homOfLE, le_of_factors
-/
def homOfFactors {P Q : Subobject Y} (h : Q.Factors P.arrow) : P ⟶ Q :=
homOfLE le_of_factors h

section Preadditive

variable [Preadditive C]

/--
theorem `factors_add` / 定理 `factors_add`

English:
theorem factors_add
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f)
  proof: (factors_iff _ _).mpr ⟨P.factorThru f wf + P.factorThru g wg, by simp⟩

中文:
定理 factors_add
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f)
  证明: (factors_iff _ _).mpr ⟨P.factorThru f wf + P.factorThru g wg, by simp⟩

Depends on / 依赖: P.factorThru, factorThru, factors_iff
-/
theorem factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (wf : P.Factors f)
    (wg : P.Factors g) : P.Factors (f + g) :=
  (factors_iff _ _).mpr ⟨P.factorThru f wf + P.factorThru g wg, by simp⟩

-- This can't be a `simp` lemma as `wf` and `wg` may not exist.
-- However you can `rw` by it to assert that `f` and `g` factor through `P` separately.
/--
theorem `factorThru_add` / 定理 `factorThru_add`

English:
theorem factorThru_add
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
  proof: by
  ext
  simp

中文:
定理 factorThru_add
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
  证明: by
  ext
  simp
-/
theorem factorThru_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y) (w : P.Factors (f + g))
    (wf : P.Factors f) (wg : P.Factors g) :
    P.factorThru (f + g) w = P.factorThru f wf + P.factorThru g wg := by
  ext
  simp

/--
theorem `factors_left_of_factors_add` / 定理 `factors_left_of_factors_add`

English:
theorem factors_left_of_factors_add
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  proof: (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru g wg, by simp⟩

@[simp]

中文:
定理 factors_left_of_factors_add
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  证明: (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru g wg, by simp⟩

@[simp]

Depends on / 依赖: P.factorThru, factorThru, factors_iff
-/
theorem factors_left_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wg : P.Factors g) : P.Factors f :=
  (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru g wg, by simp⟩

@[simp]
/--
theorem `factorThru_add_sub_factorThru_right` / 定理 `factorThru_add_sub_factorThru_right`

English:
theorem factorThru_add_sub_factorThru_right
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  proof: by
  ext
  simp

中文:
定理 factorThru_add_sub_factorThru_right
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  证明: by
  ext
  simp
-/
theorem factorThru_add_sub_factorThru_right {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wg : P.Factors g) :
    P.factorThru (f + g) w - P.factorThru g wg =
      P.factorThru f (factors_left_of_factors_add f g w wg) := by
  ext
  simp

/--
theorem `factors_right_of_factors_add` / 定理 `factors_right_of_factors_add`

English:
theorem factors_right_of_factors_add
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  proof: (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru f wf, by simp⟩

@[simp]

中文:
定理 factors_right_of_factors_add
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  证明: (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru f wf, by simp⟩

@[simp]

Depends on / 依赖: P.factorThru, factorThru, factors_iff
-/
theorem factors_right_of_factors_add {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wf : P.Factors f) : P.Factors g :=
  (factors_iff _ _).mpr ⟨P.factorThru (f + g) w - P.factorThru f wf, by simp⟩

@[simp]
/--
theorem `factorThru_add_sub_factorThru_left` / 定理 `factorThru_add_sub_factorThru_left`

English:
theorem factorThru_add_sub_factorThru_left
  statement: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  proof: by
  ext
  simp

中文:
定理 factorThru_add_sub_factorThru_left
  结论: {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
  证明: by
  ext
  simp
-/
theorem factorThru_add_sub_factorThru_left {X Y : C} {P : Subobject Y} (f g : X ⟶ Y)
    (w : P.Factors (f + g)) (wf : P.Factors f) :
    P.factorThru (f + g) w - P.factorThru f wf =
      P.factorThru g (factors_right_of_factors_add f g w wf) := by
  ext
  simp

end Preadditive

end Subobject

end CategoryTheory
