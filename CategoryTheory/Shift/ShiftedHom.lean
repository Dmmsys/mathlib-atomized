/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Shifted morphisms

Given a category `C` endowed with a shift by an additive monoid `M` and two
objects `X` and `Y` in `C`, we consider the types `ShiftedHom X Y m`
defined as `X ⟶ Y⟦m⟧` for all `m : M`, and the composition on these
shifted hom.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

/--
Definition of `ShiftedHom` / `ShiftedHom` 的定义

English:
abbreviation ShiftedHom
  signature: (X Y : C) (m : M)
  body: X ⟶ Y⟦m⟧

中文:
缩写 ShiftedHom
  签名: (X Y : C) (m : M)
  定义体: X ⟶ Y⟦m⟧
-/
abbrev ShiftedHom (X Y : C) (m : M) : Type _ := X ⟶ Y⟦m⟧

namespace ShiftedHom

variable {X Y Z T : C}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c)
  body: f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

中文:
定义 comp
  签名: {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c)
  定义体: f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

Depends on / 依赖: inv.app, shiftFunctorAdd
-/
noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom X Z c :=
  f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
  proof: by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

中文:
引理 comp_assoc
  结论: {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
  证明: by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

Depends on / 依赖: Functor, Functor.comp_map, Functor.map_comp, NatTrans, NatTrans.naturality_assoc, _assoc_inv_app, comp_map, map_comp, naturality_assoc, shiftFunctorAdd
-/
lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    (α : ShiftedHom X Y a₁) (β : ShiftedHom Y Z a₂) (γ : ShiftedHom Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

/-! In degree `0 : M`, shifted hom `ShiftedHom X Y 0` identify to morphisms `X ⟶ Y`.
We generalize this to `m₀ : M` such that `m₀ : 0` as it shall be convenient when we
apply this with `M := ℤ` and `m₀` the coercion of `0 : ℕ`. -/

/--
Definition of `mk₀` / `mk₀` 的定义

English:
definition mk₀
  signature: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y)
  body: f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

中文:
定义 mk₀
  签名: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y)
  定义体: f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

Depends on / 依赖: inv.app, shiftFunctorZero
-/
noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) : ShiftedHom X Y m₀ :=
  f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

/-- The bijection `(X ⟶ Y) ≃ ShiftedHom X Y m₀` when `m₀ = 0`. -/
@[simps apply]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: (m₀ : M) (hm₀ : m₀ = 0)
  body: mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]

中文:
定义 homEquiv
  签名: (m₀ : M) (hm₀ : m₀ = 0)
  定义体: mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]
-/
noncomputable def homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where
  toFun f := mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]

/--
lemma `mk₀_comp` / 引理 `mk₀_comp`

English:
lemma mk₀_comp
  given: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a)
  proof: by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]

中文:
引理 mk₀_comp
  条件: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a)
  证明: by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]

Depends on / 依赖: _add_zero_inv_app, shiftFunctorAdd, shiftFunctorZero
-/
lemma mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) :
    (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add_zero]) = f ≫ g := by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]
/--
lemma `mk₀_id_comp` / 引理 `mk₀_id_comp`

English:
lemma mk₀_id_comp
  given: (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a)
  proof: by
  simp [mk₀_comp]

中文:
引理 mk₀_id_comp
  条件: (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a)
  证明: by
  simp [mk₀_comp]
-/
lemma mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_zero]) = f := by
  simp [mk₀_comp]

/--
lemma `comp_mk₀` / 引理 `comp_mk₀`

English:
lemma comp_mk₀
  given: {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z)
  proof: by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]

中文:
引理 comp_mk₀
  条件: {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z)
  证明: by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]

Depends on / 依赖: Functor, Functor.id_obj, Functor.map_comp, Iso.inv_hom_id_app, Iso.refl_trans, _zero_add_inv_app, comp_id, eqToIso_refl, id_obj, inv_hom_id_app, map_comp, refl_trans, shiftFunctorAdd, shiftFunctorZero
-/
lemma comp_mk₀ {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zero_add]) = f ≫ g⟦a⟧' := by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]
/--
lemma `comp_mk₀_id` / 引理 `comp_mk₀_id`

English:
lemma comp_mk₀_id
  given: {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0)
  proof: by
  simp [comp_mk₀]

@[simp]

中文:
引理 comp_mk₀_id
  条件: {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0)
  证明: by
  simp [comp_mk₀]

@[simp]
-/
lemma comp_mk₀_id {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) :
    f.comp (mk₀ m₀ hm₀ (𝟙 Y)) (by rw [hm₀, zero_add]) = f := by
  simp [comp_mk₀]

@[simp]
/--
lemma `mk₀_comp_mk₀` / 引理 `mk₀_comp_mk₀`

English:
lemma mk₀_comp_mk₀
  statement: (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
  proof: by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp]; rw [mk₀]; rw [mk₀]; rw [assoc]

@[simp]

中文:
引理 mk₀_comp_mk₀
  结论: (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
  证明: by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp]; rw [mk₀]; rw [mk₀]; rw [assoc]

@[simp]

Depends on / 依赖: zero_add
-/
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
    (ha : a = 0) (hb : b = 0) :
    (mk₀ a ha f).comp (mk₀ b hb g) h = mk₀ c (by rw [← h, ha, hb, add_zero]) (f ≫ g) := by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp]; rw [mk₀]; rw [mk₀]; rw [assoc]

@[simp]
/--
lemma `mk₀_comp_mk₀_assoc` / 引理 `mk₀_comp_mk₀_assoc`

English:
lemma mk₀_comp_mk₀_assoc
  statement: (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
  proof: by
  subst ha
  rw [← comp_assoc]; rw [mk₀_comp_mk₀]
  all_goals simp

中文:
引理 mk₀_comp_mk₀_assoc
  结论: (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
  证明: by
  subst ha
  rw [← comp_assoc]; rw [mk₀_comp_mk₀]
  all_goals simp

Depends on / 依赖: all_goals, comp_assoc
-/
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
    (ha : a = 0) {d : M} (h : ShiftedHom Z T d) :
    (mk₀ a ha f).comp ((mk₀ a ha g).comp h
        (show _ = d by rw [ha, add_zero])) (show _ = d by rw [ha, add_zero]) =
      (mk₀ a ha (f ≫ g)).comp h (by rw [ha, add_zero]) := by
  subst ha
  rw [← comp_assoc]; rw [mk₀_comp_mk₀]
  all_goals simp

section Preadditive

variable [Preadditive C]

variable (X Y) in
@[simp]
/--
lemma `mk₀_zero` / 引理 `mk₀_zero`

English:
lemma mk₀_zero
  given: (m₀ : M) (hm₀ : m₀ = 0)
  statement: mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0
  proof: by simp [mk₀]

@[simp]

中文:
引理 mk₀_zero
  条件: (m₀ : M) (hm₀ : m₀ = 0)
  结论: mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0
  证明: by simp [mk₀]

@[simp]
-/
lemma mk₀_zero (m₀ : M) (hm₀ : m₀ = 0) : mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0 := by simp [mk₀]

@[simp]
/--
lemma `mk₀_add` / 引理 `mk₀_add`

English:
lemma mk₀_add
  given: (m₀ : M) (hm₀ : m₀ = 0) (f g : X ⟶ Y)
  proof: by simp [mk₀]

@[simp]

中文:
引理 mk₀_add
  条件: (m₀ : M) (hm₀ : m₀ = 0) (f g : X ⟶ Y)
  证明: by simp [mk₀]

@[simp]
-/
lemma mk₀_add (m₀ : M) (hm₀ : m₀ = 0) (f g : X ⟶ Y) :
    mk₀ m₀ hm₀ (f + g) = mk₀ m₀ hm₀ f + mk₀ m₀ hm₀ g := by simp [mk₀]

@[simp]
/--
lemma `mk₀_neg` / 引理 `mk₀_neg`

English:
lemma mk₀_neg
  given: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y)
  proof: by simp [mk₀]

@[simp]

中文:
引理 mk₀_neg
  条件: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y)
  证明: by simp [mk₀]

@[simp]
-/
lemma mk₀_neg (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    mk₀ m₀ hm₀ (-f) = -mk₀ m₀ hm₀ f := by simp [mk₀]

@[simp]
/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  statement: [forall (a : M), (shiftFunctor C a).Additive]
  proof: by
  rw [comp]; rw [comp]; rw [comp]; rw [Functor.map_add]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]

@[simp]

中文:
引理 comp_add
  结论: [对任意 (a : M), (shiftFunctor C a).加性]
  证明: by
  rw [comp]; rw [comp]; rw [comp]; rw [Functor.map_add]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]

@[simp]

Depends on / 依赖: Functor, Functor.map_add, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, comp_add, map_add
-/
lemma comp_add [forall (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  rw [comp]; rw [comp]; rw [comp]; rw [Functor.map_add]; rw [Preadditive.add_comp]; rw [Preadditive.comp_add]

@[simp]
/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  proof: by
  rw [comp]; rw [comp]; rw [comp]; rw [Preadditive.add_comp]

@[simp]

中文:
引理 add_comp
  证明: by
  rw [comp]; rw [comp]; rw [comp]; rw [Preadditive.add_comp]

@[simp]

Depends on / 依赖: Preadditive, Preadditive.add_comp, add_comp
-/
lemma add_comp
    {a b c : M} (α₁ α₂ : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  rw [comp]; rw [comp]; rw [comp]; rw [Preadditive.add_comp]

@[simp]
/--
lemma `comp_neg` / 引理 `comp_neg`

English:
lemma comp_neg
  statement: [forall (a : M), (shiftFunctor C a).Additive]
  proof: by
  rw [comp]; rw [comp]; rw [Functor.map_neg]; rw [Preadditive.neg_comp]; rw [Preadditive.comp_neg]

@[simp]

中文:
引理 comp_neg
  结论: [对任意 (a : M), (shiftFunctor C a).加性]
  证明: by
  rw [comp]; rw [comp]; rw [Functor.map_neg]; rw [Preadditive.neg_comp]; rw [Preadditive.comp_neg]

@[simp]

Depends on / 依赖: Functor, Functor.map_neg, Preadditive, Preadditive.comp_neg, Preadditive.neg_comp, comp_neg, map_neg, neg_comp
-/
lemma comp_neg [forall (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (-β) h = -α.comp β h := by
  rw [comp]; rw [comp]; rw [Functor.map_neg]; rw [Preadditive.neg_comp]; rw [Preadditive.comp_neg]

@[simp]
/--
lemma `neg_comp` / 引理 `neg_comp`

English:
lemma neg_comp
  proof: by
  rw [comp]; rw [comp]; rw [Preadditive.neg_comp]

中文:
引理 neg_comp
  证明: by
  rw [comp]; rw [comp]; rw [Preadditive.neg_comp]

Depends on / 依赖: Preadditive, Preadditive.neg_comp, neg_comp
-/
lemma neg_comp
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (-α).comp β h = -α.comp β h := by
  rw [comp]; rw [comp]; rw [Preadditive.neg_comp]

variable (Z) in
@[simp]
/--
lemma `comp_zero` / 引理 `comp_zero`

English:
lemma comp_zero
  statement: [forall (a : M), (shiftFunctor C a).PreservesZeroMorphisms]
  proof: by
  rw [comp]; rw [Functor.map_zero]; rw [Limits.zero_comp]; rw [Limits.comp_zero]

中文:
引理 comp_zero
  结论: [对任意 (a : M), (shiftFunctor C a).保持ZeroMorphisms]
  证明: by
  rw [comp]; rw [Functor.map_zero]; rw [Limits.zero_comp]; rw [Limits.comp_zero]

Depends on / 依赖: Functor, Functor.map_zero, Limits, Limits.comp_zero, Limits.zero_comp, comp_zero, map_zero, zero_comp
-/
lemma comp_zero [forall (a : M), (shiftFunctor C a).PreservesZeroMorphisms]
    {a : M} (β : ShiftedHom X Y a) {b c : M} (h : b + a = c) :
    β.comp (0 : ShiftedHom Y Z b) h = 0 := by
  rw [comp]; rw [Functor.map_zero]; rw [Limits.zero_comp]; rw [Limits.comp_zero]

variable (X) in
@[simp]
/--
lemma `zero_comp` / 引理 `zero_comp`

English:
lemma zero_comp
  given: (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c)
  proof: by
  rw [comp]; rw [Limits.zero_comp]

中文:
引理 zero_comp
  条件: (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c)
  证明: by
  rw [comp]; rw [Limits.zero_comp]

Depends on / 依赖: Limits, Limits.zero_comp, zero_comp
-/
lemma zero_comp (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c) :
    (0 : ShiftedHom X Y a).comp β h = 0 := by
  rw [comp]; rw [Limits.zero_comp]

end Preadditive

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
  body: F.map f ≫ (F.commShiftIso a).hom.app Y

@[simp]

中文:
定义 map
  签名: {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.交换Shift M]
  定义体: F.map f ≫ (F.commShiftIso a).hom.app Y

@[simp]

Depends on / 依赖: F.commShiftIso, F.map, commShiftIso, hom.app
-/
def map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] :
    ShiftedHom (F.obj X) (F.obj Y) a :=
  F.map f ≫ (F.commShiftIso a).hom.app Y

@[simp]
/--
lemma `map_mk₀` / 引理 `map_mk₀`

English:
lemma map_mk₀
  given: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (F : C ⥤ D) [F.CommShift M]
  proof: by
  subst hm₀
  simp [map, mk₀, shiftFunctorZero', F.commShiftIso_zero M, ← Functor.map_comp_assoc]

@[simp]

中文:
引理 map_mk₀
  条件: (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (F : C ⥤ D) [F.交换Shift M]
  证明: by
  subst hm₀
  simp [map, mk₀, shiftFunctorZero', F.commShiftIso_zero M, ← Functor.map_comp_assoc]

@[simp]

Depends on / 依赖: F.commShiftIso_zero, Functor, Functor.map_comp_assoc, commShiftIso_zero, map_comp_assoc, shiftFunctorZero
-/
lemma map_mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (F : C ⥤ D) [F.CommShift M] :
    (ShiftedHom.mk₀ m₀ hm₀ f).map F = .mk₀ _ hm₀ (F.map f) := by
  subst hm₀
  simp [map, mk₀, shiftFunctorZero', F.commShiftIso_zero M, ← Functor.map_comp_assoc]

@[simp]
/--
lemma `id_map` / 引理 `id_map`

English:
lemma id_map
  given: {a : M} (f : ShiftedHom X Y a)
  statement: f.map (𝟭 C) = f
  proof: by
  simp [map]

中文:
引理 id_map
  条件: {a : M} (f : ShiftedHom X Y a)
  结论: f.map (𝟭 C) = f
  证明: by
  simp [map]
-/
lemma id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `comp_map` / 引理 `comp_map`

English:
lemma comp_map
  statement: {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
  proof: by
  simp [map, Functor.commShiftIso_comp_hom_app]

中文:
引理 comp_map
  结论: {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.交换Shift M]
  证明: by
  simp [map, Functor.commShiftIso_comp_hom_app]

Depends on / 依赖: Functor, Functor.commShiftIso_comp_hom_app, commShiftIso_comp_hom_app
-/
lemma comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
    (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G := by
  simp [map, Functor.commShiftIso_comp_hom_app]

/--
lemma `map_naturality` / 引理 `map_naturality`

English:
lemma map_naturality
  statement: {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G)
  proof: by
  rw [comp_mk₀]; rw [mk₀_comp]; rw [map]; rw [map]; rw [Category.assoc]; rw [← τ.naturality_assoc]; rw [τ.shift_app_comm a]

@[simp]

中文:
引理 map_naturality
  结论: {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G)
  证明: by
  rw [comp_mk₀]; rw [mk₀_comp]; rw [map]; rw [map]; rw [Category.assoc]; rw [← τ.naturality_assoc]; rw [τ.shift_app_comm a]

@[simp]

Depends on / 依赖: Category, Category.assoc, naturality_assoc, shift_app_comm
-/
lemma map_naturality {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift τ M] :
    (f.map F).comp (mk₀ 0 rfl (τ.app Y)) (zero_add _) =
      (mk₀ 0 rfl (τ.app X)).comp (f.map G) (add_zero _) := by
  rw [comp_mk₀]; rw [mk₀_comp]; rw [map]; rw [map]; rw [Category.assoc]; rw [← τ.naturality_assoc]; rw [τ.shift_app_comm a]

@[simp]
/--
lemma `map_naturality_1` / 引理 `map_naturality_1`

English:
lemma map_naturality_1
  proof: by
  simp [map_naturality]

@[simp]

中文:
引理 map_naturality_1
  证明: by
  simp [map_naturality]

@[simp]

Depends on / 依赖: map_naturality
-/
lemma map_naturality_1
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.inv.app X)).comp ((f.map F).comp
      (mk₀ 0 rfl (e.hom.app Y)) (zero_add _)) (add_zero _) = f.map G := by
  simp [map_naturality]

@[simp]
/--
lemma `map_naturality_2` / 引理 `map_naturality_2`

English:
lemma map_naturality_2
  proof: map_naturality_1 f e.symm

中文:
引理 map_naturality_2
  证明: map_naturality_1 f e.symm

Depends on / 依赖: e.symm, map_naturality_1
-/
lemma map_naturality_2
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.hom.app X)).comp ((f.map G).comp
      (mk₀ 0 rfl (e.inv.app Y)) (zero_add _)) (add_zero _) = f.map F :=
  map_naturality_1 f e.symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
  proof: by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc, ← Functor.commShiftIso_hom_naturality_assoc]
  simp only [F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id]

中文:
引理 map_comp
  结论: {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
  证明: by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc, ← Functor.commShiftIso_hom_naturality_assoc]
  simp only [F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id]

Depends on / 依赖: CommShift, F.commShiftIso_add, Functor, Functor.CommShift.isoAdd, Functor.commShiftIso_hom_naturality_assoc, Functor.comp_obj, Functor.map_comp, Functor.map_comp_assoc, Iso.inv_hom_id_app, _hom_app, commShiftIso_add, commShiftIso_hom_naturality_assoc, comp_id, comp_obj, inv_hom_id_app, isoAdd, map_comp, map_comp_assoc
-/
lemma map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (F : C ⥤ D) [F.CommShift M] :
    (f.comp g h).map F = (f.map F).comp (g.map F) h := by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc, ← Functor.commShiftIso_hom_naturality_assoc]
  simp only [F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id]

section Preadditive

variable [Preadditive C] [Preadditive D]

@[simp]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  given: {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Additive]
  proof: by
  simp [ShiftedHom.map, F.map_add]

@[simp]

中文:
引理 map_add
  条件: {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.交换Shift M] [F.加性]
  证明: by
  simp [ShiftedHom.map, F.map_add]

@[simp]

Depends on / 依赖: F.map_add, ShiftedHom, ShiftedHom.map, map_add
-/
lemma map_add {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (α₁ + α₂).map F = α₁.map F + α₂.map F := by
  simp [ShiftedHom.map, F.map_add]

@[simp]
/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  given: {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive]
  proof: by
  simp [ShiftedHom.map]

中文:
引理 map_zero
  条件: {a : M} (F : C ⥤ D) [F.交换Shift M] [F.加性]
  证明: by
  simp [ShiftedHom.map]

Depends on / 依赖: ShiftedHom, ShiftedHom.map
-/
lemma map_zero {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (0 : ShiftedHom X Y a).map F = 0 := by
  simp [ShiftedHom.map]

end Preadditive

section Linear

variable {R : Type*} [Ring R] [Preadditive C] [Linear R C]

@[simp]
/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  proof: by
  rw [comp]; rw [Functor.map_smul]; rw [comp]; rw [Linear.smul_comp]; rw [Linear.comp_smul]

@[simp]

中文:
引理 comp_smul
  证明: by
  rw [comp]; rw [Functor.map_smul]; rw [comp]; rw [Linear.smul_comp]; rw [Linear.comp_smul]

@[simp]

Depends on / 依赖: Functor, Functor.map_smul, Linear, Linear.comp_smul, Linear.smul_comp, comp_smul, map_smul, smul_comp
-/
lemma comp_smul
    [forall (a : M), Functor.Linear R (shiftFunctor C a)]
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (r • β) h = r • α.comp β h := by
  rw [comp]; rw [Functor.map_smul]; rw [comp]; rw [Linear.smul_comp]; rw [Linear.comp_smul]

@[simp]
/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  proof: by
  rw [comp]; rw [comp]; rw [Linear.smul_comp]

@[simp]

中文:
引理 smul_comp
  证明: by
  rw [comp]; rw [comp]; rw [Linear.smul_comp]

@[simp]

Depends on / 依赖: Linear, Linear.smul_comp, smul_comp
-/
lemma smul_comp
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (r • α).comp β h = r • α.comp β h := by
  rw [comp]; rw [comp]; rw [Linear.smul_comp]

@[simp]
/--
lemma `mk₀_smul` / 引理 `mk₀_smul`

English:
lemma mk₀_smul
  given: (m₀ : M) (hm₀ : m₀ = 0) (r : R) {f : X ⟶ Y}
  proof: by
  simp [mk₀]

中文:
引理 mk₀_smul
  条件: (m₀ : M) (hm₀ : m₀ = 0) (r : R) {f : X ⟶ Y}
  证明: by
  simp [mk₀]
-/
lemma mk₀_smul (m₀ : M) (hm₀ : m₀ = 0) (r : R) {f : X ⟶ Y} :
    mk₀ m₀ hm₀ (r • f) = r • mk₀ m₀ hm₀ f := by
  simp [mk₀]

variable [Preadditive D] [Linear R D]

@[simp]
/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Linear R]
  proof: by
  simp [ShiftedHom.map, F.map_smul]

中文:
引理 map_smul
  条件: (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.交换Shift M] [F.线性 R]
  证明: by
  simp [ShiftedHom.map, F.map_smul]

Depends on / 依赖: F.map_smul, ShiftedHom, ShiftedHom.map, map_smul
-/
lemma map_smul (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Linear R] :
    (r • α).map F = r • (α.map F) := by
  simp [ShiftedHom.map, F.map_smul]

end Linear

end ShiftedHom

end CategoryTheory
