/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Module.Basic

/-!
# The total complex of a bicomplex

Given a preadditive category `C`, two complex shapes `c₁ : ComplexShape I₁`,
`c₂ : ComplexShape I₂`, a bicomplex `K : HomologicalComplex₂ C c₁ c₂`,
and a third complex shape `c₁₂ : ComplexShape I₁₂` equipped
with `[TotalComplexShape c₁ c₂ c₁₂]`, we construct the total complex
`K.total c₁₂ : HomologicalComplex C c₁₂`.

In particular, if `c := ComplexShape.up ℤ` and `K : HomologicalComplex₂ c c`, then for any
`n : ℤ`, `(K.total c).X n` identifies to the coproduct of the `(K.X p).X q` such that
`p + q = n`, and the differential on `(K.total c).X n` is induced by the sum of horizontal
differentials `(K.X p).X q ⟶ (K.X (p + 1)).X q` and `(-1) ^ p` times the vertical
differentials `(K.X p).X q ⟶ (K.X p).X (q + 1)`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

/--
Definition of `HasTotal` / `HasTotal` 的定义

English:
abbreviation HasTotal
  body: K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

include e in

中文:
缩写 HasTotal
  定义体: K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

include e in

Depends on / 依赖: ComplexShape, HasMap, K.toGradedObject.HasMap, toGradedObject
-/
abbrev HasTotal := K.toGradedObject.HasMap (ComplexShape.π c₁ c₂ c₁₂)

include e in
variable {K L} in
/--
lemma `hasTotal_of_iso` / 引理 `hasTotal_of_iso`

English:
lemma hasTotal_of_iso
  given: [K.HasTotal c₁₂]
  statement: L.HasTotal c₁₂
  proof: GradedObject.hasMap_of_iso (GradedObject.isoMk K.toGradedObject L.toGradedObject
    (fun ⟨i₁, i₂⟩ =>
      (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂).mapIso e)) _

中文:
引理 hasTotal_of_iso
  条件: [K.HasTotal c₁₂]
  结论: L.HasTotal c₁₂
  证明: GradedObject.hasMap_of_iso (GradedObject.isoMk K.toGradedObject L.toGradedObject
    (fun ⟨i₁, i₂⟩ =>
      (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂).mapIso e)) _

Depends on / 依赖: GradedObject, GradedObject.hasMap_of_iso, GradedObject.isoMk, HomologicalComplex, HomologicalComplex.eval, K.toGradedObject, L.toGradedObject, hasMap_of_iso, mapIso, toGradedObject
-/
lemma hasTotal_of_iso [K.HasTotal c₁₂] : L.HasTotal c₁₂ :=
  GradedObject.hasMap_of_iso (GradedObject.isoMk K.toGradedObject L.toGradedObject
    (fun ⟨i₁, i₂⟩ =>
      (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂).mapIso e)) _

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

section

variable (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)

/--
Definition of `d₁` / `d₁` 的定义

English:
definition d₁
  signature: :
  body: ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

中文:
定义 d₁
  签名: :
  定义体: ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

Depends on / 依赖: ComplexShape, K.toGradedObject, toGradedObject
-/
noncomputable def d₁ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ (c₁.next i₁)).f i₂ ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨_, i₂⟩ i₁₂)

/--
Definition of `d₂` / `d₂` 的定义

English:
definition d₂
  signature: :
  body: ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

中文:
定义 d₂
  签名: :
  定义体: ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

Depends on / 依赖: ComplexShape, K.toGradedObject, toGradedObject
-/
noncomputable def d₂ :
    (K.X i₁).X i₂ ⟶ (K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)) i₁₂ :=
  ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ (c₂.next i₂) ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, _⟩ i₁₂)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `d₁_eq_zero` / 引理 `d₁_eq_zero`

English:
lemma d₁_eq_zero
  given: (h : ¬ c₁.Rel i₁ (c₁.next i₁))
  proof: by
  dsimp [d₁]
  rw [K.shape_f _ _ h]; rw [zero_comp]; rw [smul_zero]

中文:
引理 d₁_eq_zero
  条件: (h : ¬ c₁.关系 i₁ (c₁.next i₁))
  证明: by
  dsimp [d₁]
  rw [K.shape_f _ _ h]; rw [zero_comp]; rw [smul_zero]

Depends on / 依赖: K.shape_f, shape_f, smul_zero, zero_comp
-/
lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₁]
  rw [K.shape_f _ _ h]; rw [zero_comp]; rw [smul_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `d₂_eq_zero` / 引理 `d₂_eq_zero`

English:
lemma d₂_eq_zero
  given: (h : ¬ c₂.Rel i₂ (c₂.next i₂))
  proof: by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h]; rw [zero_comp]; rw [smul_zero]

中文:
引理 d₂_eq_zero
  条件: (h : ¬ c₂.关系 i₂ (c₂.next i₂))
  证明: by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h]; rw [zero_comp]; rw [smul_zero]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shape, smul_zero, zero_comp
-/
lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h]; rw [zero_comp]; rw [smul_zero]

end

namespace totalAux

/--
lemma `d₁_eq'` / 引理 `d₁_eq'`

English:
lemma d₁_eq'
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  obtain rfl := c₁.next_eq' h
  rfl

中文:
引理 d₁_eq'
  条件: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  obtain rfl := c₁.next_eq' h
  rfl

Depends on / 依赖: next_eq
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂) := by
  obtain rfl := c₁.next_eq' h
  rfl

/--
lemma `d₁_eq` / 引理 `d₁_eq`

English:
lemma d₁_eq
  statement: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  rw [d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

中文:
引理 d₁_eq
  结论: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  rw [d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

Depends on / 依赖: K.toGradedObject, toGradedObject
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁', i₂⟩ i₁₂ h') := by
  rw [d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

/--
lemma `d₂_eq'` / 引理 `d₂_eq'`

English:
lemma d₂_eq'
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
  proof: by
  obtain rfl := c₂.next_eq' h
  rfl

中文:
引理 d₂_eq'
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂') (i₁₂ : I₁₂)
  证明: by
  obtain rfl := c₂.next_eq' h
  rfl

Depends on / 依赖: next_eq
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂) := by
  obtain rfl := c₂.next_eq' h
  rfl

/--
lemma `d₂_eq` / 引理 `d₂_eq`

English:
lemma d₂_eq
  statement: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
  proof: by
  rw [d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

中文:
引理 d₂_eq
  结论: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂') (i₁₂ : I₁₂)
  证明: by
  rw [d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

Depends on / 依赖: K.toGradedObject, toGradedObject
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂'⟩ i₁₂ h') := by
  rw [d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq]

end totalAux

set_option backward.isDefEq.respectTransparency false in
/--
lemma `d₁_eq_zero'` / 引理 `d₁_eq_zero'`

English:
lemma d₁_eq_zero'
  statement: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  rw [totalAux.d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

中文:
引理 d₁_eq_zero'
  结论: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  rw [totalAux.d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

Depends on / 依赖: K.toGradedObject, comp_zero, smul_zero, toGradedObject, totalAux, totalAux.d
-/
lemma d₁_eq_zero' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ != i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₁_eq' K c₁₂ h i₂ i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `d₂_eq_zero'` / 引理 `d₂_eq_zero'`

English:
lemma d₂_eq_zero'
  statement: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
  proof: by
  rw [totalAux.d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

中文:
引理 d₂_eq_zero'
  结论: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂') (i₁₂ : I₁₂)
  证明: by
  rw [totalAux.d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

Depends on / 依赖: K.toGradedObject, comp_zero, smul_zero, toGradedObject, totalAux, totalAux.d
-/
lemma d₂_eq_zero' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ != i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = 0 := by
  rw [totalAux.d₂_eq' K c₁₂ i₁ h i₁₂]; rw [K.toGradedObject.ιMapObjOrZero_eq_zero]; rw [comp_zero]; rw [smul_zero]
  exact h'

/--
Definition of `D₁` / `D₁` 的定义

English:
definition D₁
  signature: (i₁₂ i₁₂' : I₁₂)
  body: GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂')

中文:
定义 D₁
  签名: (i₁₂ i₁₂' : I₁₂)
  定义体: GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂')

Depends on / 依赖: ComplexShape, GradedObject, GradedObject.descMapObj, descMapObj
-/
noncomputable def D₁ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₁ c₁₂ i₁ i₂ i₁₂')

/--
Definition of `D₂` / `D₂` 的定义

English:
definition D₂
  signature: (i₁₂ i₁₂' : I₁₂)
  body: GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₂ c₁₂ i₁ i₂ i₁₂')

中文:
定义 D₂
  签名: (i₁₂ i₁₂' : I₁₂)
  定义体: GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₂ c₁₂ i₁ i₂ i₁₂')

Depends on / 依赖: ComplexShape, GradedObject, GradedObject.descMapObj, descMapObj
-/
noncomputable def D₂ (i₁₂ i₁₂' : I₁₂) :
    K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂ ⟶
      K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂) i₁₂' :=
  GradedObject.descMapObj _ (ComplexShape.π c₁ c₂ c₁₂)
    (fun ⟨i₁, i₂⟩ _ => K.d₂ c₁₂ i₁ i₂ i₁₂')

namespace totalAux

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `ιMapObj_D₁` / 引理 `ιMapObj_D₁`

English:
lemma ιMapObj_D₁
  given: (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂)
  proof: by
  simp [D₁]

中文:
引理 ιMapObj_D₁
  条件: (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : 余mplexShape.π c₁ c₂ c₁₂ i = i₁₂)
  证明: by
  simp [D₁]
-/
lemma ιMapObj_D₁ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₁]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `ιMapObj_D₂` / 引理 `ιMapObj_D₂`

English:
lemma ιMapObj_D₂
  given: (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂)
  proof: by
  simp [D₂]

中文:
引理 ιMapObj_D₂
  条件: (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : 余mplexShape.π c₁ c₂ c₁₂ i = i₁₂)
  证明: by
  simp [D₂]
-/
lemma ιMapObj_D₂ (i₁₂ i₁₂' : I₁₂) (i : I₁ × I₂) (h : ComplexShape.π c₁ c₂ c₁₂ i = i₁₂) :
    K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) i i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i.1 i.2 i₁₂' := by
  simp [D₂]

end totalAux

set_option backward.isDefEq.respectTransparency false in
/--
lemma `D₁_shape` / 引理 `D₁_shape`

English:
lemma D₁_shape
  given: (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂')
  statement: K.D₁ c₁₂ i₁₂ i₁₂' = 0
  proof: by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact d₁_eq_zero _ _ _ _ _ h₁

中文:
引理 D₁_shape
  条件: (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.关系 i₁₂ i₁₂')
  结论: K.D₁ c₁₂ i₁₂ i₁₂' = 0
  证明: by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact d₁_eq_zero _ _ _ _ _ h₁

Depends on / 依赖: ComplexShape, ComplexShape.rel_, comp_zero, totalAux
-/
lemma D₁_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₁ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' c₁₂ h₁ i₂ i₁₂']
    intro h₂
    exact h₁₂ (by simpa only [← h, ← h₂] using ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂)
  · exact d₁_eq_zero _ _ _ _ _ h₁

set_option backward.isDefEq.respectTransparency false in
/--
lemma `D₂_shape` / 引理 `D₂_shape`

English:
lemma D₂_shape
  given: (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂')
  statement: K.D₂ c₁₂ i₁₂ i₁₂' = 0
  proof: by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₂, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact d₂_eq_zero _ _ _ _ _ h₂

中文:
引理 D₂_shape
  条件: (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.关系 i₁₂ i₁₂')
  结论: K.D₂ c₁₂ i₁₂ i₁₂' = 0
  证明: by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₂, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact d₂_eq_zero _ _ _ _ _ h₂

Depends on / 依赖: ComplexShape, ComplexShape.rel_, comp_zero, totalAux
-/
lemma D₂_shape (i₁₂ i₁₂' : I₁₂) (h₁₂ : ¬ c₁₂.Rel i₁₂ i₁₂') : K.D₂ c₁₂ i₁₂ i₁₂' = 0 := by
  ext ⟨i₁, i₂⟩ h
  simp only [totalAux.ιMapObj_D₂, comp_zero]
  by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' c₁₂ i₁ h₂ i₁₂']
    intro h₁
    exact h₁₂ (by simpa only [← h, ← h₁] using ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂)
  · exact d₂_eq_zero _ _ _ _ _ h₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `D₁_D₁` / 引理 `D₁_D₁`

English:
lemma D₁_D₁
  given: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  statement: K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0
  proof: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.

中文:
引理 D₁_D₁
  条件: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  结论: K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0
  证明: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.

Depends on / 依赖: ComplexShape, ComplexShape.next_, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, comp_zero, d_f_comp_d_f_assoc, next_eq, totalAux, totalAux.d, units_smul_comp, zero_comp
-/
lemma D₁_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₁_assoc, comp_zero]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
        by_cases h₄ : c₁.Rel (c₁.next i₁) (c₁.next (c₁.next i₁))
        · rw [totalAux.d₁_eq K c₁₂ h₄ i₂ i₁₂'', Linear.comp_units_smul,
            d_f_comp_d_f_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄]; rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃]; rw [h]; rw [c₁₂.next_eq' h₁]; rw [c₁₂.next_eq' h₂]
        · rw [K.d₁_eq_zero _ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, zero_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `D₂_D₂` / 引理 `D₂_D₂`

English:
lemma D₂_D₂
  given: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  statement: K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = 0
  proof: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_zero]
      by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
      · rw [totalAux.d₂_eq K c₁₂ i₁ h₃ i₁₂']; swap
        · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃, ← c₁₂.

中文:
引理 D₂_D₂
  条件: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  结论: K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = 0
  证明: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_zero]
      by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
      · rw [totalAux.d₂_eq K c₁₂ i₁ h₃ i₁₂']; swap
        · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃, ← c₁₂.

Depends on / 依赖: ComplexShape, ComplexShape.next_, HomologicalComplex, HomologicalComplex.d_comp_d_assoc, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, comp_zero, d_comp_d_assoc, next_eq, totalAux, totalAux.d, units_smul_comp
-/
lemma D₂_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) : K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = 0 := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_zero]
      by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
      · rw [totalAux.d₂_eq K c₁₂ i₁ h₃ i₁₂']; swap
        · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel (c₂.next i₂) (c₂.next (c₂.next i₂))
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂'', Linear.comp_units_smul,
            HomologicalComplex.d_comp_d_assoc, zero_comp, smul_zero, smul_zero]
          rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]; rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃]; rw [h]; rw [c₁₂.next_eq' h₁]; rw [c₁₂.next_eq' h₂]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, comp_zero, smul_zero]
      · rw [K.d₂_eq_zero c₁₂ _ _ _ h₃, zero_comp]
    · rw [K.D₂_shape c₁₂ _ _ h₂, comp_zero]
  · rw [K.D₂_shape c₁₂ _ _ h₁, zero_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `D₂_D₁` / 引理 `D₂_D₁`

English:
lemma D₂_D₁
  given: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  proof: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.ne

中文:
引理 D₂_D₁
  条件: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  证明: by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.ne

Depends on / 依赖: ComplexShape, ComplexShape.next_, Linear, Linear.units_smul_comp, comp_neg, next_eq, totalAux, totalAux.d, units_smul_comp
-/
lemma D₂_D₁ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' = - K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' := by
  by_cases h₁ : c₁₂.Rel i₁₂ i₁₂'
  · by_cases h₂ : c₁₂.Rel i₁₂' i₁₂''
    · ext ⟨i₁, i₂⟩ h
      simp only [totalAux.ιMapObj_D₂_assoc, comp_neg, totalAux.ιMapObj_D₁_assoc]
      by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
      · rw [totalAux.d₁_eq K c₁₂ h₃ i₂ i₁₂']; swap
        · rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂, ← c₁₂.next_eq' h₁, h]
        simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₂]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · have h₅ : ComplexShape.π c₁ c₂ c₁₂ (i₁, c₂.next i₂) = i₁₂' := by
            rw [← c₁₂.next_eq' h₁]; rw [← h]; rw [ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄]
          have h₆ : ComplexShape.π c₁ c₂ c₁₂ (c₁.next i₁, c₂.next i₂) = i₁₂'' := by
            rw [← c₁₂.next_eq' h₂]; rw [← ComplexShape.next_π₁ c₂ c₁₂ h₃]; rw [h₅]
          simp only [totalAux.d₂_eq K c₁₂ _ h₄ _ h₅, totalAux.d₂_eq K c₁₂ _ h₄ _ h₆,
            Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁, Linear.comp_units_smul,
            totalAux.d₁_eq K c₁₂ h₃ _ _ h₆, HomologicalComplex.Hom.comm_assoc, smul_smul,
            ComplexShape.ε₂_ε₁ c₁₂ h₃ h₄, neg_mul, Units.neg_smul]
        · simp only [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp, comp_zero, smul_zero, neg_zero]
      · rw [K.d₁_eq_zero c₁₂ _ _ _ h₃, zero_comp, neg_zero]
        by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
        · rw [totalAux.d₂_eq K c₁₂ i₁ h₄ i₁₂']; swap
          · rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, ← c₁₂.next_eq' h₁, h]
          simp only [Linear.units_smul_comp, assoc, totalAux.ιMapObj_D₁]
          rw [K.d₁_eq_zero c₁₂ _ _ _ h₃]; rw [comp_zero]; rw [smul_zero]
        · rw [K.d₂_eq_zero c₁₂ _ _ _ h₄, zero_comp]
    · rw [K.D₁_shape c₁₂ _ _ h₂, K.D₂_shape c₁₂ _ _ h₂, comp_zero, comp_zero, neg_zero]
  · rw [K.D₁_shape c₁₂ _ _ h₁, K.D₂_shape c₁₂ _ _ h₁, zero_comp, zero_comp, neg_zero]

@[reassoc]
/--
lemma `D₁_D₂` / 引理 `D₁_D₂`

English:
lemma D₁_D₂
  given: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  proof: by simp

中文:
引理 D₁_D₂
  条件: (i₁₂ i₁₂' i₁₂'' : I₁₂)
  证明: by simp
-/
lemma D₁_D₂ (i₁₂ i₁₂' i₁₂'' : I₁₂) :
    K.D₁ c₁₂ i₁₂ i₁₂' ≫ K.D₂ c₁₂ i₁₂' i₁₂'' = - K.D₂ c₁₂ i₁₂ i₁₂' ≫ K.D₁ c₁₂ i₁₂' i₁₂'' := by simp

/-- The total complex of a bicomplex. -/
@[simps -isSimp d, implicit_reducible]
/--
Definition of `total` / `total` 的定义

English:
definition total
  signature: : HomologicalComplex C c₁₂ where
  body: K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    rw [K.D₁_shape c₁₂ _ _ h₁₂]; rw [K.D₂_shape c₁₂ _ _ h₁₂]; rw [zero_add]

中文:
定义 total
  签名: : 同调复形 C c₁₂ where
  定义体: K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    rw [K.D₁_shape c₁₂ _ _ h₁₂]; rw [K.D₂_shape c₁₂ _ _ h₁₂]; rw [zero_add]

Depends on / 依赖: ComplexShape, K.toGradedObject.mapObj, mapObj, toGradedObject
-/
noncomputable def total : HomologicalComplex C c₁₂ where
  X := K.toGradedObject.mapObj (ComplexShape.π c₁ c₂ c₁₂)
  d i₁₂ i₁₂' := K.D₁ c₁₂ i₁₂ i₁₂' + K.D₂ c₁₂ i₁₂ i₁₂'
  shape i₁₂ i₁₂' h₁₂ := by
    rw [K.D₁_shape c₁₂ _ _ h₁₂]; rw [K.D₂_shape c₁₂ _ _ h₁₂]; rw [zero_add]

/--
Definition of `ιTotal` / `ιTotal` 的定义

English:
definition ιTotal
  signature: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  body: K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

@[reassoc (attr := simp)]

中文:
定义 ιTotal
  签名: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  定义体: K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

@[reassoc (attr := simp)]

Depends on / 依赖: ComplexShape, K.toGradedObject, toGradedObject
-/
noncomputable def ιTotal (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObj (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂ h

@[reassoc (attr := simp)]
/--
lemma `XXIsoOfEq_hom_ιTotal` / 引理 `XXIsoOfEq_hom_ιTotal`

English:
lemma XXIsoOfEq_hom_ιTotal
  statement: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  proof: by
  subst h₁ h₂
  simp

@[reassoc (attr := simp)]

中文:
引理 XXIsoOfEq_hom_ιTotal
  结论: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  证明: by
  subst h₁ h₂
  simp

@[reassoc (attr := simp)]
-/
lemma XXIsoOfEq_hom_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (y₁, y₂) = i₁₂) :
    (K.XXIsoOfEq _ _ _ h₁ h₂).hom ≫ K.ιTotal c₁₂ y₁ y₂ i₁₂ h =
      K.ιTotal c₁₂ x₁ x₂ i₁₂ (by rw [h₁, h₂, h]) := by
  subst h₁ h₂
  simp

@[reassoc (attr := simp)]
/--
lemma `XXIsoOfEq_inv_ιTotal` / 引理 `XXIsoOfEq_inv_ιTotal`

English:
lemma XXIsoOfEq_inv_ιTotal
  statement: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  proof: by
  subst h₁ h₂
  simp

中文:
引理 XXIsoOfEq_inv_ιTotal
  结论: {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
  证明: by
  subst h₁ h₂
  simp
-/
lemma XXIsoOfEq_inv_ιTotal {x₁ y₁ : I₁} (h₁ : x₁ = y₁) {x₂ y₂ : I₂} (h₂ : x₂ = y₂)
    (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (x₁, x₂) = i₁₂) :
    (K.XXIsoOfEq _ _ _ h₁ h₂).inv ≫ K.ιTotal c₁₂ x₁ x₂ i₁₂ h =
      K.ιTotal c₁₂ y₁ y₂ i₁₂ (by rw [← h, h₁, h₂]) := by
  subst h₁ h₂
  simp

/--
Definition of `ιTotalOrZero` / `ιTotalOrZero` 的定义

English:
definition ιTotalOrZero
  signature: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  body: K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂

中文:
定义 ιTotalOrZero
  签名: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  定义体: K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂

Depends on / 依赖: ComplexShape, K.toGradedObject, toGradedObject
-/
noncomputable def ιTotalOrZero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    (K.X i₁).X i₂ ⟶ (K.total c₁₂).X i₁₂ :=
  K.toGradedObject.ιMapObjOrZero (ComplexShape.π c₁ c₂ c₁₂) ⟨i₁, i₂⟩ i₁₂

/--
lemma `ιTotalOrZero_eq` / 引理 `ιTotalOrZero_eq`

English:
lemma ιTotalOrZero_eq
  statement: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  proof: dif_pos h

中文:
引理 ιTotalOrZero_eq
  结论: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma ιTotalOrZero_eq (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = K.ιTotal c₁₂ i₁ i₂ i₁₂ h := dif_pos h

/--
lemma `ιTotalOrZero_eq_zero` / 引理 `ιTotalOrZero_eq_zero`

English:
lemma ιTotalOrZero_eq_zero
  statement: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  proof: dif_neg h

@[reassoc (attr := simp)]

中文:
引理 ιTotalOrZero_eq_zero
  结论: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  证明: dif_neg h

@[reassoc (attr := simp)]

Depends on / 依赖: dif_neg
-/
lemma ιTotalOrZero_eq_zero (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) != i₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ = 0 := dif_neg h

@[reassoc (attr := simp)]
/--
lemma `ι_D₁` / 引理 `ι_D₁`

English:
lemma ι_D₁
  given: (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂)
  proof: by
  apply totalAux.ιMapObj_D₁

@[reassoc (attr := simp)]

中文:
引理 ι_D₁
  条件: (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : 余mplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂)
  证明: by
  apply totalAux.ιMapObj_D₁

@[reassoc (attr := simp)]

Depends on / 依赖: totalAux
-/
lemma ι_D₁ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₁ c₁₂ i₁₂ i₁₂' =
      K.d₁ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₁

@[reassoc (attr := simp)]
/--
lemma `ι_D₂` / 引理 `ι_D₂`

English:
lemma ι_D₂
  statement: (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
  proof: by
  apply totalAux.ιMapObj_D₂

中文:
引理 ι_D₂
  结论: (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
  证明: by
  apply totalAux.ιMapObj_D₂

Depends on / 依赖: totalAux
-/
lemma ι_D₂ (i₁₂ i₁₂' : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ K.D₂ c₁₂ i₁₂ i₁₂' =
      K.d₂ c₁₂ i₁ i₂ i₁₂' := by
  apply totalAux.ιMapObj_D₂

/--
lemma `d₁_eq'` / 引理 `d₁_eq'`

English:
lemma d₁_eq'
  given: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  proof: totalAux.d₁_eq' _ _ h _ _

中文:
引理 d₁_eq'
  条件: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  证明: totalAux.d₁_eq' _ _ h _ _

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₁_eq' {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotalOrZero c₁₂ i₁' i₂ i₁₂) :=
  totalAux.d₁_eq' _ _ h _ _

/--
lemma `d₁_eq` / 引理 `d₁_eq`

English:
lemma d₁_eq
  statement: {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  proof: totalAux.d₁_eq _ _ h _ _ _

中文:
引理 d₁_eq
  结论: {i₁ i₁' : I₁} (h : c₁.关系 i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
  证明: totalAux.d₁_eq _ _ h _ _ _

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = i₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.d i₁ i₁').f i₂ ≫
      K.ιTotal c₁₂ i₁' i₂ i₁₂ h') :=
  totalAux.d₁_eq _ _ h _ _ _

/--
lemma `d₂_eq'` / 引理 `d₂_eq'`

English:
lemma d₂_eq'
  given: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
  proof: totalAux.d₂_eq' _ _ _ h _

中文:
引理 d₂_eq'
  条件: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂') (i₁₂ : I₁₂)
  证明: totalAux.d₂_eq' _ _ _ h _

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₂_eq' (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotalOrZero c₁₂ i₁ i₂' i₁₂) :=
  totalAux.d₂_eq' _ _ _ h _

/--
lemma `d₂_eq` / 引理 `d₂_eq`

English:
lemma d₂_eq
  statement: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
  proof: totalAux.d₂_eq _ _ _ h _ _

中文:
引理 d₂_eq
  结论: (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.关系 i₂ i₂') (i₁₂ : I₁₂)
  证明: totalAux.d₂_eq _ _ _ h _ _

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') (i₁₂ : I₁₂)
    (h' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = i₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ = ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ • ((K.X i₁).d i₂ i₂' ≫
    K.ιTotal c₁₂ i₁ i₂' i₁₂ h') :=
  totalAux.d₂_eq _ _ _ h _ _

section

variable {c₁₂}
variable {A : C} {i₁₂ : I₁₂}
  (f : forall (i₁ : I₁) (i₂ : I₂) (_ : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂), (K.X i₁).X i₂ ⟶ A)

/--
Definition of `totalDesc` / `totalDesc` 的定义

English:
definition totalDesc
  signature: : (K.total c₁₂).X i₁₂ ⟶ A
  body: K.toGradedObject.descMapObj _ (fun ⟨i₁, i₂⟩ hi => f i₁ i₂ hi)

中文:
定义 totalDesc
  签名: : (K.total c₁₂).X i₁₂ ⟶ A
  定义体: K.toGradedObject.descMapObj _ (fun ⟨i₁, i₂⟩ hi => f i₁ i₂ hi)

Depends on / 依赖: K.toGradedObject.descMapObj, descMapObj, toGradedObject
-/
noncomputable def totalDesc : (K.total c₁₂).X i₁₂ ⟶ A :=
  K.toGradedObject.descMapObj _ (fun ⟨i₁, i₂⟩ hi => f i₁ i₂ hi)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_totalDesc` / 引理 `ι_totalDesc`

English:
lemma ι_totalDesc
  given: (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂)
  proof: by
  simp [totalDesc, ιTotal]

中文:
引理 ι_totalDesc
  条件: (i₁ : I₁) (i₂ : I₂) (hi : 余mplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂)
  证明: by
  simp [totalDesc, ιTotal]

Depends on / 依赖: totalDesc
-/
lemma ι_totalDesc (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ K.totalDesc f = f i₁ i₂ hi := by
  simp [totalDesc, ιTotal]

end

namespace total

variable {K L M}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
  proof: by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

中文:
引理 hom_ext
  结论: {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
  证明: by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

Depends on / 依赖: GradedObject, GradedObject.mapObj_ext, mapObj_ext
-/
lemma hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
    (h : forall (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂),
      K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ f = K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ g) : f = g := by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

variable [L.HasTotal c₁₂]

namespace mapAux

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `d₁_mapMap` / 引理 `d₁_mapMap`

English:
lemma d₁_mapMap
  given: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [totalAux.d₁_eq' _ c₁₂ h]
  · simp [d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

中文:
引理 d₁_mapMap
  条件: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [totalAux.d₁_eq' _ c₁₂ h]
  · simp [d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₁_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₁ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₁ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · simp [totalAux.d₁_eq' _ c₁₂ h]
  · simp [d₁_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `d₂_mapMap` / 引理 `d₂_mapMap`

English:
lemma d₂_mapMap
  given: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [totalAux.d₂_eq' _ c₁₂ i₁ h]
  · simp [d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

中文:
引理 d₂_mapMap
  条件: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [totalAux.d₂_eq' _ c₁₂ i₁ h]
  · simp [d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

Depends on / 依赖: totalAux, totalAux.d
-/
lemma d₂_mapMap (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.d₂ c₁₂ i₁ i₂ i₁₂ ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ =
    (φ.f i₁).f i₂ ≫ L.d₂ c₁₂ i₁ i₂ i₁₂ := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · simp [totalAux.d₂_eq' _ c₁₂ i₁ h]
  · simp [d₂_eq_zero _ c₁₂ i₁ i₂ i₁₂ h]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapMap_D₁` / 引理 `mapMap_D₁`

English:
lemma mapMap_D₁
  given: (i₁₂ i₁₂' : I₁₂)
  proof: by
  cat_disch

中文:
引理 mapMap_D₁
  条件: (i₁₂ i₁₂' : I₁₂)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapMap_D₁ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₁ c₁₂ i₁₂ i₁₂' =
      K.D₁ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapMap_D₂` / 引理 `mapMap_D₂`

English:
lemma mapMap_D₂
  given: (i₁₂ i₁₂' : I₁₂)
  proof: by
  cat_disch

中文:
引理 mapMap_D₂
  条件: (i₁₂ i₁₂' : I₁₂)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma mapMap_D₂ (i₁₂ i₁₂' : I₁₂) :
    GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂ ≫ L.D₂ c₁₂ i₁₂ i₁₂' =
      K.D₂ c₁₂ i₁₂ i₁₂' ≫ GradedObject.mapMap (toGradedObjectMap φ) _ i₁₂' := by
  cat_disch

end mapAux

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : K.total c₁₂ ⟶ L.total c₁₂ where
  body: GradedObject.mapMap (toGradedObjectMap φ) _
  comm' i₁₂ i₁₂' _ := by
    dsimp [total]
    rw [comp_add]; rw [add_comp]; rw [mapAux.mapMap_D₁]; rw [mapAux.mapMap_D₂]

@[simp]

中文:
定义 map
  签名: : K.total c₁₂ ⟶ L.total c₁₂ where
  定义体: GradedObject.mapMap (toGradedObjectMap φ) _
  comm' i₁₂ i₁₂' _ := by
    dsimp [total]
    rw [comp_add]; rw [add_comp]; rw [mapAux.mapMap_D₁]; rw [mapAux.mapMap_D₂]

@[simp]

Depends on / 依赖: GradedObject, GradedObject.mapMap, mapMap, toGradedObjectMap
-/
noncomputable def map : K.total c₁₂ ⟶ L.total c₁₂ where
  f := GradedObject.mapMap (toGradedObjectMap φ) _
  comm' i₁₂ i₁₂' _ := by
    dsimp [total]
    rw [comp_add]; rw [add_comp]; rw [mapAux.mapMap_D₁]; rw [mapAux.mapMap_D₂]

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  proof: rfl

中文:
引理 forget_map
  证明: rfl
-/
lemma forget_map :
    (HomologicalComplex.forget C c₁₂).map (map φ c₁₂) =
      GradedObject.mapMap (toGradedObjectMap φ) _ := rfl

variable (K) in
@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (𝟙 K) c₁₂ = 𝟙 _
  proof: by
  apply (HomologicalComplex.forget _ _).map_injective
  apply GradedObject.mapMap_id

中文:
引理 map_id
  结论: map (𝟙 K) c₁₂ = 𝟙 _
  证明: by
  apply (HomologicalComplex.forget _ _).map_injective
  apply GradedObject.mapMap_id

Depends on / 依赖: GradedObject, GradedObject.mapMap_id, HomologicalComplex, HomologicalComplex.forget, forget, mapMap_id, map_injective
-/
lemma map_id : map (𝟙 K) c₁₂ = 𝟙 _ := by
  apply (HomologicalComplex.forget _ _).map_injective
  apply GradedObject.mapMap_id

variable [M.HasTotal c₁₂]

@[simp, reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂
  proof: by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

中文:
引理 map_comp
  结论: map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂
  证明: by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

Depends on / 依赖: GradedObject, GradedObject.mapMap_comp, HomologicalComplex, HomologicalComplex.forget, forget, mapMap_comp, map_injective, toGradedObjectMap
-/
lemma map_comp : map (φ ≫ ψ) c₁₂ = map φ c₁₂ ≫ map ψ c₁₂ := by
  apply (HomologicalComplex.forget _ _).map_injective
  exact GradedObject.mapMap_comp (toGradedObjectMap φ) (toGradedObjectMap ψ) _

/-- The isomorphism `K.total c₁₂ ≅ L.total c₁₂` of homological complexes induced
by an isomorphism of bicomplexes `K ≅ L`. -/
@[simps]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: : K.total c₁₂ ≅ L.total c₁₂ where
  body: map e.hom _
  inv := map e.inv _
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

中文:
定义 mapIso
  签名: : K.total c₁₂ ≅ L.total c₁₂ where
  定义体: map e.hom _
  inv := map e.inv _
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

Depends on / 依赖: e.hom
-/
noncomputable def mapIso : K.total c₁₂ ≅ L.total c₁₂ where
  hom := map e.hom _
  inv := map e.inv _
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end total

section

variable [L.HasTotal c₁₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιTotal_map` / 引理 `ιTotal_map`

English:
lemma ιTotal_map
  given: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂)
  proof: by
  simp [total.map, ιTotal]

中文:
引理 ιTotal_map
  条件: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : 余mplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂)
  证明: by
  simp [total.map, ιTotal]

Depends on / 依赖: total.map
-/
lemma ιTotal_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotal c₁₂ i₁ i₂ i₁₂ h := by
  simp [total.map, ιTotal]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιTotalOrZero_map` / 引理 `ιTotalOrZero_map`

English:
lemma ιTotalOrZero_map
  given: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  proof: by
  simp [total.map, ιTotalOrZero]

中文:
引理 ιTotalOrZero_map
  条件: (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂)
  证明: by
  simp [total.map, ιTotalOrZero]

Depends on / 依赖: total.map
-/
lemma ιTotalOrZero_map (i₁ : I₁) (i₂ : I₂) (i₁₂ : I₁₂) :
    K.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ ≫ (total.map φ c₁₂).f i₁₂ =
      (φ.f i₁).f i₂ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ i₁₂ := by
  simp [total.map, ιTotalOrZero]

end

variable (C c₁ c₂)
variable [forall (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

/-- The functor which sends a bicomplex to its total complex. -/
@[simps]
/--
Definition of `totalFunctor` / `totalFunctor` 的定义

English:
definition totalFunctor
  signature: :
  body: K.total c₁₂
  map φ := total.map φ c₁₂

中文:
定义 totalFunctor
  签名: :
  定义体: K.total c₁₂
  map φ := total.map φ c₁₂

Depends on / 依赖: K.total
-/
noncomputable def totalFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂ where
  obj K := K.total c₁₂
  map φ := total.map φ c₁₂

end HomologicalComplex₂
