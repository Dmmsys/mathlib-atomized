/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Tactic.Linarith

/-! # The mapping cone of a morphism of cochain complexes

In this file, we study the homotopy cofiber `HomologicalComplex.homotopyCofiber`
of a morphism `φ : F ⟶ G` of cochain complexes indexed by `ℤ`. In this case,
we redefine it as `CochainComplex.mappingCone φ`. The API involves definitions
- `mappingCone.inl φ : Cochain F (mappingCone φ) (-1)`,
- `mappingCone.inr φ : G ⟶ mappingCone φ`,
- `mappingCone.fst φ : Cocycle (mappingCone φ) F 1` and
- `mappingCone.snd φ : Cochain (mappingCone φ) G 0`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v v'

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

section

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    {F G : CochainComplex C ι} (φ : F ⟶ G)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
  body: by
    rintro i _ rfl
    infer_instance

中文:
实例 [forall
  签名: p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
  定义体: by
    rintro i _ rfl
    infer_instance

Depends on / 依赖: _comp, _naturality_assoc, comp_id, infer_instance, leftRightHomologyComparison, rightHomologyMap
-/
instance [forall p, HasBinaryBiproduct (F.X (p + 1)) (G.X p)] :
    HasHomotopyCofiber φ where
  hasBinaryBiproduct := by
    rintro i _ rfl
    infer_instance

end

variable {F G : CochainComplex C Int} (φ : F ⟶ G)
variable [HasHomotopyCofiber φ]

/--
Definition of `mappingCone` / `mappingCone` 的定义

English:
definition mappingCone
  signature: : CochainComplex C Int
  body: homotopyCofiber φ

中文:
定义 mappingCone
  签名: : CochainComplex C 整数
  定义体: homotopyCofiber φ

Depends on / 依赖: homotopyCofiber
-/
noncomputable def mappingCone : CochainComplex C Int := homotopyCofiber φ

namespace mappingCone

open HomComplex

@[simp]
/--
lemma `isZero_X_iff` / 引理 `isZero_X_iff`

English:
lemma isZero_X_iff
  given: (i : Int)
  proof: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  rw [← biprod_isZero_iff]
  exact (homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff

中文:
引理 isZero_X_iff
  条件: (i : 整数)
  证明: by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  rw [← biprod_isZero_iff]
  exact (homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff

Depends on / 依赖: HasHomotopyCofiber, HasHomotopyCofiber.hasBinaryBiproduct, XIsoBiprod, biprod_isZero_iff, hasBinaryBiproduct, homotopyCofiber, homotopyCofiber.XIsoBiprod, isZero_iff
-/
lemma isZero_X_iff (i : Int) :
    IsZero ((mappingCone φ).X i) ↔ IsZero (F.X (i + 1)) ∧ IsZero (G.X i) := by
  have := HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
  rw [← biprod_isZero_iff]
  exact (homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).isZero_iff

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : Cochain F (mappingCone φ) (-1)
  body: Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q (by dsimp; lia))

中文:
定义 inl
  签名: : Cochain F (mappingCone φ) (-1)
  定义体: Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q (by dsimp; lia))

Depends on / 依赖: Cochain, Cochain.mk, homotopyCofiber, homotopyCofiber.inlX
-/
noncomputable def inl : Cochain F (mappingCone φ) (-1) :=
  Cochain.mk (fun p q hpq => homotopyCofiber.inlX φ p q (by dsimp; lia))

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : G ⟶ mappingCone φ
  body: homotopyCofiber.inr φ

中文:
定义 inr
  签名: : G ⟶ mappingCone φ
  定义体: homotopyCofiber.inr φ

Depends on / 依赖: S.homologyData.left, S.homologyData.right, _compatibility, homologyData, homotopyCofiber, homotopyCofiber.inr, infer_instance, leftRightHomologyComparison
-/
noncomputable def inr : G ⟶ mappingCone φ := homotopyCofiber.inr φ

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : Cocycle (mappingCone φ) F 1
  body: Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by lia) (by
    ext p _ rfl
    simp [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1) (by lia) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

中文:
定义 fst
  签名: : Cocycle (mappingCone φ) F 1
  定义体: Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by lia) (by
    ext p _ rfl
    simp [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1) (by lia) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

Depends on / 依赖: Cochain, Cochain.mk, Cocycle, Cocycle.mk, Int.negOnePow, d_fstX, homotopyCofiber, homotopyCofiber.d_fstX, homotopyCofiber.fstX, mappingCone, negOnePow
-/
noncomputable def fst : Cocycle (mappingCone φ) F 1 :=
  Cocycle.mk (Cochain.mk (fun p q hpq => homotopyCofiber.fstX φ p q hpq)) 2 (by lia) (by
    ext p _ rfl
    simp [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1) (by lia) rfl,
      homotopyCofiber.d_fstX φ p (p + 1) (p + 2) rfl, mappingCone,
      show Int.negOnePow 2 = 1 by rfl])

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : Cochain (mappingCone φ) G 0
  body: Cochain.ofHoms (homotopyCofiber.sndX φ)

中文:
定义 snd
  签名: : Cochain (mappingCone φ) G 0
  定义体: Cochain.ofHoms (homotopyCofiber.sndX φ)

Depends on / 依赖: Cochain, Cochain.ofHoms, homotopyCofiber, homotopyCofiber.sndX, ofHoms
-/
noncomputable def snd : Cochain (mappingCone φ) G 0 :=
  Cochain.ofHoms (homotopyCofiber.sndX φ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_v_fst_v` / 引理 `inl_v_fst_v`

English:
lemma inl_v_fst_v
  given: (p q : Int) (hpq : q + 1 = p)
  proof: by
  simp [inl, fst]

中文:
引理 inl_v_fst_v
  条件: (p q : 整数) (hpq : q + 1 = p)
  证明: by
  simp [inl, fst]

Depends on / 依赖: _compatibility, h.left, h.leftRightHomologyComparison, h.right, leftRightHomologyComparison
-/
lemma inl_v_fst_v (p q : Int) (hpq : q + 1 = p) :
    (inl φ).v p q (by rw [← hpq, add_neg_cancel_right]) ≫
      (fst φ : Cochain (mappingCone φ) F 1).v q p hpq = 𝟙 _ := by
  simp [inl, fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_v_snd_v` / 引理 `inl_v_snd_v`

English:
lemma inl_v_snd_v
  given: (p q : Int) (hpq : p + (-1) = q)
  proof: by
  simp [inl, snd]

中文:
引理 inl_v_snd_v
  条件: (p q : 整数) (hpq : p + (-1) = q)
  证明: by
  simp [inl, snd]

Depends on / 依赖: Iso.refl, Iso.symm, Iso.trans, LeftHomologyData, LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso, RightHomologyData, RightHomologyData.homologyIso, RightHomologyData.rightHomologyIso, S.homologyData, _comp, _comp_assoc, _comp_iso_hom_comp_rightHomologyMap, _eq_leftHomologpMap, homologyData, homologyIso, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyMapIso
-/
lemma inl_v_snd_v (p q : Int) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q) = 0 := by
  simp [inl, snd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_f_fst_v` / 引理 `inr_f_fst_v`

English:
lemma inr_f_fst_v
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [inr, fst]

中文:
引理 inr_f_fst_v
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [inr, fst]
-/
lemma inr_f_fst_v (p q : Int) (hpq : p + 1 = q) :
    (inr φ).f p ≫ (fst φ).1.v p q hpq = 0 := by
  simp [inr, fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_f_snd_v` / 引理 `inr_f_snd_v`

English:
lemma inr_f_snd_v
  given: (p : Int)
  proof: by
  simp [inr, snd]

@[simp]

中文:
引理 inr_f_snd_v
  条件: (p : 整数)
  证明: by
  simp [inr, snd]

@[simp]
-/
lemma inr_f_snd_v (p : Int) :
    (inr φ).f p ≫ (snd φ).v p p (add_zero p) = 𝟙 _ := by
  simp [inr, snd]

@[simp]
/--
lemma `inl_fst` / 引理 `inl_fst`

English:
lemma inl_fst
  proof: by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) p (p - 1) p rfl (by lia)]

@[simp]

中文:
引理 inl_fst
  证明: by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) p (p - 1) p rfl (by lia)]

@[simp]

Depends on / 依赖: Cochain, Cochain.comp_v, comp_v, neg_add_cancel
-/
lemma inl_fst :
    (inl φ).comp (fst φ).1 (neg_add_cancel 1) = Cochain.ofHom (𝟙 F) := by
  ext p
  simp [Cochain.comp_v _ _ (neg_add_cancel 1) p (p - 1) p rfl (by lia)]

@[simp]
/--
lemma `inl_snd` / 引理 `inl_snd`

English:
lemma inl_snd
  proof: by
  ext
  simp

@[simp]

中文:
引理 inl_snd
  证明: by
  ext
  simp

@[simp]
-/
lemma inl_snd :
    (inl φ).comp (snd φ) (add_zero (-1)) = 0 := by
  ext
  simp

@[simp]
/--
lemma `inr_fst` / 引理 `inr_fst`

English:
lemma inr_fst
  proof: by
  ext
  simp

@[simp]

中文:
引理 inr_fst
  证明: by
  ext
  simp

@[simp]
-/
lemma inr_fst :
    (Cochain.ofHom (inr φ)).comp (fst φ).1 (zero_add 1) = 0 := by
  ext
  simp

@[simp]
/--
lemma `inr_snd` / 引理 `inr_snd`

English:
lemma inr_snd
  proof: by cat_disch

中文:
引理 inr_snd
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma inr_snd :
    (Cochain.ofHom (inr φ)).comp (snd φ) (zero_add 0) = Cochain.ofHom (𝟙 G) := by cat_disch

/-! In order to obtain identities of cochains involving `inl`, `inr`, `fst` and `snd`,
it is often convenient to use an `ext` lemma, and use simp lemmas like `inl_v_f_fst_v`,
but it is sometimes possible to get identities of cochains by using rewrites of
identities of cochains like `inl_fst`. Then, similarly as in category theory,
if we associate the compositions of cochains to the right as much as possible,
it is also interesting to have `reassoc` variants of lemmas, like `inl_fst_assoc`. -/

@[simp]
/--
lemma `inl_fst_assoc` / 引理 `inl_fst_assoc`

English:
lemma inl_fst_assoc
  given: {K : CochainComplex C Int} {d e : Int} (γ : Cochain F K d) (he : 1 + d = e)
  proof: by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (by lia) (by lia)]; rw [inl_fst]; rw [Cochain.id_comp]

@[simp]

中文:
引理 inl_fst_assoc
  条件: {K : CochainComplex C 整数} {d e : 整数} (γ : Cochain F K d) (he : 1 + d = e)
  证明: by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (by lia) (by lia)]; rw [inl_fst]; rw [Cochain.id_comp]

@[simp]

Depends on / 依赖: Cochain, Cochain.comp_assoc, Cochain.id_comp, comp_assoc, id_comp, inl_fst, neg_add_cancel
-/
lemma inl_fst_assoc {K : CochainComplex C Int} {d e : Int} (γ : Cochain F K d) (he : 1 + d = e) :
    (inl φ).comp ((fst φ).1.comp γ he) (by rw [← he, neg_add_cancel_left]) = γ := by
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (by lia) (by lia)]; rw [inl_fst]; rw [Cochain.id_comp]

@[simp]
/--
lemma `inl_snd_assoc` / 引理 `inl_snd_assoc`

English:
lemma inl_snd_assoc
  statement: {K : CochainComplex C Int} {d e f : Int} (γ : Cochain G K d)
  proof: by
  obtain rfl : e = d := by lia
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain]; rw [inl_snd]; rw [Cochain.zero_comp]

@[simp]

中文:
引理 inl_snd_assoc
  结论: {K : CochainComplex C 整数} {d e f : 整数} (γ : Cochain G K d)
  证明: by
  obtain rfl : e = d := by lia
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain]; rw [inl_snd]; rw [Cochain.zero_comp]

@[simp]

Depends on / 依赖: Cochain, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.zero_comp, comp_assoc_of_second_is_zero_cochain, inl_snd, zero_comp
-/
lemma inl_snd_assoc {K : CochainComplex C Int} {d e f : Int} (γ : Cochain G K d)
    (he : 0 + d = e) (hf : -1 + e = f) :
    (inl φ).comp ((snd φ).comp γ he) hf = 0 := by
  obtain rfl : e = d := by lia
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain]; rw [inl_snd]; rw [Cochain.zero_comp]

@[simp]
/--
lemma `inr_fst_assoc` / 引理 `inr_fst_assoc`

English:
lemma inr_fst_assoc
  statement: {K : CochainComplex C Int} {d e f : Int} (γ : Cochain F K d)
  proof: by
  obtain rfl : e = f := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_fst]; rw [Cochain.zero_comp]

@[simp]

中文:
引理 inr_fst_assoc
  结论: {K : CochainComplex C 整数} {d e f : 整数} (γ : Cochain F K d)
  证明: by
  obtain rfl : e = f := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_fst]; rw [Cochain.zero_comp]

@[simp]

Depends on / 依赖: Cochain, Cochain.comp_assoc_of_first_is_zero_cochain, Cochain.zero_comp, comp_assoc_of_first_is_zero_cochain, inr_fst, zero_comp
-/
lemma inr_fst_assoc {K : CochainComplex C Int} {d e f : Int} (γ : Cochain F K d)
    (he : 1 + d = e) (hf : 0 + e = f) :
    (Cochain.ofHom (inr φ)).comp ((fst φ).1.comp γ he) hf = 0 := by
  obtain rfl : e = f := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_fst]; rw [Cochain.zero_comp]

@[simp]
/--
lemma `inr_snd_assoc` / 引理 `inr_snd_assoc`

English:
lemma inr_snd_assoc
  given: {K : CochainComplex C Int} {d e : Int} (γ : Cochain G K d) (he : 0 + d = e)
  proof: by
  obtain rfl : d = e := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_snd]; rw [Cochain.id_comp]

中文:
引理 inr_snd_assoc
  条件: {K : CochainComplex C 整数} {d e : 整数} (γ : Cochain G K d) (he : 0 + d = e)
  证明: by
  obtain rfl : d = e := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_snd]; rw [Cochain.id_comp]

Depends on / 依赖: Cochain, Cochain.comp_assoc_of_first_is_zero_cochain, Cochain.id_comp, comp_assoc_of_first_is_zero_cochain, id_comp, inr_snd
-/
lemma inr_snd_assoc {K : CochainComplex C Int} {d e : Int} (γ : Cochain G K d) (he : 0 + d = e) :
    (Cochain.ofHom (inr φ)).comp ((snd φ).comp γ he) (by simp only [← he, zero_add]) = γ := by
  obtain rfl : d = e := by lia
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]; rw [inr_snd]; rw [Cochain.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext_to` / 引理 `ext_to`

English:
lemma ext_to
  statement: (i j : Int) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
  proof: homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using! h₂)

中文:
引理 ext_to
  结论: (i j : 整数) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
  证明: homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using! h₂)

Depends on / 依赖: ext_to_X, homotopyCofiber, homotopyCofiber.ext_to_X
-/
lemma ext_to (i j : Int) (hij : i + 1 = j) {A : C} {f g : A ⟶ (mappingCone φ).X i}
    (h₁ : f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij)
    (h₂ : f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i)) :
    f = g :=
  homotopyCofiber.ext_to_X φ i j hij h₁ (by simpa [snd] using! h₂)

/--
lemma `ext_to_iff` / 引理 `ext_to_iff`

English:
lemma ext_to_iff
  given: (i j : Int) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i)
  proof: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

中文:
引理 ext_to_iff
  条件: (i j : 整数) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i)
  证明: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

Depends on / 依赖: ext_to
-/
lemma ext_to_iff (i j : Int) (hij : i + 1 = j) {A : C} (f g : A ⟶ (mappingCone φ).X i) :
    f = g ↔ f ≫ (fst φ).1.v i j hij = g ≫ (fst φ).1.v i j hij ∧
      f ≫ (snd φ).v i i (add_zero i) = g ≫ (snd φ).v i i (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_to φ i j hij h₁ h₂

/--
lemma `ext_from` / 引理 `ext_from`

English:
lemma ext_from
  statement: (i j : Int) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
  proof: homotopyCofiber.ext_from_X φ i j hij h₁ h₂

中文:
引理 ext_from
  结论: (i j : 整数) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
  证明: homotopyCofiber.ext_from_X φ i j hij h₁ h₂

Depends on / 依赖: ext_from_X, homotopyCofiber, homotopyCofiber.ext_from_X
-/
lemma ext_from (i j : Int) (hij : j + 1 = i) {A : C} {f g : (mappingCone φ).X j ⟶ A}
    (h₁ : (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g)
    (h₂ : (inr φ).f j ≫ f = (inr φ).f j ≫ g) :
    f = g :=
  homotopyCofiber.ext_from_X φ i j hij h₁ h₂

/--
lemma `ext_from_iff` / 引理 `ext_from_iff`

English:
lemma ext_from_iff
  given: (i j : Int) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A)
  proof: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

中文:
引理 ext_from_iff
  条件: (i j : 整数) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A)
  证明: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

Depends on / 依赖: ext_from
-/
lemma ext_from_iff (i j : Int) (hij : j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) :
    f = g ↔ (inl φ).v i j (by lia) ≫ f = (inl φ).v i j (by lia) ≫ g ∧
      (inr φ).f j ≫ f = (inr φ).f j ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact ext_from φ i j hij h₁ h₂

/--
lemma `decomp_to` / 引理 `decomp_to`

English:
lemma decomp_to
  given: {i : Int} {A : C} (f : A ⟶ (mappingCone φ).X i) (j : Int) (hij : i + 1 = j)
  proof: ⟨f ≫ (fst φ).1.v i j hij, f ≫ (snd φ).v i i (add_zero i),
    by apply ext_to φ i j hij <;> simp⟩

中文:
引理 decomp_to
  条件: {i : 整数} {A : C} (f : A ⟶ (mappingCone φ).X i) (j : 整数) (hij : i + 1 = j)
  证明: ⟨f ≫ (fst φ).1.v i j hij, f ≫ (snd φ).v i i (add_zero i),
    by apply ext_to φ i j hij <;> simp⟩

Depends on / 依赖: add_zero, ext_to
-/
lemma decomp_to {i : Int} {A : C} (f : A ⟶ (mappingCone φ).X i) (j : Int) (hij : i + 1 = j) :
    exists (a : A ⟶ F.X j) (b : A ⟶ G.X i), f = a ≫ (inl φ).v j i (by lia) + b ≫ (inr φ).f i :=
  ⟨f ≫ (fst φ).1.v i j hij, f ≫ (snd φ).v i i (add_zero i),
    by apply ext_to φ i j hij <;> simp⟩

/--
lemma `decomp_from` / 引理 `decomp_from`

English:
lemma decomp_from
  given: {j : Int} {A : C} (f : (mappingCone φ).X j ⟶ A) (i : Int) (hij : j + 1 = i)
  proof: ⟨(inl φ).v i j (by lia) ≫ f, (inr φ).f j ≫ f,
    by apply ext_from φ i j hij <;> simp⟩

中文:
引理 decomp_from
  条件: {j : 整数} {A : C} (f : (mappingCone φ).X j ⟶ A) (i : 整数) (hij : j + 1 = i)
  证明: ⟨(inl φ).v i j (by lia) ≫ f, (inr φ).f j ≫ f,
    by apply ext_from φ i j hij <;> simp⟩

Depends on / 依赖: ext_from, homologyMap, infer_instance
-/
lemma decomp_from {j : Int} {A : C} (f : (mappingCone φ).X j ⟶ A) (i : Int) (hij : j + 1 = i) :
    exists (a : F.X i ⟶ A) (b : G.X j ⟶ A),
      f = (fst φ).1.v j i hij ≫ a + (snd φ).v j j (add_zero j) ≫ b :=
  ⟨(inl φ).v i j (by lia) ≫ f, (inr φ).f j ≫ f,
    by apply ext_from φ i j hij <;> simp⟩

/--
lemma `ext_cochain_to_iff` / 引理 `ext_cochain_to_iff`

English:
lemma ext_cochain_to_iff
  statement: (i j : Int) (hij : i + 1 = j)
  proof: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by lia)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain

中文:
引理 ext_cochain_to_iff
  结论: (i j : 整数) (hij : i + 1 = j)
  证明: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by lia)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.comp_zero_cochain_v, Cochain.congr_v, comp_v, comp_zero_cochain_v, congr_v, ext_to_iff, replace
-/
lemma ext_cochain_to_iff (i j : Int) (hij : i + 1 = j)
    {K : CochainComplex C Int} {γ₁ γ₂ : Cochain K (mappingCone φ) i} :
    γ₁ = γ₂ ↔ γ₁.comp (fst φ).1 hij = γ₂.comp (fst φ).1 hij ∧
      γ₁.comp (snd φ) (add_zero i) = γ₂.comp (snd φ) (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by lia)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain.comp_zero_cochain_v] at h₂
    exact ⟨h₁, h₂⟩

/--
lemma `ext_cochain_from_iff` / 引理 `ext_cochain_from_iff`

English:
lemma ext_cochain_from_iff
  statement: (i j : Int) (hij : i + 1 = j)
  proof: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by lia)
    replace h₂ := Cochain.congr_v h₂ p q (by lia)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by lia) hpq] at h₁
    

中文:
引理 ext_cochain_from_iff
  结论: (i j : 整数) (hij : i + 1 = j)
  证明: by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by lia)
    replace h₂ := Cochain.congr_v h₂ p q (by lia)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by lia) hpq] at h₁
    

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.congr_v, Cochain.ofHom_v, Cochain.zero_cochain_comp_v, comp_v, congr_v, ext_from_iff, ofHom_v, replace, zero_cochain_comp_v
-/
lemma ext_cochain_from_iff (i j : Int) (hij : i + 1 = j)
    {K : CochainComplex C Int} {γ₁ γ₂ : Cochain (mappingCone φ) K j} :
    γ₁ = γ₂ ↔
      (inl φ).comp γ₁ (show _ = i by lia) = (inl φ).comp γ₂ (by lia) ∧
        (Cochain.ofHom (inr φ)).comp γ₁ (zero_add j) =
          (Cochain.ofHom (inr φ)).comp γ₂ (zero_add j) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by lia)
    replace h₂ := Cochain.congr_v h₂ p q (by lia)
    simp only [Cochain.comp_v (inl φ) _ _ (p + 1) p q (by lia) hpq] at h₁
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h₂
    exact ⟨h₁, h₂⟩

/--
lemma `id` / 引理 `id`

English:
lemma id
  proof: by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_cancel 1)]

中文:
引理 id
  证明: by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_cancel 1)]

Depends on / 依赖: ext_cochain_from_iff, neg_add_cancel
-/
lemma id :
    (fst φ).1.comp (inl φ) (add_neg_cancel 1) +
      (snd φ).comp (Cochain.ofHom (inr φ)) (add_zero 0) = Cochain.ofHom (𝟙 _) := by
  simp [ext_cochain_from_iff φ (-1) 0 (neg_add_cancel 1)]

/--
lemma `id_X` / 引理 `id_X`

English:
lemma id_X
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_cancel 1) p q p hpq (by lia)]
    using Cochain.congr_v (id φ) p p (add_zero p)

中文:
引理 id_X
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_cancel 1) p q p hpq (by lia)]
    using Cochain.congr_v (id φ) p p (add_zero p)

Depends on / 依赖: Cochain, Cochain.add_v, Cochain.comp_v, Cochain.comp_zero_cochain_v, Cochain.congr_v, Cochain.ofHom_v, add_neg_cancel, add_v, add_zero, comp_v, comp_zero_cochain_v, congr_v, id_f, ofHom_v
-/
lemma id_X (p q : Int) (hpq : p + 1 = q) :
    (fst φ).1.v p q hpq ≫ (inl φ).v q p (by lia) +
      (snd φ).v p p (add_zero p) ≫ (inr φ).f p = 𝟙 ((mappingCone φ).X p) := by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_cancel 1) p q p hpq (by lia)]
    using Cochain.congr_v (id φ) p p (add_zero p)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `inl_v_d` / 引理 `inl_v_d`

English:
lemma inl_v_d
  given: (i j k : Int) (hij : i + (-1) = j) (hik : k + (-1) = i)
  proof: by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; lia) (by dsimp; lia)]
  abel

@[reassoc]

中文:
引理 inl_v_d
  条件: (i j k : 整数) (hij : i + (-1) = j) (hik : k + (-1) = i)
  证明: by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; lia) (by dsimp; lia)]
  abel

@[reassoc]

Depends on / 依赖: homotopyCofiber, homotopyCofiber.inlX_d, inlX_d, mappingCone
-/
lemma inl_v_d (i j k : Int) (hij : i + (-1) = j) (hik : k + (-1) = i) :
    (inl φ).v i j hij ≫ (mappingCone φ).d j i =
      φ.f i ≫ (inr φ).f i - F.d i k ≫ (inl φ).v _ _ hik := by
  dsimp [mappingCone, inl, inr]
  rw [homotopyCofiber.inlX_d φ j i k (by dsimp; lia) (by dsimp; lia)]
  abel

@[reassoc]
/--
lemma `inr_f_d` / 引理 `inr_f_d`

English:
lemma inr_f_d
  given: (n₁ n₂ : Int)
  proof: by
  simp

@[reassoc]

中文:
引理 inr_f_d
  条件: (n₁ n₂ : 整数)
  证明: by
  simp

@[reassoc]
-/
lemma inr_f_d (n₁ n₂ : Int) :
    (inr φ).f n₁ ≫ (mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (inr φ).f n₂ := by
  simp

@[reassoc]
/--
lemma `d_fst_v` / 引理 `d_fst_v`

English:
lemma d_fst_v
  given: (i j k : Int) (hij : i + 1 = j) (hjk : j + 1 = k)
  proof: by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]

中文:
引理 d_fst_v
  条件: (i j k : 整数) (hij : i + 1 = j) (hjk : j + 1 = k)
  证明: by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]

Depends on / 依赖: d_fstX, homotopyCofiber, homotopyCofiber.d_fstX
-/
lemma d_fst_v (i j k : Int) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone φ).d i j ≫ (fst φ).1.v j k hjk =
      -(fst φ).1.v i j hij ≫ F.d j k := by
  apply homotopyCofiber.d_fstX

@[reassoc (attr := simp)]
/--
lemma `d_fst_v'` / 引理 `d_fst_v'`

English:
lemma d_fst_v'
  given: (i j : Int) (hij : i + 1 = j)
  proof: d_fst_v φ (i - 1) i j (by lia) hij

中文:
引理 d_fst_v'
  条件: (i j : 整数) (hij : i + 1 = j)
  证明: d_fst_v φ (i - 1) i j (by lia) hij

Depends on / 依赖: d_fst_v
-/
lemma d_fst_v' (i j : Int) (hij : i + 1 = j) :
    (mappingCone φ).d (i - 1) i ≫ (fst φ).1.v i j hij =
      -(fst φ).1.v (i - 1) i (by lia) ≫ F.d i j :=
  d_fst_v φ (i - 1) i j (by lia) hij

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `d_snd_v` / 引理 `d_snd_v`

English:
lemma d_snd_v
  given: (i j : Int) (hij : i + 1 = j)
  proof: by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]

中文:
引理 d_snd_v
  条件: (i j : 整数) (hij : i + 1 = j)
  证明: by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]

Depends on / 依赖: Cochain, Cochain.ofHoms_v, d_sndX, homotopyCofiber, homotopyCofiber.d_sndX, mappingCone, ofHoms_v
-/
lemma d_snd_v (i j : Int) (hij : i + 1 = j) :
    (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) =
      (fst φ).1.v i j hij ≫ φ.f j + (snd φ).v i i (add_zero i) ≫ G.d i j := by
  dsimp [mappingCone, snd, fst]
  simp only [Cochain.ofHoms_v]
  apply homotopyCofiber.d_sndX

@[reassoc (attr := simp)]
/--
lemma `d_snd_v'` / 引理 `d_snd_v'`

English:
lemma d_snd_v'
  given: (n : Int)
  proof: by
  apply d_snd_v

@[simp]

中文:
引理 d_snd_v'
  条件: (n : 整数)
  证明: by
  apply d_snd_v

@[simp]

Depends on / 依赖: d_snd_v
-/
lemma d_snd_v' (n : Int) :
    (mappingCone φ).d (n - 1) n ≫ (snd φ).v n n (add_zero n) =
    (fst φ : Cochain (mappingCone φ) F 1).v (n - 1) n (by lia) ≫ φ.f n +
      (snd φ).v (n - 1) (n - 1) (add_zero _) ≫ G.d (n - 1) n := by
  apply d_snd_v

@[simp]
/--
lemma `δ_inl` / 引理 `δ_inl`

English:
lemma δ_inl
  proof: by
  ext p
  simp [δ_v (-1) 0 (neg_add_cancel 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by lia) (by lia)]

@[simp]

中文:
引理 δ_inl
  证明: by
  ext p
  simp [δ_v (-1) 0 (neg_add_cancel 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by lia) (by lia)]

@[simp]

Depends on / 依赖: add_zero, inl_v_d, neg_add_cancel
-/
lemma δ_inl :
    δ (-1) 0 (inl φ) = Cochain.ofHom (φ ≫ inr φ) := by
  ext p
  simp [δ_v (-1) 0 (neg_add_cancel 1) (inl φ) p p (add_zero p) _ _ rfl rfl,
    inl_v_d φ p (p - 1) (p + 1) (by lia) (by lia)]

@[simp]
/--
lemma `δ_snd` / 引理 `δ_snd`

English:
lemma δ_snd
  proof: by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

中文:
引理 δ_snd
  证明: by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

Depends on / 依赖: d_snd_v
-/
lemma δ_snd :
    δ 0 1 (snd φ) = -(fst φ).1.comp (Cochain.ofHom φ) (add_zero 1) := by
  ext p q hpq
  simp [d_snd_v φ p q hpq]

section

variable {K : CochainComplex C Int} {n m : Int}

/--
Definition of `descCochain` / `descCochain` 的定义

English:
definition descCochain
  signature: (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)
  body: (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

中文:
定义 descCochain
  签名: (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)
  定义体: (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

Depends on / 依赖: add_comm, zero_add
-/
noncomputable def descCochain (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n) :
    Cochain (mappingCone φ) K n :=
  (fst φ).1.comp α (by rw [← h, add_comm]) + (snd φ).comp β (zero_add n)

variable (α : Cochain F K m) (β : Cochain G K n) (h : m + 1 = n)

@[simp]
/--
lemma `inl_descCochain` / 引理 `inl_descCochain`

English:
lemma inl_descCochain
  proof: by
  simp [descCochain]

@[simp]

中文:
引理 inl_descCochain
  证明: by
  simp [descCochain]

@[simp]

Depends on / 依赖: descCochain
-/
lemma inl_descCochain :
    (inl φ).comp (descCochain φ α β h) (by lia) = α := by
  simp [descCochain]

@[simp]
/--
lemma `inr_descCochain` / 引理 `inr_descCochain`

English:
lemma inr_descCochain
  proof: by
  simp [descCochain]

@[reassoc (attr := simp)]

中文:
引理 inr_descCochain
  证明: by
  simp [descCochain]

@[reassoc (attr := simp)]

Depends on / 依赖: descCochain
-/
lemma inr_descCochain :
    (Cochain.ofHom (inr φ)).comp (descCochain φ α β h) (zero_add n) = β := by
  simp [descCochain]

@[reassoc (attr := simp)]
/--
lemma `inl_v_descCochain_v` / 引理 `inl_v_descCochain_v`

English:
lemma inl_v_descCochain_v
  given: (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃)
  proof: by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by lia) p₁ p₂ p₃
    (by lia) (by lia)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]

中文:
引理 inl_v_descCochain_v
  条件: (p₁ p₂ p₃ : 整数) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃)
  证明: by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by lia) p₁ p₂ p₃
    (by lia) (by lia)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.congr_v, comp_v, congr_v, inl_descCochain
-/
lemma inl_v_descCochain_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + (-1) = p₂) (h₂₃ : p₂ + n = p₃) :
    (inl φ).v p₁ p₂ h₁₂ ≫ (descCochain φ α β h).v p₂ p₃ h₂₃ =
        α.v p₁ p₃ (by rw [← h₂₃, ← h₁₂, ← h, add_comm m, add_assoc, neg_add_cancel_left]) := by
  simpa only [Cochain.comp_v _ _ (show -1 + n = m by lia) p₁ p₂ p₃
    (by lia) (by lia)] using
      Cochain.congr_v (inl_descCochain φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]
/--
lemma `inr_f_descCochain_v` / 引理 `inr_f_descCochain_v`

English:
lemma inr_f_descCochain_v
  given: (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂)
  proof: by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by lia)

中文:
引理 inr_f_descCochain_v
  条件: (p₁ p₂ : 整数) (h₁₂ : p₁ + n = p₂)
  证明: by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by lia)

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.congr_v, Cochain.ofHom_v, add_zero, comp_v, congr_v, inr_descCochain, ofHom_v, zero_add
-/
lemma inr_f_descCochain_v (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) :
    (inr φ).f p₁ ≫ (descCochain φ α β h).v p₁ p₂ h₁₂ = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (zero_add n) p₁ p₁ p₂ (add_zero p₁) h₁₂, Cochain.ofHom_v]
    using Cochain.congr_v (inr_descCochain φ α β h) p₁ p₂ (by lia)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_descCochain` / 引理 `δ_descCochain`

English:
lemma δ_descCochain
  given: (n' : Int) (hn' : n + 1 = n')
  proof: by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (fst φ).1 α _ 2 n n' hn' (by lia) (by lia),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_as

中文:
引理 δ_descCochain
  条件: (n' : 整数) (hn' : n + 1 = n')
  证明: by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (fst φ).1 α _ 2 n n' hn' (by lia) (by lia),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_as

Depends on / 依赖: Cochain, Cochain.comp_add, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_neg, Cochain.comp_units_smul, Cochain.neg_comp, Cochain.zero_comp, Cocycle, Int.negOnePow_succ, Units.neg_smul, add_zero, comp_add, comp_assoc_of_second_is_zero_cochain, comp_neg, comp_units_smul, descCochain, negOnePow_succ, neg_comp, neg_smul, smul_neg
-/
lemma δ_descCochain (n' : Int) (hn' : n + 1 = n') :
    δ n n' (descCochain φ α β h) =
      (fst φ).1.comp (δ m n α +
          n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (by lia) +
      (snd φ).comp (δ n n' β) (zero_add n') := by
  dsimp only [descCochain]
  simp only [δ_add, Cochain.comp_add, δ_comp (fst φ).1 α _ 2 n n' hn' (by lia) (by lia),
    Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero,
    δ_comp (snd φ) β (zero_add n) 1 n' n' hn' (zero_add 1) hn', δ_snd, Cochain.neg_comp,
    smul_neg, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_units_smul, ← hn',
    Int.negOnePow_succ, Units.neg_smul, Cochain.comp_neg]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle (mappingCone φ) K n` that is
constructed from `α : Cochain F K m` (with `m + 1 = n`) and `β : Cocycle F K n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
/--
Definition of `descCocycle` / `descCocycle` 的定义

English:
definition descCocycle
  signature: {K : CochainComplex C Int} {n m : Int}
  body: Cocycle.mk (descCochain φ α β.1 h) (n + 1) rfl
    (by simp [δ_descCochain _ _ _ _ _ rfl, eq, Int.negOnePow_succ])

中文:
定义 descCocycle
  签名: {K : CochainComplex C 整数} {n m : 整数}
  定义体: Cocycle.mk (descCochain φ α β.1 h) (n + 1) rfl
    (by simp [δ_descCochain _ _ _ _ _ rfl, eq, Int.negOnePow_succ])

Depends on / 依赖: Cocycle, Cocycle.mk, Int.negOnePow_succ, descCochain, negOnePow_succ
-/
noncomputable def descCocycle {K : CochainComplex C Int} {n m : Int}
    (α : Cochain F K m) (β : Cocycle G K n)
    (h : m + 1 = n) (eq : δ m n α = n.negOnePow • (Cochain.ofHom φ).comp β.1 (zero_add n)) :
    Cocycle (mappingCone φ) K n :=
  Cocycle.mk (descCochain φ α β.1 h) (n + 1) rfl
    (by simp [δ_descCochain _ _ _ _ _ rfl, eq, Int.negOnePow_succ])

section

variable {K : CochainComplex C Int}

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (α : Cochain F K (-1)) (β : G ⟶ K)
  body: Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_cancel 1) (by simp [eq]))

中文:
定义 desc
  签名: (α : Cochain F K (-1)) (β : G ⟶ K)
  定义体: Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_cancel 1) (by simp [eq]))

Depends on / 依赖: Cocycle, Cocycle.homOf, Cocycle.ofHom, descCocycle, neg_add_cancel
-/
noncomputable def desc (α : Cochain F K (-1)) (β : G ⟶ K)
    (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β)) : mappingCone φ ⟶ K :=
  Cocycle.homOf (descCocycle φ α (Cocycle.ofHom β) (neg_add_cancel 1) (by simp [eq]))

variable (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

@[simp]
/--
lemma `ofHom_desc` / 引理 `ofHom_desc`

English:
lemma ofHom_desc
  proof: by
  simp [desc]

@[reassoc (attr := simp)]

中文:
引理 ofHom_desc
  证明: by
  simp [desc]

@[reassoc (attr := simp)]
-/
lemma ofHom_desc :
    Cochain.ofHom (desc φ α β eq) = descCochain φ α (Cochain.ofHom β) (neg_add_cancel 1) := by
  simp [desc]

@[reassoc (attr := simp)]
/--
lemma `inl_v_desc_f` / 引理 `inl_v_desc_f`

English:
lemma inl_v_desc_f
  given: (p q : Int) (h : p + (-1) = q)
  proof: by
  simp [desc]

中文:
引理 inl_v_desc_f
  条件: (p q : 整数) (h : p + (-1) = q)
  证明: by
  simp [desc]
-/
lemma inl_v_desc_f (p q : Int) (h : p + (-1) = q) :
    (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h := by
  simp [desc]

/--
lemma `inl_desc` / 引理 `inl_desc`

English:
lemma inl_desc
  proof: by
  simp

@[reassoc (attr := simp)]

中文:
引理 inl_desc
  证明: by
  simp

@[reassoc (attr := simp)]
-/
lemma inl_desc :
    (inl φ).comp (Cochain.ofHom (desc φ α β eq)) (add_zero _) = α := by
  simp

@[reassoc (attr := simp)]
/--
lemma `inr_f_desc_f` / 引理 `inr_f_desc_f`

English:
lemma inr_f_desc_f
  given: (p : Int)
  proof: by
  simp [desc]

@[reassoc (attr := simp)]

中文:
引理 inr_f_desc_f
  条件: (p : 整数)
  证明: by
  simp [desc]

@[reassoc (attr := simp)]
-/
lemma inr_f_desc_f (p : Int) :
    (inr φ).f p ≫ (desc φ α β eq).f p = β.f p := by
  simp [desc]

@[reassoc (attr := simp)]
/--
lemma `inr_desc` / 引理 `inr_desc`

English:
lemma inr_desc
  statement: inr φ ≫ desc φ α β eq = β
  proof: by cat_disch

中文:
引理 inr_desc
  结论: inr φ ≫ desc φ α β eq = β
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma inr_desc : inr φ ≫ desc φ α β eq = β := by cat_disch

/--
lemma `desc_f` / 引理 `desc_f`

English:
lemma desc_f
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [ext_from_iff _ _ _ hpq]

中文:
引理 desc_f
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [ext_from_iff _ _ _ hpq]

Depends on / 依赖: ext_from_iff
-/
lemma desc_f (p q : Int) (hpq : p + 1 = q) :
    (desc φ α β eq).f p = (fst φ).1.v p q hpq ≫ α.v q p (by lia) +
      (snd φ).v p p (add_zero p) ≫ β.f p := by
  simp [ext_from_iff _ _ _ hpq]

end

/--
Definition of `descHomotopy` / `descHomotopy` 的定义

English:
definition descHomotopy
  signature: {K : CochainComplex C Int} (f₁ f₂ : mappingCone φ ⟶ K)
  body: (Cochain.equivHomotopy f₁ f₂).symm ⟨descCochain φ γ₁ γ₂ (by simp), by
    simp only [Cochain.ofHom_comp] at h₂
    simp [ext_cochain_from_iff _ _ _ (neg_add_cancel 1),
      δ_descCochain _ _ _ _ _ (neg_add_cancel 1), h₁, h₂]⟩

中文:
定义 descHomotopy
  签名: {K : CochainComplex C 整数} (f₁ f₂ : mappingCone φ ⟶ K)
  定义体: (Cochain.equivHomotopy f₁ f₂).symm ⟨descCochain φ γ₁ γ₂ (by simp), by
    simp only [Cochain.ofHom_comp] at h₂
    simp [ext_cochain_from_iff _ _ _ (neg_add_cancel 1),
      δ_descCochain _ _ _ _ _ (neg_add_cancel 1), h₁, h₂]⟩

Depends on / 依赖: Cochain, Cochain.equivHomotopy, Cochain.ofHom_comp, descCochain, equivHomotopy, ext_cochain_from_iff, neg_add_cancel, ofHom_comp
-/
noncomputable def descHomotopy {K : CochainComplex C Int} (f₁ f₂ : mappingCone φ ⟶ K)
    (γ₁ : Cochain F K (-2)) (γ₂ : Cochain G K (-1))
    (h₁ : (inl φ).comp (Cochain.ofHom f₁) (add_zero (-1)) =
      δ (-2) (-1) γ₁ + (Cochain.ofHom φ).comp γ₂ (zero_add (-1)) +
      (inl φ).comp (Cochain.ofHom f₂) (add_zero (-1)))
    (h₂ : Cochain.ofHom (inr φ ≫ f₁) = δ (-1) 0 γ₂ + Cochain.ofHom (inr φ ≫ f₂)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨descCochain φ γ₁ γ₂ (by simp), by
    simp only [Cochain.ofHom_comp] at h₂
    simp [ext_cochain_from_iff _ _ _ (neg_add_cancel 1),
      δ_descCochain _ _ _ _ _ (neg_add_cancel 1), h₁, h₂]⟩

section

variable {K : CochainComplex C Int} {n m : Int}

/--
Definition of `liftCochain` / `liftCochain` 的定义

English:
definition liftCochain
  signature: (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)
  body: α.comp (inl φ) (by lia) + β.comp (Cochain.ofHom (inr φ)) (add_zero n)

中文:
定义 liftCochain
  签名: (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)
  定义体: α.comp (inl φ) (by lia) + β.comp (Cochain.ofHom (inr φ)) (add_zero n)

Depends on / 依赖: Cochain, Cochain.ofHom, add_zero
-/
noncomputable def liftCochain (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m) :
    Cochain K (mappingCone φ) n :=
  α.comp (inl φ) (by lia) + β.comp (Cochain.ofHom (inr φ)) (add_zero n)

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

@[simp]
/--
lemma `liftCochain_fst` / 引理 `liftCochain_fst`

English:
lemma liftCochain_fst
  proof: by
  simp [liftCochain]

@[simp]

中文:
引理 liftCochain_fst
  证明: by
  simp [liftCochain]

@[simp]

Depends on / 依赖: liftCochain
-/
lemma liftCochain_fst :
    (liftCochain φ α β h).comp (fst φ).1 h = α := by
  simp [liftCochain]

@[simp]
/--
lemma `liftCochain_snd` / 引理 `liftCochain_snd`

English:
lemma liftCochain_snd
  proof: by
  simp [liftCochain]

@[reassoc (attr := simp)]

中文:
引理 liftCochain_snd
  证明: by
  simp [liftCochain]

@[reassoc (attr := simp)]

Depends on / 依赖: liftCochain
-/
lemma liftCochain_snd :
    (liftCochain φ α β h).comp (snd φ) (add_zero n) = β := by
  simp [liftCochain]

@[reassoc (attr := simp)]
/--
lemma `liftCochain_v_fst_v` / 引理 `liftCochain_v_fst_v`

English:
lemma liftCochain_v_fst_v
  given: (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃)
  proof: by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]

中文:
引理 liftCochain_v_fst_v
  条件: (p₁ p₂ p₃ : 整数) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃)
  证明: by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.congr_v, comp_v, congr_v, liftCochain_fst
-/
lemma liftCochain_v_fst_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + 1 = p₃) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (fst φ).1.v p₂ p₃ h₂₃ = α.v p₁ p₃ (by lia) := by
  simpa only [Cochain.comp_v _ _ h p₁ p₂ p₃ h₁₂ h₂₃]
    using Cochain.congr_v (liftCochain_fst φ α β h) p₁ p₃ (by lia)

@[reassoc (attr := simp)]
/--
lemma `liftCochain_v_snd_v` / 引理 `liftCochain_v_snd_v`

English:
lemma liftCochain_v_snd_v
  given: (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂)
  proof: by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by lia)

中文:
引理 liftCochain_v_snd_v
  条件: (p₁ p₂ : 整数) (h₁₂ : p₁ + n = p₂)
  证明: by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by lia)

Depends on / 依赖: Cochain, Cochain.comp_v, Cochain.congr_v, add_zero, comp_v, congr_v, liftCochain_snd
-/
lemma liftCochain_v_snd_v (p₁ p₂ : Int) (h₁₂ : p₁ + n = p₂) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (snd φ).v p₂ p₂ (add_zero p₂) = β.v p₁ p₂ h₁₂ := by
  simpa only [Cochain.comp_v _ _ (add_zero n) p₁ p₂ p₂ h₁₂ (add_zero p₂)]
    using Cochain.congr_v (liftCochain_snd φ α β h) p₁ p₂ (by lia)

/--
lemma `δ_liftCochain` / 引理 `δ_liftCochain`

English:
lemma δ_liftCochain
  given: (m' : Int) (hm' : m + 1 = m')
  proof: by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp α (inl φ) _ m' _ _ h hm' (neg_add_cancel 1),
    δ_comp_zero_cochain _ _ _ h, δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochai

中文:
引理 δ_liftCochain
  条件: (m' : 整数) (hm' : m + 1 = m')
  证明: by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp α (inl φ) _ m' _ _ h hm' (neg_add_cancel 1),
    δ_comp_zero_cochain _ _ _ h, δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochai

Depends on / 依赖: Cochain, Cochain.add_comp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_zero, Cochain.ofHom_comp, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, add_comp, comp_assoc_of_second_is_zero_cochain, comp_zero, liftCochain, negOnePow_neg, negOnePow_one, neg_add_cancel, neg_smul, ofHom_comp, one_smul, zero_add
-/
lemma δ_liftCochain (m' : Int) (hm' : m + 1 = m') :
    δ n m (liftCochain φ α β h) = -(δ m m' α).comp (inl φ) (by lia) +
      (δ n m β + α.comp (Cochain.ofHom φ) (add_zero m)).comp
        (Cochain.ofHom (inr φ)) (add_zero m) := by
  dsimp only [liftCochain]
  simp only [δ_add, δ_comp α (inl φ) _ m' _ _ h hm' (neg_add_cancel 1),
    δ_comp_zero_cochain _ _ _ h, δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

end

/-- Given `φ : F ⟶ G`, this is the cocycle in `Cocycle K (mappingCone φ) n` that is
constructed from `α : Cochain K F m` (with `n + 1 = m`) and `β : Cocycle K G n`,
when a suitable cocycle relation is satisfied. -/
@[simps!]
/--
Definition of `liftCocycle` / `liftCocycle` 的定义

English:
definition liftCocycle
  signature: {K : CochainComplex C Int} {n m : Int}
  body: Cocycle.mk (liftCochain φ α β h) m h (by
    simp only [δ_liftCochain φ α β h (m + 1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

中文:
定义 liftCocycle
  签名: {K : CochainComplex C 整数} {n m : 整数}
  定义体: Cocycle.mk (liftCochain φ α β h) m h (by
    simp only [δ_liftCochain φ α β h (m + 1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

Depends on / 依赖: Cochain, Cochain.zero_comp, Cocycle, Cocycle.mk, add_zero, liftCochain, neg_zero, zero_comp
-/
noncomputable def liftCocycle {K : CochainComplex C Int} {n m : Int}
    (α : Cocycle K F m) (β : Cochain K G n) (h : n + 1 = m)
    (eq : δ n m β + α.1.comp (Cochain.ofHom φ) (add_zero m) = 0) :
    Cocycle K (mappingCone φ) n :=
  Cocycle.mk (liftCochain φ α β h) m h (by
    simp only [δ_liftCochain φ α β h (m + 1) rfl, eq,
      Cocycle.δ_eq_zero, Cochain.zero_comp, neg_zero, add_zero])

section

variable {K : CochainComplex C Int} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: :
  body: Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]

中文:
定义 lift
  签名: :
  定义体: Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]

Depends on / 依赖: Cocycle, Cocycle.homOf, HomologyData, HomologyData.op_left, HomologyMapData, HomologyMapData.op_left, Iso.hom_inv_id, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, RightHomologyMapData, RightHomologyMapData.op_, comm_assoc, comp_id, hom_inv_id, homologyMap, liftCocycle, op.homologyMap, op_left, unop_inj
-/
noncomputable def lift :
    K ⟶ mappingCone φ :=
  Cocycle.homOf (liftCocycle φ α β (zero_add 1) eq)

@[simp]
/--
lemma `ofHom_lift` / 引理 `ofHom_lift`

English:
lemma ofHom_lift
  proof: by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

@[reassoc (attr := simp)]

中文:
引理 ofHom_lift
  证明: by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

@[reassoc (attr := simp)]

Depends on / 依赖: Cocycle, Cocycle.cochain_ofHom_homOf_eq_coe, cochain_ofHom_homOf_eq_coe, liftCocycle_coe
-/
lemma ofHom_lift :
    Cochain.ofHom (lift φ α β eq) = liftCochain φ α β (zero_add 1) := by
  simp only [lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

@[reassoc (attr := simp)]
/--
lemma `lift_f_fst_v` / 引理 `lift_f_fst_v`

English:
lemma lift_f_fst_v
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [lift]

中文:
引理 lift_f_fst_v
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [lift]
-/
lemma lift_f_fst_v (p q : Int) (hpq : p + 1 = q) :
    (lift φ α β eq).f p ≫ (fst φ).1.v p q hpq = α.1.v p q hpq := by
  simp [lift]

/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  proof: by simp

@[reassoc (attr := simp)]

中文:
引理 lift_fst
  证明: by simp

@[reassoc (attr := simp)]
-/
lemma lift_fst :
    (Cochain.ofHom (lift φ α β eq)).comp (fst φ).1 (zero_add 1) = α.1 := by simp

@[reassoc (attr := simp)]
/--
lemma `lift_f_snd_v` / 引理 `lift_f_snd_v`

English:
lemma lift_f_snd_v
  given: (p q : Int) (hpq : p + 0 = q)
  proof: by
  obtain rfl : q = p := by lia
  simp [lift]

中文:
引理 lift_f_snd_v
  条件: (p q : 整数) (hpq : p + 0 = q)
  证明: by
  obtain rfl : q = p := by lia
  simp [lift]
-/
lemma lift_f_snd_v (p q : Int) (hpq : p + 0 = q) :
    (lift φ α β eq).f p ≫ (snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : q = p := by lia
  simp [lift]

/--
lemma `lift_snd` / 引理 `lift_snd`

English:
lemma lift_snd
  proof: by simp

中文:
引理 lift_snd
  证明: by simp
-/
lemma lift_snd :
    (Cochain.ofHom (lift φ α β eq)).comp (snd φ) (zero_add 0) = β := by simp

/--
lemma `lift_f` / 引理 `lift_f`

English:
lemma lift_f
  given: (p q : Int) (hpq : p + 1 = q)
  proof: by
  simp [ext_to_iff _ _ _ hpq]

中文:
引理 lift_f
  条件: (p q : 整数) (hpq : p + 1 = q)
  证明: by
  simp [ext_to_iff _ _ _ hpq]

Depends on / 依赖: ext_to_iff
-/
lemma lift_f (p q : Int) (hpq : p + 1 = q) :
    (lift φ α β eq).f p = α.1.v p q hpq ≫
      (inl φ).v q p (by omega) + β.v p p (add_zero p) ≫ (inr φ).f p := by
  simp [ext_to_iff _ _ _ hpq]

end

/--
Definition of `liftHomotopy` / `liftHomotopy` 的定义

English:
definition liftHomotopy
  signature: {K : CochainComplex C Int} (f₁ f₂ : K ⟶ mappingCone φ)
  body: (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_cancel 1), by
    simp [δ_liftCochain _ _ _ _ _ (zero_add 1), ext_cochain_to_iff _ _ _ (zero_add 1), h₁, h₂]⟩

中文:
定义 liftHomotopy
  签名: {K : CochainComplex C 整数} (f₁ f₂ : K ⟶ mappingCone φ)
  定义体: (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_cancel 1), by
    simp [δ_liftCochain _ _ _ _ _ (zero_add 1), ext_cochain_to_iff _ _ _ (zero_add 1), h₁, h₂]⟩

Depends on / 依赖: Cochain, Cochain.equivHomotopy, equivHomotopy, ext_cochain_to_iff, liftCochain, neg_add_cancel, zero_add
-/
noncomputable def liftHomotopy {K : CochainComplex C Int} (f₁ f₂ : K ⟶ mappingCone φ)
    (α : Cochain K F 0) (β : Cochain K G (-1))
    (h₁ : (Cochain.ofHom f₁).comp (fst φ).1 (zero_add 1) =
      -δ 0 1 α + (Cochain.ofHom f₂).comp (fst φ).1 (zero_add 1))
    (h₂ : (Cochain.ofHom f₁).comp (snd φ) (zero_add 0) =
      δ (-1) 0 β + α.comp (Cochain.ofHom φ) (zero_add 0) +
        (Cochain.ofHom f₂).comp (snd φ) (zero_add 0)) :
    Homotopy f₁ f₂ :=
  (Cochain.equivHomotopy f₁ f₂).symm ⟨liftCochain φ α β (neg_add_cancel 1), by
    simp [δ_liftCochain _ _ _ _ _ (zero_add 1), ext_cochain_to_iff _ _ _ (zero_add 1), h₁, h₂]⟩

section

variable {K L : CochainComplex C Int} {n m : Int}
  (α : Cochain K F m) (β : Cochain K G n) {n' m' : Int} (α' : Cochain F L m') (β' : Cochain G L n')
  (h : n + 1 = m) (h' : m' + 1 = n') (p : Int) (hp : n + n' = p)

@[simp]
/--
lemma `liftCochain_descCochain` / 引理 `liftCochain_descCochain`

English:
lemma liftCochain_descCochain
  proof: by
  simp [liftCochain, descCochain,
    Cochain.comp_assoc α (inl φ) _ _ (show -1 + n' = m' by lia) (by linarith)]

中文:
引理 liftCochain_descCochain
  证明: by
  simp [liftCochain, descCochain,
    Cochain.comp_assoc α (inl φ) _ _ (show -1 + n' = m' by lia) (by linarith)]

Depends on / 依赖: Cochain, Cochain.comp_assoc, comp_assoc, descCochain, liftCochain
-/
lemma liftCochain_descCochain :
    (liftCochain φ α β h).comp (descCochain φ α' β' h') hp =
      α.comp α' (by lia) + β.comp β' (by lia) := by
  simp [liftCochain, descCochain,
    Cochain.comp_assoc α (inl φ) _ _ (show -1 + n' = m' by lia) (by linarith)]

/--
lemma `liftCochain_v_descCochain_v` / 引理 `liftCochain_v_descCochain_v`

English:
lemma liftCochain_v_descCochain_v
  statement: (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
  proof: by
  have eq := Cochain.congr_v (liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by lia)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by lia)] using eq

中文:
引理 liftCochain_v_descCochain_v
  结论: (p₁ p₂ p₃ : 整数) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
  证明: by
  have eq := Cochain.congr_v (liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by lia)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by lia)] using eq

Depends on / 依赖: Cochain, Cochain.add_v, Cochain.comp_v, Cochain.congr_v, add_v, comp_v, congr_v, liftCochain_descCochain
-/
lemma liftCochain_v_descCochain_v (p₁ p₂ p₃ : Int) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
    (q : Int) (hq : p₁ + m = q) :
    (liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (descCochain φ α' β' h').v p₂ p₃ h₂₃ =
      α.v p₁ q hq ≫ α'.v q p₃ (by omega) + β.v p₁ p₂ h₁₂ ≫ β'.v p₂ p₃ h₂₃ := by
  have eq := Cochain.congr_v (liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by lia)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by lia)] using eq

end

/--
lemma `lift_desc_f` / 引理 `lift_desc_f`

English:
lemma lift_desc_f
  statement: {K L : CochainComplex C Int} (α : Cocycle K F 1) (β : Cochain K G 0)
  proof: by
  simp only [lift, desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_cancel 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]

中文:
引理 lift_desc_f
  结论: {K L : CochainComplex C 整数} (α : Cocycle K F 1) (β : Cochain K G 0)
  证明: by
  simp only [lift, desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_cancel 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]

Depends on / 依赖: Cochain, Cochain.ofHom, Cochain.ofHom_v, Cocycle, Cocycle.homOf_f, Cocycle.ofHom_coe, add_zero, descCocycle_coe, homOf_f, liftCochain_v_descCochain_v, liftCocycle_coe, neg_add_cancel, ofHom_coe, ofHom_v, zero_add
-/
lemma lift_desc_f {K L : CochainComplex C Int} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)
    (α' : Cochain F L (-1)) (β' : G ⟶ L)
    (eq' : δ (-1) 0 α' = Cochain.ofHom (φ ≫ β')) (n n' : Int) (hnn' : n + 1 = n') :
    (lift φ α β eq).f n ≫ (desc φ α' β' eq').f n =
    α.1.v n n' hnn' ≫ α'.v n' n (by omega) + β.v n n (add_zero n) ≫ β'.f n := by
  simp only [lift, desc, Cocycle.homOf_f, liftCocycle_coe, descCocycle_coe, Cocycle.ofHom_coe,
    liftCochain_v_descCochain_v φ α.1 β α' (Cochain.ofHom β') (zero_add 1) (neg_add_cancel 1) 0
    (add_zero 0) n n n (add_zero n) (add_zero n) n' hnn', Cochain.ofHom_v]


section

open Preadditive Category

variable (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `H : C ⥤ D` is an additive functor and `φ` is a morphism of cochain complexes
in `C`, this is the comparison isomorphism (in each degree `n`) between the image
by `H` of `mappingCone φ` and the mapping cone of the image by `H` of `φ`.
It is an auxiliary definition for `mapHomologicalComplexXIso` and
`mapHomologicalComplexIso`. This definition takes an extra
parameter `m : ℤ` such that `n + 1 = m` which may help getting better
definitional properties. See also the equational lemma `mapHomologicalComplexXIso_eq`. -/
@[simps]
/--
Definition of `mapHomologicalComplexXIso'` / `mapHomologicalComplexXIso'` 的定义

English:
definition mapHomologicalComplexXIso'
  signature: (n m : Int) (hnm : n + 1 = m)
  body: H.map ((fst φ).1.v n m (by lia)) ≫
      (inl ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).v m n (by lia) +
      H.map ((snd φ).v n n (add_zero n)) ≫
        (inr ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).f n
  inv := (fst ((H.mapHomologicalComplex (ComplexShape.up Int)).

中文:
定义 mapHomologicalComplexXIso'
  签名: (n m : 整数) (hnm : n + 1 = m)
  定义体: H.map ((fst φ).1.v n m (by lia)) ≫
      (inl ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).v m n (by lia) +
      H.map ((snd φ).v n n (add_zero n)) ≫
        (inr ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).f n
  inv := (fst ((H.mapHomologicalComplex (ComplexShape.up Int)).

Depends on / 依赖: H.map
-/
noncomputable def mapHomologicalComplexXIso' (n m : Int) (hnm : n + 1 = m) :
    ((H.mapHomologicalComplex (ComplexShape.up Int)).obj (mappingCone φ)).X n ≅
      (mappingCone ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).X n where
  hom := H.map ((fst φ).1.v n m (by lia)) ≫
      (inl ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).v m n (by lia) +
      H.map ((snd φ).v n n (add_zero n)) ≫
        (inr ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).f n
  inv := (fst ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).1.v n m (by lia) ≫
      H.map ((inl φ).v m n (by lia)) +
      (snd ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).v n n (add_zero n) ≫
        H.map ((inr φ).f n)
  hom_inv_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc,
      inl_v_fst_v_assoc, inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero,
      inl_v_snd_v_assoc, inr_f_snd_v_assoc, zero_add, ← Functor.map_comp, ← Functor.map_add]
    rw [← H.map_id]
    congr 1
    simp [ext_from_iff _ _ _ hnm]
  inv_hom_id := by
    simp only [Functor.mapHomologicalComplex_obj_X, comp_add, add_comp, assoc,
      ← H.map_comp_assoc, inl_v_fst_v, CategoryTheory.Functor.map_id, id_comp, inr_f_fst_v,
      inl_v_snd_v, inr_f_snd_v]
    simp [ext_from_iff _ _ _ hnm]

/--
Definition of `mapHomologicalComplexXIso` / `mapHomologicalComplexXIso` 的定义

English:
definition mapHomologicalComplexXIso
  signature: (n : Int)
  body: mapHomologicalComplexXIso' φ H n (n + 1) rfl

中文:
定义 mapHomologicalComplexXIso
  签名: (n : 整数)
  定义体: mapHomologicalComplexXIso' φ H n (n + 1) rfl

Depends on / 依赖: mapHomologicalComplexXIso
-/
noncomputable def mapHomologicalComplexXIso (n : Int) :
    ((H.mapHomologicalComplex (ComplexShape.up Int)).obj (mappingCone φ)).X n ≅
      (mappingCone ((H.mapHomologicalComplex (ComplexShape.up Int)).map φ)).X n :=
  mapHomologicalComplexXIso' φ H n (n + 1) rfl

/--
lemma `mapHomologicalComplexXIso_eq` / 引理 `mapHomologicalComplexXIso_eq`

English:
lemma mapHomologicalComplexXIso_eq
  given: (n m : Int) (hnm : n + 1 = m)
  proof: by
  subst hnm
  rfl

中文:
引理 mapHomologicalComplexXIso_eq
  条件: (n m : 整数) (hnm : n + 1 = m)
  证明: by
  subst hnm
  rfl
-/
lemma mapHomologicalComplexXIso_eq (n m : Int) (hnm : n + 1 = m) :
    mapHomologicalComplexXIso φ H n = mapHomologicalComplexXIso' φ H n m hnm := by
  subst hnm
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapHomologicalComplexIso` / `mapHomologicalComplexIso` 的定义

English:
definition mapHomologicalComplexIso
  signature: :
  body: HomologicalComplex.Hom.isoOfComponents (mapHomologicalComplexXIso φ H) (by
    rintro n _ rfl
    rw [ext_to_iff _ _ (n + 2) (by lia)]; rw [assoc]; rw [assoc]; rw [d_fst_v _ _ _ _ rfl]; rw [assoc]; rw [assoc]; rw [d_snd_v _ _ _ rfl]
    simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl,
    

中文:
定义 mapHomologicalComplexIso
  签名: :
  定义体: HomologicalComplex.Hom.isoOfComponents (mapHomologicalComplexXIso φ H) (by
    rintro n _ rfl
    rw [ext_to_iff _ _ (n + 2) (by lia)]; rw [assoc]; rw [assoc]; rw [d_fst_v _ _ _ _ rfl]; rw [assoc]; rw [assoc]; rw [d_snd_v _ _ _ rfl]
    simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl,
    

Depends on / 依赖: Functor, Functor.mapHomologicalComplex_obj_X, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, _hom, add_comp, comp_neg, d_fst_v, d_snd_v, ext_to_iff, isoOfComponents, mapHomologicalComplexXIso, mapHomologicalComplexXIso_eq, mapHomologicalComplex_obj_X
-/
noncomputable def mapHomologicalComplexIso :
    (H.mapHomologicalComplex _).obj (mappingCone φ) ≅
      mappingCone ((H.mapHomologicalComplex _).map φ) :=
  HomologicalComplex.Hom.isoOfComponents (mapHomologicalComplexXIso φ H) (by
    rintro n _ rfl
    rw [ext_to_iff _ _ (n + 2) (by lia)]; rw [assoc]; rw [assoc]; rw [d_fst_v _ _ _ _ rfl]; rw [assoc]; rw [assoc]; rw [d_snd_v _ _ _ rfl]
    simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl,
      mapHomologicalComplexXIso_eq φ H (n + 1) (n + 2) (by lia),
      mapHomologicalComplexXIso'_hom, mapHomologicalComplexXIso'_hom]
    constructor
    · dsimp
      simp only [Functor.mapHomologicalComplex_obj_X, comp_neg, add_comp, assoc, inl_v_fst_v_assoc,
        inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero, inl_v_fst_v, comp_id, inr_f_fst_v,
        ← H.map_comp, d_fst_v φ n (n + 1) (n + 2) rfl (by lia), Functor.map_neg]
    · dsimp
      simp only [comp_add, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
        Functor.mapHomologicalComplex_obj_X, zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc,
        inr_f_snd_v_assoc, zero_add, inl_v_snd_v, inr_f_snd_v, comp_id, ← H.map_comp,
        d_snd_v φ n (n + 1) rfl, Functor.map_add])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_inr` / 引理 `map_inr`

English:
lemma map_inr
  proof: by
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl, mappingCone.ext_to_iff _ _ _ rfl,
    Functor.mapHomologicalComplex_obj_X, mapHomologicalComplexXIso'_hom, comp_add,
    add_comp, assoc, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero,

中文:
引理 map_inr
  证明: by
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl, mappingCone.ext_to_iff _ _ _ rfl,
    Functor.mapHomologicalComplex_obj_X, mapHomologicalComplexXIso'_hom, comp_add,
    add_comp, assoc, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero,

Depends on / 依赖: Functor, Functor.mapHomologicalComplex_obj_X, H.map_comp, H.map_id, H.map_zero, _hom, add_comp, add_zero, and_self, comp_add, comp_id, comp_zero, ext_to_iff, inl_v_fst_v, inl_v_snd_v, inr_f_fst_v, inr_f_snd_v, mapHomologicalComplexIso, mapHomologicalComplexXIso, mapHomologicalComplexXIso_eq
-/
lemma map_inr :
    (H.mapHomologicalComplex (ComplexShape.up Int)).map (inr φ) ≫
      (mapHomologicalComplexIso φ H).hom =
    inr ((Functor.mapHomologicalComplex H (ComplexShape.up Int)).map φ) := by
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ H n (n + 1) rfl, mappingCone.ext_to_iff _ _ _ rfl,
    Functor.mapHomologicalComplex_obj_X, mapHomologicalComplexXIso'_hom, comp_add,
    add_comp, assoc, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero, inl_v_snd_v,
    inr_f_snd_v, zero_add, ← H.map_comp, H.map_zero, H.map_id, and_self]

end

end mappingCone

end CochainComplex
