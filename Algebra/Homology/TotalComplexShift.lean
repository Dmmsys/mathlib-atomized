/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.Linarith

/-!
# Behaviour of the total complex with respect to shifts

There are two ways to shift objects in `HomologicalComplex₂ C (up ℤ) (up ℤ)`:
* by shifting the first indices (and changing signs of horizontal differentials),
  which corresponds to the shift by `ℤ` on `CochainComplex (CochainComplex C ℤ) ℤ`.
* by shifting the second indices (and changing signs of vertical differentials).

These two sorts of shift functors shall be abbreviated as
`HomologicalComplex₂.shiftFunctor₁ C x` and
`HomologicalComplex₂.shiftFunctor₂ C y`.

In this file, for any `K : HomologicalComplex₂ C (up ℤ) (up ℤ)`, we define an isomorphism
`K.totalShift₁Iso x : ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
for any `x : ℤ` (which does not involve signs) and an isomorphism
`K.totalShift₂Iso y : ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
for any `y : ℤ` (which is given by the multiplication by `(p * y).negOnePow` on the
summand in bidegree `(p, q)` of `K`).

Depending on the order of the "composition" of the two isomorphisms
`totalShift₁Iso` and `totalShift₂Iso`, we get
two ways to identify `((shiftFunctor₁ C x).obj ((shiftFunctor₂ C y).obj K)).total (up ℤ)`
and `(K.total (up ℤ))⟦x + y⟧`. The lemma `totalShift₁Iso_trans_totalShift₂Iso` shows that
these two compositions of isomorphisms differ by the sign `(x * y).negOnePow`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C]

/--
Definition of `shiftFunctor₁` / `shiftFunctor₁` 的定义

English:
abbreviation shiftFunctor₁
  signature: (x : Int)
  body: shiftFunctor _ x

中文:
缩写 shiftFunctor₁
  签名: (x : 整数)
  定义体: shiftFunctor _ x

Depends on / 依赖: shiftFunctor
-/
abbrev shiftFunctor₁ (x : Int) :
    HomologicalComplex₂ C (up Int) (up Int) ⥤ HomologicalComplex₂ C (up Int) (up Int) :=
  shiftFunctor _ x

/--
Definition of `shiftFunctor₂` / `shiftFunctor₂` 的定义

English:
abbreviation shiftFunctor₂
  signature: (y : Int)
  body: (shiftFunctor _ y).mapHomologicalComplex _

中文:
缩写 shiftFunctor₂
  签名: (y : 整数)
  定义体: (shiftFunctor _ y).mapHomologicalComplex _

Depends on / 依赖: mapHomologicalComplex, shiftFunctor
-/
abbrev shiftFunctor₂ (y : Int) :
    HomologicalComplex₂ C (up Int) (up Int) ⥤ HomologicalComplex₂ C (up Int) (up Int) :=
  (shiftFunctor _ y).mapHomologicalComplex _

variable {C}
variable (K L : HomologicalComplex₂ C (up Int) (up Int)) (f : K ⟶ L)

/--
Definition of `shiftFunctor₁XXIso` / `shiftFunctor₁XXIso` 的定义

English:
definition shiftFunctor₁XXIso
  signature: (a x a' : Int) (h : a' = a + x) (b : Int)
  body: eqToIso (by subst h; rfl)

中文:
定义 shiftFunctor₁XXIso
  签名: (a x a' : 整数) (h : a' = a + x) (b : 整数)
  定义体: eqToIso (by subst h; rfl)

Depends on / 依赖: eqToIso
-/
def shiftFunctor₁XXIso (a x a' : Int) (h : a' = a + x) (b : Int) :
    (((shiftFunctor₁ C x).obj K).X a).X b ≅ (K.X a').X b := eqToIso (by subst h; rfl)

/--
Definition of `shiftFunctor₂XXIso` / `shiftFunctor₂XXIso` 的定义

English:
definition shiftFunctor₂XXIso
  signature: (a b y b' : Int) (h : b' = b + y)
  body: eqToIso (by subst h; rfl)

@[simp]

中文:
定义 shiftFunctor₂XXIso
  签名: (a b y b' : 整数) (h : b' = b + y)
  定义体: eqToIso (by subst h; rfl)

@[simp]

Depends on / 依赖: eqToIso
-/
def shiftFunctor₂XXIso (a b y b' : Int) (h : b' = b + y) :
    (((shiftFunctor₂ C y).obj K).X a).X b ≅ (K.X a).X b' := eqToIso (by subst h; rfl)

@[simp]
/--
lemma `shiftFunctor₁XXIso_refl` / 引理 `shiftFunctor₁XXIso_refl`

English:
lemma shiftFunctor₁XXIso_refl
  given: (a b x : Int)
  proof: rfl

@[simp]

中文:
引理 shiftFunctor₁XXIso_refl
  条件: (a b x : 整数)
  证明: rfl

@[simp]
-/
lemma shiftFunctor₁XXIso_refl (a b x : Int) :
    K.shiftFunctor₁XXIso a x (a + x) rfl b = Iso.refl _ := rfl

@[simp]
/--
lemma `shiftFunctor₂XXIso_refl` / 引理 `shiftFunctor₂XXIso_refl`

English:
lemma shiftFunctor₂XXIso_refl
  given: (a b y : Int)
  proof: rfl

中文:
引理 shiftFunctor₂XXIso_refl
  条件: (a b y : 整数)
  证明: rfl
-/
lemma shiftFunctor₂XXIso_refl (a b y : Int) :
    K.shiftFunctor₂XXIso a b y (b + y) rfl = Iso.refl _ := rfl

variable (x y : Int) [K.HasTotal (up Int)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((shiftFunctor₁ C x).obj K).HasTotal (up Int)
  body: fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + x)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a + x, b⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a - x, b), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl
      right_inv := by
        intro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl }
    (fun _ => Iso.refl _)

中文:
实例 :
  签名: ((shiftFunctor₁ C x).obj K).HasTotal (up 整数)
  定义体: fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + x)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a + x, b⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a - x, b), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl
      right_inv := by
        intro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl }
    (fun _ => Iso.refl _)
-/
instance : ((shiftFunctor₁ C x).obj K).HasTotal (up Int) := fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + x)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a + x, b⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a - x, b), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl
      right_inv := by
        intro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          lia
        · rfl }
    (fun _ => Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((shiftFunctor₂ C y).obj K).HasTotal (up Int)
  body: fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + y)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a, b + y⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a, b - y), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv _ := by simp
      right_inv _ := by simp }
    (fun _ => Iso.refl _)

中文:
实例 :
  签名: ((shiftFunctor₂ C y).obj K).HasTotal (up 整数)
  定义体: fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + y)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a, b + y⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a, b - y), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv _ := by simp
      right_inv _ := by simp }
    (fun _ => Iso.refl _)
-/
instance : ((shiftFunctor₂ C y).obj K).HasTotal (up Int) := fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up Int) (up Int) (up Int)) (n + y)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a, b + y⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a, b - y), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        lia⟩
      left_inv _ := by simp
      right_inv _ := by simp }
    (fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).HasTotal (up Int)
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).HasTotal (up 整数)
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).HasTotal (up Int) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((shiftFunctor₁ C x ⋙ shiftFunctor₂ C y).obj K).HasTotal (up Int)
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: ((shiftFunctor₁ C x ⋙ shiftFunctor₂ C y).obj K).HasTotal (up 整数)
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : ((shiftFunctor₁ C x ⋙ shiftFunctor₂ C y).obj K).HasTotal (up Int) := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalShift₁XIso` / `totalShift₁XIso` 的定义

English:
definition totalShift₁XIso
  signature: (n n' : Int) (h : n + x = n')
  body: totalDesc _ (fun p q hpq => K.ιTotal (up Int) (p + x) q n' (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq _ _ _ (Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up Int) (p - x) q n
        (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).obj K).XXIsoOfEq_inv_ιTotal _ (by lia) rfl _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Category.assoc, ι_totalDesc, XXIsoOfEq_inv_ιTotal, comp_id]

中文:
定义 totalShift₁XIso
  签名: (n n' : 整数) (h : n + x = n')
  定义体: totalDesc _ (fun p q hpq => K.ιTotal (up Int) (p + x) q n' (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq _ _ _ (Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up Int) (p - x) q n
        (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).obj K).XXIsoOfEq_inv_ιTotal _ (by lia) rfl _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Category.assoc, ι_totalDesc, XXIsoOfEq_inv_ιTotal, comp_id]

Depends on / 依赖: totalDesc
-/
noncomputable def totalShift₁XIso (n n' : Int) (h : n + x = n') :
    (((shiftFunctor₁ C x).obj K).total (up Int)).X n ≅ (K.total (up Int)).X n' where
  hom := totalDesc _ (fun p q hpq => K.ιTotal (up Int) (p + x) q n' (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq _ _ _ (Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up Int) (p - x) q n
        (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).obj K).XXIsoOfEq_inv_ιTotal _ (by lia) rfl _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Category.assoc, ι_totalDesc, XXIsoOfEq_inv_ιTotal, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `D₁_totalShift₁XIso_hom` / 引理 `D₁_totalShift₁XIso_hom`

English:
lemma D₁_totalShift₁XIso_hom
  given: (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁')
  proof: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₁]; rw [((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ (show p + x + 1 = p + 1 + x by lia) _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [one_smul]; rw [Linear.units_smul_comp]
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

中文:
引理 D₁_totalShift₁XIso_hom
  条件: (n₀ n₁ n₀' n₁' : 整数) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁')
  证明: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₁]; rw [((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ (show p + x + 1 = p + 1 + x by lia) _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [one_smul]; rw [Linear.units_smul_comp]
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

Depends on / 依赖: Category, Category.assoc, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, comp_zero, hom_ext, one_smul, smul_zero, total.hom_ext, units_smul_comp, zero_comp
-/
lemma D₁_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₁ (up Int) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₁ (up Int) n₀' n₁') := by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₁]; rw [((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ (show p + x + 1 = p + 1 + x by lia) _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [one_smul]; rw [Linear.units_smul_comp]
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `D₂_totalShift₁XIso_hom` / 引理 `D₂_totalShift₁XIso_hom`

English:
lemma D₂_totalShift₁XIso_hom
  given: (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁')
  proof: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₂]; rw [((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [smul_smul]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p]; rw [Int.negOnePow_add]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    grind [up_Rel]

中文:
引理 D₂_totalShift₁XIso_hom
  条件: (n₀ n₁ n₀' n₁' : 整数) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁')
  证明: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₂]; rw [((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [smul_smul]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p]; rw [Int.negOnePow_add]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    grind [up_Rel]

Depends on / 依赖: Category, Category.assoc, Int.negOnePow_add, Int.units_mul_self, Linear, Linear.comp_units_smul, Linear.units_smul_comp, add_comm, comp_units_smul, hom_ext, mul_assoc, negOnePow_add, one_mul, smul_smul, total.hom_ext, units_mul_self, units_smul_comp
-/
lemma D₂_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₂ (up Int) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₂ (up Int) n₀' n₁') := by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [ι_D₂]; rw [((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [smul_smul]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p]; rw [Int.negOnePow_add]; rw [← mul_assoc]; rw [Int.units_mul_self]; rw [one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    grind [up_Rel]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalShift₁Iso` / `totalShift₁Iso` 的定义

English:
definition totalShift₁Iso
  signature: :
  body: HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

中文:
定义 totalShift₁Iso
  签名: :
  定义体: HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, K.totalShift, Linear, Linear.comp_units_smul, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, comp_add, comp_units_smul, isoOfComponents, smul_add, total_d
-/
noncomputable def totalShift₁Iso :
    ((shiftFunctor₁ C x).obj K).total (up Int) ≅ (K.total (up Int))⟦x⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_totalShift₁Iso_hom_f` / 引理 `ι_totalShift₁Iso_hom_f`

English:
lemma ι_totalShift₁Iso_hom_f
  statement: (a b n : Int) (h : a + b = n) (a' : Int) (ha' : a' = a + x)
  proof: by
  subst ha' hn'
  dsimp [totalShift₁Iso, totalShift₁XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

中文:
引理 ι_totalShift₁Iso_hom_f
  结论: (a b n : 整数) (h : a + b = n) (a' : 整数) (ha' : a' = a + x)
  证明: by
  subst ha' hn'
  dsimp [totalShift₁Iso, totalShift₁XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

Depends on / 依赖: comp_id, id_comp
-/
lemma ι_totalShift₁Iso_hom_f (a b n : Int) (h : a + b = n) (a' : Int) (ha' : a' = a + x)
    (n' : Int) (hn' : n' = n + x) :
    ((shiftFunctor₁ C x).obj K).ιTotal (up Int) a b n h ≫ (K.totalShift₁Iso x).hom.f n =
      (K.shiftFunctor₁XXIso a x a' ha' b).hom ≫ K.ιTotal (up Int) a' b n' (by dsimp; lia) ≫
        (CochainComplex.shiftFunctorObjXIso (K.total (up Int)) x n n' hn').inv := by
  subst ha' hn'
  dsimp [totalShift₁Iso, totalShift₁XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ι_totalShift₁Iso_inv_f` / 引理 `ι_totalShift₁Iso_inv_f`

English:
lemma ι_totalShift₁Iso_inv_f
  statement: (a b n : Int) (h : a + b = n) (a' n' : Int)
  proof: by
  subst hn'
  obtain rfl : a = a' - x := by lia
  dsimp [totalShift₁Iso, totalShift₁XIso, shiftFunctor₁XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

中文:
引理 ι_totalShift₁Iso_inv_f
  结论: (a b n : 整数) (h : a + b = n) (a' n' : 整数)
  证明: by
  subst hn'
  obtain rfl : a = a' - x := by lia
  dsimp [totalShift₁Iso, totalShift₁XIso, shiftFunctor₁XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

Depends on / 依赖: XXIsoOfEq, id_comp
-/
lemma ι_totalShift₁Iso_inv_f (a b n : Int) (h : a + b = n) (a' n' : Int)
    (ha' : a' + b = n') (hn' : n' = n + x) :
    K.ιTotal (up Int) a' b n' ha' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up Int)) x n n' hn').inv ≫
        (K.totalShift₁Iso x).inv.f n =
      (K.shiftFunctor₁XXIso a x a' (by lia) b).inv ≫
        ((shiftFunctor₁ C x).obj K).ιTotal (up Int) a b n h := by
  subst hn'
  obtain rfl : a = a' - x := by lia
  dsimp [totalShift₁Iso, totalShift₁XIso, shiftFunctor₁XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K L} in
@[reassoc]
/--
lemma `totalShift₁Iso_hom_naturality` / 引理 `totalShift₁Iso_hom_naturality`

English:
lemma totalShift₁Iso_hom_naturality
  given: [L.HasTotal (up Int)]
  proof: by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₁Iso_hom_f x i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₁Iso_hom_f_assoc x i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ιTotal_map]

中文:
引理 totalShift₁Iso_hom_naturality
  条件: [L.HasTotal (up 整数)]
  证明: by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₁Iso_hom_f x i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₁Iso_hom_f_assoc x i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ιTotal_map]

Depends on / 依赖: comp_id, id_comp
-/
lemma totalShift₁Iso_hom_naturality [L.HasTotal (up Int)] :
    total.map ((shiftFunctor₁ C x).map f) (up Int) ≫ (L.totalShift₁Iso x).hom =
      (K.totalShift₁Iso x).hom ≫ (total.map f (up Int))⟦x⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₁Iso_hom_f x i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₁Iso_hom_f_assoc x i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ιTotal_map]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalShift₂XIso` / `totalShift₂XIso` 的定义

English:
definition totalShift₂XIso
  signature: (n n' : Int) (h : n + y = n')
  body: totalDesc _ (fun p q hpq => (p * y).negOnePow • K.ιTotal (up Int) p (q + y) n'
    (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq => (p * y).negOnePow •
    (K.XXIsoOfEq _ _ _ rfl (Int.sub_add_cancel q y)).inv ≫
      ((shiftFunctor₂ C y).obj K).ιTotal (up Int) p (q - y) n (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, ι_totalDesc, smul_smul,
      Int.units_mul_self, one_smul, comp_id]
    exact ((shiftFunctor₂ C y).obj K).XXIsoOfEq_inv_ιTotal _ rfl (by lia) _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, Category.assoc, ι_totalDesc,
      Linear.comp_units_smul, XXIsoOfEq_inv_ιTotal, smul_smul, Int.units_mul_self, one_smul,
      comp_id]

中文:
定义 totalShift₂XIso
  签名: (n n' : 整数) (h : n + y = n')
  定义体: totalDesc _ (fun p q hpq => (p * y).negOnePow • K.ιTotal (up Int) p (q + y) n'
    (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq => (p * y).negOnePow •
    (K.XXIsoOfEq _ _ _ rfl (Int.sub_add_cancel q y)).inv ≫
      ((shiftFunctor₂ C y).obj K).ιTotal (up Int) p (q - y) n (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, ι_totalDesc, smul_smul,
      Int.units_mul_self, one_smul, comp_id]
    exact ((shiftFunctor₂ C y).obj K).XXIsoOfEq_inv_ιTotal _ rfl (by lia) _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, Category.assoc, ι_totalDesc,
      Linear.comp_units_smul, XXIsoOfEq_inv_ιTotal, smul_smul, Int.units_mul_self, one_smul,
      comp_id]

Depends on / 依赖: negOnePow, totalDesc
-/
noncomputable def totalShift₂XIso (n n' : Int) (h : n + y = n') :
    (((shiftFunctor₂ C y).obj K).total (up Int)).X n ≅ (K.total (up Int)).X n' where
  hom := totalDesc _ (fun p q hpq => (p * y).negOnePow • K.ιTotal (up Int) p (q + y) n'
    (by dsimp at hpq ⊢; lia))
  inv := totalDesc _ (fun p q hpq => (p * y).negOnePow •
    (K.XXIsoOfEq _ _ _ rfl (Int.sub_add_cancel q y)).inv ≫
      ((shiftFunctor₂ C y).obj K).ιTotal (up Int) p (q - y) n (by dsimp at hpq ⊢; lia))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, ι_totalDesc, smul_smul,
      Int.units_mul_self, one_smul, comp_id]
    exact ((shiftFunctor₂ C y).obj K).XXIsoOfEq_inv_ιTotal _ rfl (by lia) _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, Category.assoc, ι_totalDesc,
      Linear.comp_units_smul, XXIsoOfEq_inv_ιTotal, smul_smul, Int.units_mul_self, one_smul,
      comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `D₁_totalShift₂XIso_hom` / 引理 `D₁_totalShift₂XIso_hom`

English:
lemma D₁_totalShift₂XIso_hom
  given: (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁')
  proof: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [smul_smul]; rw [((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ rfl _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [Linear.comp_units_smul]; rw [← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

中文:
引理 D₁_totalShift₂XIso_hom
  条件: (n₀ n₁ n₀' n₁' : 整数) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁')
  证明: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [smul_smul]; rw [((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ rfl _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [Linear.comp_units_smul]; rw [← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

Depends on / 依赖: Category, Category.assoc, Int.negOnePow_add, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, hom_ext, negOnePow_add, one_smul, smul_smul, total.hom_ext, units_smul_comp
-/
lemma D₁_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₁ (up Int) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₁ (up Int) n₀' n₁') := by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₁_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [ι_D₁]; rw [smul_smul]; rw [((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; lia)]; rw [K.d₁_eq _ rfl _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul]; rw [one_smul]; rw [Category.assoc]; rw [ι_totalDesc]; rw [Linear.comp_units_smul]; rw [← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `D₂_totalShift₂XIso_hom` / 引理 `D₂_totalShift₂XIso_hom`

English:
lemma D₂_totalShift₂XIso_hom
  given: (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁')
  proof: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [smul_smul]; rw [ι_D₂]; rw [((shiftFunctor₂ C y).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ (show q + y + 1 = q + 1 + y by lia) _ (by dsimp; lia)]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [smul_smul]; rw [ι_totalDesc]
    dsimp
    rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]
    congr 2
    lia
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    simp_all only [up_Rel]
    grind

中文:
引理 D₂_totalShift₂XIso_hom
  条件: (n₀ n₁ n₀' n₁' : 整数) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁')
  证明: by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [smul_smul]; rw [ι_D₂]; rw [((shiftFunctor₂ C y).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ (show q + y + 1 = q + 1 + y by lia) _ (by dsimp; lia)]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [smul_smul]; rw [ι_totalDesc]
    dsimp
    rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]
    congr 2
    lia
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    simp_all only [up_Rel]
    grind

Depends on / 依赖: Category, Category.assoc, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, hom_ext, smul_smul, total.hom_ext, units_smul_comp
-/
lemma D₂_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : Int) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₂ (up Int) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₂ (up Int) n₀' n₁') := by
  by_cases h : (up Int).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₂_assoc]; rw [Linear.comp_units_smul]; rw [ι_totalDesc_assoc]; rw [Linear.units_smul_comp]; rw [smul_smul]; rw [ι_D₂]; rw [((shiftFunctor₂ C y).obj K).d₂_eq _ _ rfl _ (by dsimp; lia)]; rw [K.d₂_eq _ _ (show q + y + 1 = q + 1 + y by lia) _ (by dsimp; lia)]; rw [Linear.units_smul_comp]; rw [Category.assoc]; rw [smul_smul]; rw [ι_totalDesc]
    dsimp
    rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]; rw [smul_smul]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]; rw [← Int.negOnePow_add]
    congr 2
    lia
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    simp_all only [up_Rel]
    grind

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `totalShift₂Iso` / `totalShift₂Iso` 的定义

English:
definition totalShift₂Iso
  signature: :
  body: HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₂XIso y n (n + y) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₂XIso_hom y n n' _ _ rfl rfl,
        K.D₂_totalShift₂XIso_hom y n n' _ _ rfl rfl])

中文:
定义 totalShift₂Iso
  签名: :
  定义体: HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₂XIso y n (n + y) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₂XIso_hom y n n' _ _ rfl rfl,
        K.D₂_totalShift₂XIso_hom y n n' _ _ rfl rfl])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, K.totalShift, Linear, Linear.comp_units_smul, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, comp_add, comp_units_smul, isoOfComponents, smul_add, total_d
-/
noncomputable def totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).total (up Int) ≅ (K.total (up Int))⟦y⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₂XIso y n (n + y) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₂XIso_hom y n n' _ _ rfl rfl,
        K.D₂_totalShift₂XIso_hom y n n' _ _ rfl rfl])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_totalShift₂Iso_hom_f` / 引理 `ι_totalShift₂Iso_hom_f`

English:
lemma ι_totalShift₂Iso_hom_f
  statement: (a b n : Int) (h : a + b = n) (b' : Int) (hb' : b' = b + y)
  proof: by
  subst hb' hn'
  dsimp [totalShift₂Iso, totalShift₂XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

中文:
引理 ι_totalShift₂Iso_hom_f
  结论: (a b n : 整数) (h : a + b = n) (b' : 整数) (hb' : b' = b + y)
  证明: by
  subst hb' hn'
  dsimp [totalShift₂Iso, totalShift₂XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

Depends on / 依赖: comp_id, id_comp
-/
lemma ι_totalShift₂Iso_hom_f (a b n : Int) (h : a + b = n) (b' : Int) (hb' : b' = b + y)
    (n' : Int) (hn' : n' = n + y) :
    ((shiftFunctor₂ C y).obj K).ιTotal (up Int) a b n h ≫ (K.totalShift₂Iso y).hom.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' hb').hom ≫
        K.ιTotal (up Int) a b' n' (by dsimp; lia) ≫
          (CochainComplex.shiftFunctorObjXIso (K.total (up Int)) y n n' hn').inv := by
  subst hb' hn'
  dsimp [totalShift₂Iso, totalShift₂XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ι_totalShift₂Iso_inv_f` / 引理 `ι_totalShift₂Iso_inv_f`

English:
lemma ι_totalShift₂Iso_inv_f
  statement: (a b n : Int) (h : a + b = n) (b' n' : Int)
  proof: by
  subst hn'
  obtain rfl : b = b' - y := by lia
  dsimp [totalShift₂Iso, totalShift₂XIso, shiftFunctor₂XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

中文:
引理 ι_totalShift₂Iso_inv_f
  结论: (a b n : 整数) (h : a + b = n) (b' n' : 整数)
  证明: by
  subst hn'
  obtain rfl : b = b' - y := by lia
  dsimp [totalShift₂Iso, totalShift₂XIso, shiftFunctor₂XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

Depends on / 依赖: XXIsoOfEq, id_comp
-/
lemma ι_totalShift₂Iso_inv_f (a b n : Int) (h : a + b = n) (b' n' : Int)
    (hb' : a + b' = n') (hn' : n' = n + y) :
    K.ιTotal (up Int) a b' n' hb' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up Int)) y n n' hn').inv ≫
        (K.totalShift₂Iso y).inv.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' (by lia)).inv ≫
        ((shiftFunctor₂ C y).obj K).ιTotal (up Int) a b n h := by
  subst hn'
  obtain rfl : b = b' - y := by lia
  dsimp [totalShift₂Iso, totalShift₂XIso, shiftFunctor₂XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K L} in
@[reassoc]
/--
lemma `totalShift₂Iso_hom_naturality` / 引理 `totalShift₂Iso_hom_naturality`

English:
lemma totalShift₂Iso_hom_naturality
  given: [L.HasTotal (up Int)]
  proof: by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₂Iso_hom_f y i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₂Iso_hom_f_assoc y i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id]; rw [Linear.comp_units_smul]; rw [Linear.units_smul_comp]; rw [ιTotal_map]

中文:
引理 totalShift₂Iso_hom_naturality
  条件: [L.HasTotal (up 整数)]
  证明: by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₂Iso_hom_f y i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₂Iso_hom_f_assoc y i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id]; rw [Linear.comp_units_smul]; rw [Linear.units_smul_comp]; rw [ιTotal_map]

Depends on / 依赖: Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_id, comp_units_smul, id_comp, units_smul_comp
-/
lemma totalShift₂Iso_hom_naturality [L.HasTotal (up Int)] :
    total.map ((shiftFunctor₂ C y).map f) (up Int) ≫ (L.totalShift₂Iso y).hom =
      (K.totalShift₂Iso y).hom ≫ (total.map f (up Int))⟦y⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc]; rw [L.ι_totalShift₂Iso_hom_f y i₁ i₂ n h _ rfl _ rfl]; rw [K.ι_totalShift₂Iso_hom_f_assoc y i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [comp_id]; rw [Linear.comp_units_smul]; rw [Linear.units_smul_comp]; rw [ιTotal_map]

variable (C) in
/--
Definition of `shiftFunctor₁₂CommIso` / `shiftFunctor₁₂CommIso` 的定义

English:
definition shiftFunctor₁₂CommIso
  signature: (x y : Int)
  body: Iso.refl _

中文:
定义 shiftFunctor₁₂CommIso
  签名: (x y : 整数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def shiftFunctor₁₂CommIso (x y : Int) :
    shiftFunctor₂ C y ⋙ shiftFunctor₁ C x ≅ shiftFunctor₁ C x ⋙ shiftFunctor₂ C y :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `totalShift₁Iso_trans_totalShift₂Iso` / 引理 `totalShift₁Iso_trans_totalShift₂Iso`

English:
lemma totalShift₁Iso_trans_totalShift₂Iso
  proof: by
  ext n n₁ n₂ h
  dsimp at h ⊢
  rw [Linear.comp_units_smul]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ n₂ n h _ rfl _ rfl]; rw [ιTotal_map_assoc]; rw [ι_totalShift₂Iso_hom_f_assoc _ y n₁ n₂ n h _ rfl _ rfl]; rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]
  dsimp [shiftFunctor₁₂CommIso]
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ι_totalShift₂Iso_hom_f _ y (n₁ + x) n₂ (n + x) (by lia) _ rfl _ rfl]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [add_mul]; rw [add_comm (x * y)]
  dsimp
  rw [id_comp]; rw [comp_id]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ (n₂ + y) (n + y) (by lia) _ rfl (n + x + y) (by lia)]; rw [CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp
  rw [Iso.inv_hom_id]; rw [comp_id]; rw [id_comp]

中文:
引理 totalShift₁Iso_trans_totalShift₂Iso
  证明: by
  ext n n₁ n₂ h
  dsimp at h ⊢
  rw [Linear.comp_units_smul]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ n₂ n h _ rfl _ rfl]; rw [ιTotal_map_assoc]; rw [ι_totalShift₂Iso_hom_f_assoc _ y n₁ n₂ n h _ rfl _ rfl]; rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]
  dsimp [shiftFunctor₁₂CommIso]
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ι_totalShift₂Iso_hom_f _ y (n₁ + x) n₂ (n + x) (by lia) _ rfl _ rfl]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [add_mul]; rw [add_comm (x * y)]
  dsimp
  rw [id_comp]; rw [comp_id]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ (n₂ + y) (n + y) (by lia) _ rfl (n + x + y) (by lia)]; rw [CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp
  rw [Iso.inv_hom_id]; rw [comp_id]; rw [id_comp]

Depends on / 依赖: Int.negOnePow_add, Linear, Linear.comp_units_smul, Linear.units_smul_comp, add_c, add_mul, comp_id, comp_units_smul, id_comp, negOnePow_add, smul_smul, units_smul_comp
-/
lemma totalShift₁Iso_trans_totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).totalShift₁Iso x ≪≫
      (shiftFunctor (CochainComplex C Int) x).mapIso (K.totalShift₂Iso y) =
    (x * y).negOnePow • (total.mapIso ((shiftFunctor₁₂CommIso C x y).app K) (up Int)) ≪≫
      ((shiftFunctor₁ C x).obj K).totalShift₂Iso y ≪≫
      (shiftFunctor _ y).mapIso (K.totalShift₁Iso x) ≪≫
      (shiftFunctorComm (CochainComplex C Int) x y).app _ := by
  ext n n₁ n₂ h
  dsimp at h ⊢
  rw [Linear.comp_units_smul]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ n₂ n h _ rfl _ rfl]; rw [ιTotal_map_assoc]; rw [ι_totalShift₂Iso_hom_f_assoc _ y n₁ n₂ n h _ rfl _ rfl]; rw [Linear.units_smul_comp]; rw [Linear.comp_units_smul]
  dsimp [shiftFunctor₁₂CommIso]
  rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [id_comp]; rw [comp_id]; rw [ι_totalShift₂Iso_hom_f _ y (n₁ + x) n₂ (n + x) (by lia) _ rfl _ rfl]; rw [smul_smul]; rw [← Int.negOnePow_add]; rw [add_mul]; rw [add_comm (x * y)]
  dsimp
  rw [id_comp]; rw [comp_id]; rw [ι_totalShift₁Iso_hom_f_assoc _ x n₁ (n₂ + y) (n + y) (by lia) _ rfl (n + x + y) (by lia)]; rw [CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp
  rw [Iso.inv_hom_id]; rw [comp_id]; rw [id_comp]

/-- The compatibility isomorphisms of the total complex with the shifts
in both variables "commute" only up to a sign `(x * y).negOnePow`. -/
@[reassoc]
/--
lemma `totalShift₁Iso_hom_totalShift₂Iso_hom` / 引理 `totalShift₁Iso_hom_totalShift₂Iso_hom`

English:
lemma totalShift₁Iso_hom_totalShift₂Iso_hom
  proof: congr_arg Iso.hom (totalShift₁Iso_trans_totalShift₂Iso K x y)

中文:
引理 totalShift₁Iso_hom_totalShift₂Iso_hom
  证明: congr_arg Iso.hom (totalShift₁Iso_trans_totalShift₂Iso K x y)

Depends on / 依赖: Iso.hom, congr_arg
-/
lemma totalShift₁Iso_hom_totalShift₂Iso_hom :
    (((shiftFunctor₂ C y).obj K).totalShift₁Iso x).hom ≫ (K.totalShift₂Iso y).hom⟦x⟧' =
      (x * y).negOnePow • (total.map ((shiftFunctor₁₂CommIso C x y).hom.app K) (up Int) ≫
          (((shiftFunctor₁ C x).obj K).totalShift₂Iso y).hom ≫
          (K.totalShift₁Iso x).hom⟦y⟧' ≫
          (shiftFunctorComm (CochainComplex C Int) x y).hom.app _) :=
  congr_arg Iso.hom (totalShift₁Iso_trans_totalShift₂Iso K x y)

end HomologicalComplex₂
