/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Shift.Quotient
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The shift on cochain complexes and on the homotopy category

In this file, we show that for any preadditive category `C`, the categories
`CochainComplex C ℤ` and `HomotopyCategory C (ComplexShape.up ℤ)` are
equipped with a shift by `ℤ`.

We also show that if `F : C ⥤ D` is an additive functor, then the functors
`F.mapHomologicalComplex (ComplexShape.up ℤ)` and
`F.mapHomotopyCategory (ComplexShape.up ℤ)` commute with the shift by `ℤ`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor by `n : ℤ` on `CochainComplex C ℤ` which sends a cochain
complex `K` to the complex which is `K.X (i + n)` in degree `i`, and which
multiplies the differentials by `(-1)^n`. -/
@[simps]
/--
Definition of `shiftFunctor` / `shiftFunctor` 的定义

English:
definition shiftFunctor
  signature: (n : Int)
  body: { X := fun i => K.X (i + n)
      d := fun _ _ => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        rw [K.shape]; rw [smul_zero]
        intro hij'
        apply 

中文:
定义 shiftFunctor
  签名: (n : 整数)
  定义体: { X := fun i => K.X (i + n)
      d := fun _ _ => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        rw [K.shape]; rw [smul_zero]
        intro hij'
        apply 

Depends on / 依赖: Hom.comm, K.shape, Linear, Linear.comp_units_smul, Linear.units_smul_comp, comp_units_smul, d_comp_d, intros, map_comp, map_id, n.negOnePow, negOnePow, smul_zero, units_smul_comp
-/
def shiftFunctor (n : Int) : CochainComplex C Int ⥤ CochainComplex C Int where
  obj K :=
    { X := fun i => K.X (i + n)
      d := fun _ _ => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        rw [K.shape]; rw [smul_zero]
        intro hij'
        apply hij
        dsimp at hij' ⊢
        lia }
  map φ :=
    { f := fun _ => φ.f _
      comm' := by
        intros
        dsimp
        simp only [Linear.comp_units_smul, Hom.comm, Linear.units_smul_comp] }
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance (n : Int) : (shiftFunctor C n).Additive where

instance (n : Int) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R (shiftFunctor C n) where

variable {C}

/-- The canonical isomorphism `((shiftFunctor C n).obj K).X i ≅ K.X m` when `m = i + n`. -/
@[simp]
/--
Definition of `shiftFunctorObjXIso` / `shiftFunctorObjXIso` 的定义

English:
definition shiftFunctorObjXIso
  signature: (K : CochainComplex C Int) (n i m : Int) (hm : m = i + n)
  body: K.XIsoOfEq hm.symm

中文:
定义 shiftFunctorObjXIso
  签名: (K : CochainComplex C 整数) (n i m : 整数) (hm : m = i + n)
  定义体: K.XIsoOfEq hm.symm

Depends on / 依赖: K.XIsoOfEq, XIsoOfEq, hm.symm
-/
def shiftFunctorObjXIso (K : CochainComplex C Int) (n i m : Int) (hm : m = i + n) :
    ((shiftFunctor C n).obj K).X i ≅ K.X m := K.XIsoOfEq hm.symm

section

variable (C)

attribute [local simp] XIsoOfEq_hom_naturality

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The shift functor by `n` on `CochainComplex C ℤ` identifies to the identity
functor when `n = 0`. -/
@[simps!]
/--
Definition of `shiftFunctorZero'` / `shiftFunctorZero'` 的定义

English:
definition shiftFunctorZero'
  signature: (n : Int) (h : n = 0)
  body: NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by simp [h])) (fun _ => by ext; simp)

中文:
定义 shiftFunctorZero'
  签名: (n : 整数) (h : n = 0)
  定义体: NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by simp [h])) (fun _ => by ext; simp)

Depends on / 依赖: Hom.isoOfComponents, K.shiftFunctorObjXIso, NatIso, NatIso.ofComponents, isoOfComponents, ofComponents, shiftFunctorObjXIso
-/
def shiftFunctorZero' (n : Int) (h : n = 0) :
    shiftFunctor C n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by simp [h])) (fun _ => by ext; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The compatibility of the shift functors on `CochainComplex C ℤ` with respect
to the addition of integers. -/
@[simps!]
/--
Definition of `shiftFunctorAdd'` / `shiftFunctorAdd'` 的定义

English:
definition shiftFunctorAdd'
  signature: (n₁ n₂ n₁₂ : Int) (h : n₁ + n₂ = n₁₂)
  body: NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_ho

中文:
定义 shiftFunctorAdd'
  签名: (n₁ n₂ n₁₂ : 整数) (h : n₁ + n₂ = n₁₂)
  定义体: NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_ho

Depends on / 依赖: Hom.isoOfComponents, Int.negOnePow_add, K.shiftFunctorObjXIso, Linear, Linear.comp_units_smul, Linear.units_smul_comp, NatIso, NatIso.ofComponents, XIsoOfEq_hom_comp_d, add_comm, comp_units_smul, d_comp_XIsoOfEq_hom, intros, isoOfComponents, negOnePow_add, ofComponents, shiftFunctorObjXIso, smul_smul, units_smul_comp
-/
def shiftFunctorAdd' (n₁ n₂ n₁₂ : Int) (h : n₁ + n₂ = n₁₂) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by lia))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_hom_comp_d]))
    (by intros; ext; simp)

attribute [local simp] XIsoOfEq

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (CochainComplex C Int) Int
  body: hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

中文:
实例 :
  签名: HasShift (CochainComplex C 整数) 整数
  定义体: hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.commi, hasShiftMk
-/
instance : HasShift (CochainComplex C Int) Int := hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

instance (n : Int) :
    (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up Int)) n).Additive :=
inferInstanceAs (CochainComplex.shiftFunctor C n).Additive

instance (n : Int) {R : Type*} [Ring R] [Linear R C] :
    Functor.Linear R
      (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up Int)) n) where

end

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `shiftFunctor_obj_X'` / 引理 `shiftFunctor_obj_X'`

English:
lemma shiftFunctor_obj_X'
  given: (K : CochainComplex C Int) (n p : Int)
  proof: rfl

中文:
引理 shiftFunctor_obj_X'
  条件: (K : CochainComplex C 整数) (n p : 整数)
  证明: rfl
-/
lemma shiftFunctor_obj_X' (K : CochainComplex C Int) (n p : Int) :
    ((CategoryTheory.shiftFunctor (CochainComplex C Int) n).obj K).X p = K.X (p + n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `shiftFunctor_map_f'` / 引理 `shiftFunctor_map_f'`

English:
lemma shiftFunctor_map_f'
  given: {K L : CochainComplex C Int} (φ : K ⟶ L) (n p : Int)
  proof: rfl

中文:
引理 shiftFunctor_map_f'
  条件: {K L : CochainComplex C 整数} (φ : K ⟶ L) (n p : 整数)
  证明: rfl
-/
lemma shiftFunctor_map_f' {K L : CochainComplex C Int} (φ : K ⟶ L) (n p : Int) :
    ((CategoryTheory.shiftFunctor (CochainComplex C Int) n).map φ).f p = φ.f (p + n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `shiftFunctor_obj_d'` / 引理 `shiftFunctor_obj_d'`

English:
lemma shiftFunctor_obj_d'
  given: (K : CochainComplex C Int) (n i j : Int)
  proof: rfl

中文:
引理 shiftFunctor_obj_d'
  条件: (K : CochainComplex C 整数) (n i j : 整数)
  证明: rfl
-/
lemma shiftFunctor_obj_d' (K : CochainComplex C Int) (n i j : Int) :
    ((CategoryTheory.shiftFunctor (CochainComplex C Int) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shiftFunctorAdd_inv_app_f` / 引理 `shiftFunctorAdd_inv_app_f`

English:
lemma shiftFunctorAdd_inv_app_f
  given: (K : CochainComplex C Int) (a b n : Int)
  proof: rfl

中文:
引理 shiftFunctorAdd_inv_app_f
  条件: (K : CochainComplex C 整数) (a b n : 整数)
  证明: rfl
-/
lemma shiftFunctorAdd_inv_app_f (K : CochainComplex C Int) (a b n : Int) :
    ((shiftFunctorAdd (CochainComplex C Int) a b).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shiftFunctorAdd_hom_app_f` / 引理 `shiftFunctorAdd_hom_app_f`

English:
lemma shiftFunctorAdd_hom_app_f
  given: (K : CochainComplex C Int) (a b n : Int)
  proof: by
  tauto

中文:
引理 shiftFunctorAdd_hom_app_f
  条件: (K : CochainComplex C 整数) (a b n : 整数)
  证明: by
  tauto
-/
lemma shiftFunctorAdd_hom_app_f (K : CochainComplex C Int) (a b n : Int) :
    ((shiftFunctorAdd (CochainComplex C Int) a b).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := by
  tauto

/--
lemma `shiftFunctorAdd'_inv_app_f'` / 引理 `shiftFunctorAdd'_inv_app_f'`

English:
lemma shiftFunctorAdd'_inv_app_f'
  given: (K : CochainComplex C Int) (a b ab : Int) (h : a + b = ab) (n : Int)
  proof: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_inv_app_f]

中文:
引理 shiftFunctorAdd'_inv_app_f'
  条件: (K : CochainComplex C 整数) (a b ab : 整数) (h : a + b = ab) (n : 整数)
  证明: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_inv_app_f]
-/
lemma shiftFunctorAdd'_inv_app_f' (K : CochainComplex C Int) (a b ab : Int) (h : a + b = ab) (n : Int) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C Int) a b ab h).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_inv_app_f]

/--
lemma `shiftFunctorAdd'_hom_app_f'` / 引理 `shiftFunctorAdd'_hom_app_f'`

English:
lemma shiftFunctorAdd'_hom_app_f'
  given: (K : CochainComplex C Int) (a b ab : Int) (h : a + b = ab) (n : Int)
  proof: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_hom_app_f]

中文:
引理 shiftFunctorAdd'_hom_app_f'
  条件: (K : CochainComplex C 整数) (a b ab : 整数) (h : a + b = ab) (n : 整数)
  证明: by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_hom_app_f]
-/
lemma shiftFunctorAdd'_hom_app_f' (K : CochainComplex C Int) (a b ab : Int) (h : a + b = ab) (n : Int) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C Int) a b ab h).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd_hom_app_f]

/--
lemma `shiftFunctorZero_inv_app_f` / 引理 `shiftFunctorZero_inv_app_f`

English:
lemma shiftFunctorZero_inv_app_f
  given: (K : CochainComplex C Int) (n : Int)
  proof: rfl

中文:
引理 shiftFunctorZero_inv_app_f
  条件: (K : CochainComplex C 整数) (n : 整数)
  证明: rfl
-/
lemma shiftFunctorZero_inv_app_f (K : CochainComplex C Int) (n : Int) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C Int) Int).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := rfl

/--
lemma `shiftFunctorZero_hom_app_f` / 引理 `shiftFunctorZero_hom_app_f`

English:
lemma shiftFunctorZero_hom_app_f
  given: (K : CochainComplex C Int) (n : Int)
  proof: by
  tauto

中文:
引理 shiftFunctorZero_hom_app_f
  条件: (K : CochainComplex C 整数) (n : 整数)
  证明: by
  tauto
-/
lemma shiftFunctorZero_hom_app_f (K : CochainComplex C Int) (n : Int) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C Int) Int).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := by
  tauto

/--
lemma `XIsoOfEq_shift` / 引理 `XIsoOfEq_shift`

English:
lemma XIsoOfEq_shift
  given: (K : CochainComplex C Int) (n : Int) {p q : Int} (hpq : p = q)
  proof: rfl

中文:
引理 XIsoOfEq_shift
  条件: (K : CochainComplex C 整数) (n : 整数) {p q : 整数} (hpq : p = q)
  证明: rfl

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.id, leftHomologyMap
-/
lemma XIsoOfEq_shift (K : CochainComplex C Int) (n : Int) {p q : Int} (hpq : p = q) :
    (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq]) := rfl

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shiftFunctorAdd'_eq` / 引理 `shiftFunctorAdd'_eq`

English:
lemma shiftFunctorAdd'_eq
  given: (a b c : Int) (h : a + b = c)
  proof: by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

中文:
引理 shiftFunctorAdd'_eq
  条件: (a b c : 整数) (h : a + b = c)
  证明: by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.id, cyclesMap
-/
lemma shiftFunctorAdd'_eq (a b c : Int) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (CochainComplex C Int) a b c h =
      shiftFunctorAdd' C a b c h := by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

/--
lemma `shiftFunctorAdd_eq` / 引理 `shiftFunctorAdd_eq`

English:
lemma shiftFunctorAdd_eq
  given: (a b : Int)
  proof: by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd'_eq]

中文:
引理 shiftFunctorAdd_eq
  条件: (a b : 整数)
  证明: by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd'_eq]

Depends on / 依赖: CategoryTheory, CategoryTheory.shiftFunctorAdd, _eq_shiftFunctorAdd, shiftFunctorAdd
-/
lemma shiftFunctorAdd_eq (a b : Int) :
    CategoryTheory.shiftFunctorAdd (CochainComplex C Int) a b = shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftFunctorAdd'_eq]

/--
lemma `shiftFunctorZero_eq` / 引理 `shiftFunctorZero_eq`

English:
lemma shiftFunctorZero_eq
  proof: by
  ext
  rw [shiftFunctorZero_hom_app_f]; rw [shiftFunctorZero'_hom_app_f]

中文:
引理 shiftFunctorZero_eq
  证明: by
  ext
  rw [shiftFunctorZero_hom_app_f]; rw [shiftFunctorZero'_hom_app_f]

Depends on / 依赖: _hom_app_f, shiftFunctorZero, shiftFunctorZero_hom_app_f
-/
lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (CochainComplex C Int) Int = shiftFunctorZero' C 0 rfl := by
  ext
  rw [shiftFunctorZero_hom_app_f]; rw [shiftFunctorZero'_hom_app_f]

variable {C}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftFunctorComm_hom_app_f` / 引理 `shiftFunctorComm_hom_app_f`

English:
lemma shiftFunctorComm_hom_app_f
  given: (K : CochainComplex C Int) (a b p : Int)
  proof: by
  rw [shiftFunctorComm_eq _ _ _ _ rfl]
  dsimp
  rw [shiftFunctorAdd'_inv_app_f']; rw [shiftFunctorAdd'_hom_app_f']
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

中文:
引理 shiftFunctorComm_hom_app_f
  条件: (K : CochainComplex C 整数) (a b p : 整数)
  证明: by
  rw [shiftFunctorComm_eq _ _ _ _ rfl]
  dsimp
  rw [shiftFunctorAdd'_inv_app_f']; rw [shiftFunctorAdd'_hom_app_f']
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.zero, XIsoOfEq, _hom_app_f, _inv_app_f, eqToHom_trans, eqToIso, eqToIso.hom, leftHomologyMap, shiftFunctorAdd, shiftFunctorComm_eq
-/
lemma shiftFunctorComm_hom_app_f (K : CochainComplex C Int) (a b p : Int) :
    ((shiftFunctorComm (CochainComplex C Int) a b).hom.app K).f p =
      (K.XIsoOfEq (show p + b + a = p + a + b
        by rw [add_assoc, add_comm b, add_assoc])).hom := by
  rw [shiftFunctorComm_eq _ _ _ _ rfl]
  dsimp
  rw [shiftFunctorAdd'_inv_app_f']; rw [shiftFunctorAdd'_hom_app_f']
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

variable (C)

attribute [local simp] XIsoOfEq_hom_naturality

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Shifting cochain complexes by `n` and evaluating in a degree `i` identifies
to the evaluation in degree `i'` when `n + i = i'`. -/
@[simps!]
/--
Definition of `shiftEval` / `shiftEval` 的定义

English:
definition shiftEval
  signature: (n i i' : Int) (hi : n + i = i')
  body: NatIso.ofComponents (fun K => K.XIsoOfEq (by dsimp; rw [← hi, add_comm i]))
    (by simp)

中文:
定义 shiftEval
  签名: (n i i' : 整数) (hi : n + i = i')
  定义体: NatIso.ofComponents (fun K => K.XIsoOfEq (by dsimp; rw [← hi, add_comm i]))
    (by simp)

Depends on / 依赖: K.XIsoOfEq, LeftHomologyMapData, LeftHomologyMapData.zero, NatIso, NatIso.ofComponents, XIsoOfEq, add_comm, cyclesMap, ofComponents
-/
def shiftEval (n i i' : Int) (hi : n + i = i') :
    (CategoryTheory.shiftFunctor (CochainComplex C Int) n) ⋙
      HomologicalComplex.eval C (ComplexShape.up Int) i ≅
      HomologicalComplex.eval C (ComplexShape.up Int) i' :=
  NatIso.ofComponents (fun K => K.XIsoOfEq (by dsimp; rw [← hi, add_comm i]))
    (by simp)

end CochainComplex

namespace CategoryTheory

open Category

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

attribute [local simp] Functor.map_zsmul

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The commutation with the shift isomorphism for the functor on cochain complexes
induced by an additive functor between preadditive categories. -/
@[simps!]
/--
Definition of `mapCochainComplexShiftIso` / `mapCochainComplexShiftIso` 的定义

English:
definition mapCochainComplexShiftIso
  signature: (n : Int)
  body: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (fun _ => by ext; dsimp; rw [id_comp, comp_id])

中文:
定义 mapCochainComplexShiftIso
  签名: (n : 整数)
  定义体: NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (fun _ => by ext; dsimp; rw [id_comp, comp_id])

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, comp_id, id_comp, isoOfComponents, ofComponents
-/
def mapCochainComplexShiftIso (n : Int) :
    shiftFunctor _ n ⋙ F.mapHomologicalComplex (ComplexShape.up Int) ≅
      F.mapHomologicalComplex (ComplexShape.up Int) ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by simp)) (fun _ => by ext; dsimp; rw [id_comp, comp_id])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `commShiftMapCochainComplex` / 实例 `commShiftMapCochainComplex`

English:
instance commShiftMapCochainComplex
  signature: :
  body: F.mapCochainComplexShiftIso
  commShiftIso_zero := by
    ext
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp only [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
       HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map, eqToHom_trans, eqToHom_refl]
  com

中文:
实例 commShiftMapCochainComplex
  签名: :
  定义体: F.mapCochainComplexShiftIso
  commShiftIso_zero := by
    ext
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp only [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
       HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map, eqToHom_trans, eqToHom_refl]
  com

Depends on / 依赖: F.mapCochainComplexShiftIso, mapCochainComplexShiftIso
-/
instance commShiftMapCochainComplex :
    (F.mapHomologicalComplex (ComplexShape.up Int)).CommShift Int where
  commShiftIso := F.mapCochainComplexShiftIso
  commShiftIso_zero := by
    ext
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp only [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorZero_hom_app_f,
       HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_map, eqToHom_trans, eqToHom_refl]
  commShiftIso_add := fun a b => by
    ext
    rw [CommShift.isoAdd_hom_app]
    dsimp
    rw [id_comp]; rw [id_comp]
    simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
      CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
      eqToHom_map, eqToHom_trans, eqToHom_refl]

/--
lemma `mapHomologicalComplex_commShiftIso_eq` / 引理 `mapHomologicalComplex_commShiftIso_eq`

English:
lemma mapHomologicalComplex_commShiftIso_eq
  given: (n : Int)
  proof: rfl

@[simp]

中文:
引理 mapHomologicalComplex_commShiftIso_eq
  条件: (n : 整数)
  证明: rfl

@[simp]

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.comp_, leftHomologyMap, leftHomologyMapData
-/
lemma mapHomologicalComplex_commShiftIso_eq (n : Int) :
    (F.mapHomologicalComplex (ComplexShape.up Int)).commShiftIso n =
      F.mapCochainComplexShiftIso n := rfl

@[simp]
/--
lemma `mapHomologicalComplex_commShiftIso_hom_app_f` / 引理 `mapHomologicalComplex_commShiftIso_hom_app_f`

English:
lemma mapHomologicalComplex_commShiftIso_hom_app_f
  given: (K : CochainComplex C Int) (n i : Int)
  proof: rfl

@[simp]

中文:
引理 mapHomologicalComplex_commShiftIso_hom_app_f
  条件: (K : CochainComplex C 整数) (n i : 整数)
  证明: rfl

@[simp]

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.comp_, cyclesMap, leftHomologyMapData
-/
lemma mapHomologicalComplex_commShiftIso_hom_app_f (K : CochainComplex C Int) (n i : Int) :
    (((F.mapHomologicalComplex (ComplexShape.up Int)).commShiftIso n).hom.app K).f i = 𝟙 _ := rfl

@[simp]
/--
lemma `mapHomologicalComplex_commShiftIso_inv_app_f` / 引理 `mapHomologicalComplex_commShiftIso_inv_app_f`

English:
lemma mapHomologicalComplex_commShiftIso_inv_app_f
  given: (K : CochainComplex C Int) (n i : Int)
  proof: rfl

中文:
引理 mapHomologicalComplex_commShiftIso_inv_app_f
  条件: (K : CochainComplex C 整数) (n i : 整数)
  证明: rfl
-/
lemma mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C Int) (n i : Int) :
    (((F.mapHomologicalComplex (ComplexShape.up Int)).commShiftIso n).inv.app K).f i = 𝟙 _ := rfl

end Functor

end CategoryTheory

namespace Homotopy

variable {C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: {K L : CochainComplex C Int} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n : Int)
  body: n.negOnePow • h.hom _ _
  zero i j hij := by
    dsimp
    rw [h.zero]; rw [smul_zero]
    intro hij'
    dsimp at hij hij'
    lia
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up Int).Rel i (i + 1) by simp)]; rw [prevD_eq _ (show (ComplexShape.up Int).Rel (i - 1) i by simp)]
    dsi

中文:
定义 shift
  签名: {K L : CochainComplex C 整数} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n : 整数)
  定义体: n.negOnePow • h.hom _ _
  zero i j hij := by
    dsimp
    rw [h.zero]; rw [smul_zero]
    intro hij'
    dsimp at hij hij'
    lia
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up Int).Rel i (i + 1) by simp)]; rw [prevD_eq _ (show (ComplexShape.up Int).Rel (i - 1) i by simp)]
    dsi

Depends on / 依赖: h.hom, n.negOnePow, negOnePow
-/
def shift {K L : CochainComplex C Int} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n : Int) :
    Homotopy (φ₁⟦n⟧') (φ₂⟦n⟧') where
  hom _ _ := n.negOnePow • h.hom _ _
  zero i j hij := by
    dsimp
    rw [h.zero]; rw [smul_zero]
    intro hij'
    dsimp at hij hij'
    lia
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up Int).Rel i (i + 1) by simp)]; rw [prevD_eq _ (show (ComplexShape.up Int).Rel (i - 1) i by simp)]
    dsimp
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul,
      dNext_eq _ (show (ComplexShape.up Int).Rel (i + n) (i + 1 + n) by dsimp; lia),
      prevD_eq _ (show (ComplexShape.up Int).Rel (i - 1 + n) (i + n) by dsimp; lia)]
        using h.comm (i + n)

end Homotopy

namespace HomotopyCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (homotopic C (ComplexShape.up Int)).IsCompatibleWithShift Int
  body: ⟨fun n _ _ _ _ ⟨h⟩ => ⟨h.shift n⟩⟩

中文:
实例 :
  签名: (homotopic C (ComplexShape.up 整数)).IsCompatibleWithShift 整数
  定义体: ⟨fun n _ _ _ _ ⟨h⟩ => ⟨h.shift n⟩⟩

Depends on / 依赖: h.shift
-/
instance : (homotopic C (ComplexShape.up Int)).IsCompatibleWithShift Int :=
  ⟨fun n _ _ _ _ ⟨h⟩ => ⟨h.shift n⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasShift` / 实例 `hasShift`

English:
instance hasShift
  signature: :
  body: by
  dsimp only [HomotopyCategory]
  infer_instance

中文:
实例 hasShift
  签名: :
  定义体: by
  dsimp only [HomotopyCategory]
  infer_instance

Depends on / 依赖: HomotopyCategory, infer_instance
-/
noncomputable instance hasShift :
    HasShift (HomotopyCategory C (ComplexShape.up Int)) Int := by
  dsimp only [HomotopyCategory]
  infer_instance

variable {C} in
/--
lemma `shift_quotient_obj` / 引理 `shift_quotient_obj`

English:
lemma shift_quotient_obj
  given: (K : HomologicalComplex C (.up Int)) (n : Int)
  proof: Quotient.functor_obj_shift ..

中文:
引理 shift_quotient_obj
  条件: (K : HomologicalComplex C (.up 整数)) (n : 整数)
  证明: Quotient.functor_obj_shift ..

Depends on / 依赖: Quotient, Quotient.functor_obj_shift, functor_obj_shift
-/
lemma shift_quotient_obj (K : HomologicalComplex C (.up Int)) (n : Int) :
    ((HomotopyCategory.quotient _ _).obj K)⟦n⟧ =
    (HomotopyCategory.quotient _ _).obj (K⟦n⟧) :=
  Quotient.functor_obj_shift ..

/--
Instance `commShiftQuotient` / 实例 `commShiftQuotient`

English:
instance commShiftQuotient
  signature: :
  body: Quotient.functor_commShift (homotopic C (ComplexShape.up Int)) Int

中文:
实例 commShiftQuotient
  签名: :
  定义体: Quotient.functor_commShift (homotopic C (ComplexShape.up Int)) Int

Depends on / 依赖: ComplexShape, ComplexShape.up, Quotient, Quotient.functor_commShift, functor_commShift, homotopic
-/
noncomputable instance commShiftQuotient :
    (HomotopyCategory.quotient C (ComplexShape.up Int)).CommShift Int :=
  Quotient.functor_commShift (homotopic C (ComplexShape.up Int)) Int

instance (n : Int) : (shiftFunctor (HomotopyCategory C (ComplexShape.up Int)) n).Additive := by
  have : ((quotient C (ComplexShape.up Int) ⋙ shiftFunctor _ n)).Additive :=
    Functor.additive_of_iso ((quotient C (ComplexShape.up Int)).commShiftIso n)
  apply Functor.additive_of_full_essSurj_comp (quotient _ _)

set_option backward.isDefEq.respectTransparency false in
instance {R : Type*} [Ring R] [CategoryTheory.Linear R C] (n : Int) :
    (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up Int)) n).Linear R where
  map_smul := by
    rintro ⟨X⟩ ⟨Y⟩ f r
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up Int)).map_surjective f
    have h₁ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) f
    have h₂ := NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) (r • f)
    dsimp at h₁ h₂
    rw [← Functor.map_smul]; rw [← h₁]; rw [← h₂]
    simp

section

variable {C}
variable (F : C ⥤ D) [F.Additive]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F.mapHomotopyCategory (ComplexShape.up Int)).CommShift Int
  body: Quotient.liftCommShift _ _ _ _

中文:
实例 :
  签名: (F.mapHomotopyCategory (ComplexShape.up 整数)).CommShift 整数
  定义体: Quotient.liftCommShift _ _ _ _

Depends on / 依赖: Quotient, Quotient.liftCommShift, liftCommShift
-/
noncomputable instance : (F.mapHomotopyCategory (ComplexShape.up Int)).CommShift Int :=
  Quotient.liftCommShift _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift (F.mapHomotopyCategoryFactors (ComplexShape.up Int)).hom Int
  body: Quotient.liftCommShift_compatibility _ _ _ _

中文:
实例 :
  签名: 自然数Trans.CommShift (F.mapHomotopyCategoryFactors (ComplexShape.up 整数)).hom 整数
  定义体: Quotient.liftCommShift_compatibility _ _ _ _

Depends on / 依赖: Quotient, Quotient.liftCommShift_compatibility, liftCommShift_compatibility
-/
instance : NatTrans.CommShift (F.mapHomotopyCategoryFactors (ComplexShape.up Int)).hom Int :=
  Quotient.liftCommShift_compatibility _ _ _ _

end

end HomotopyCategory
