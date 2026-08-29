/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from or to single complexes

We introduce constructors `Cochain.fromSingleMk` and `Cocycle.fromSingleMk`
for cochains and cocycles from a single complex. We also introduce similar
definitions for cochains and cocycles to a single complex.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C Int}

namespace Cochain

/-- Constructor for cochains from a single complex. -/
@[nolint unusedArguments]
/--
Definition of `fromSingleMk` / `fromSingleMk` 的定义

English:
definition fromSingleMk
  signature: {p q : Int} (f : X ⟶ K.X q) {n : Int} (_ : p + n = q)
  body: Cochain.single ((HomologicalComplex.singleObjXSelf (.up Int) p X).hom ≫ f) n

中文:
定义 fromSingleMk
  签名: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (_ : p + n = q)
  定义体: Cochain.single ((HomologicalComplex.singleObjXSelf (.up Int) p X).hom ≫ f) n

Depends on / 依赖: Cochain, Cochain.single, HomologicalComplex, HomologicalComplex.singleObjXSelf, single, singleObjXSelf
-/
noncomputable def fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up Int) p X).hom ≫ f) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
@[simp]
/--
lemma `fromSingleMk_zero` / 引理 `fromSingleMk_zero`

English:
lemma fromSingleMk_zero
  given: (p q n : Int) (h : p + n = q)
  proof: by
  simp [fromSingleMk]

中文:
引理 fromSingleMk_zero
  条件: (p q n : 整数) (h : p + n = q)
  证明: by
  simp [fromSingleMk]

Depends on / 依赖: fromSingleMk
-/
lemma fromSingleMk_zero (p q n : Int) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `fromSingleMk_v` / 引理 `fromSingleMk_v`

English:
lemma fromSingleMk_v
  given: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  simp [fromSingleMk]

中文:
引理 fromSingleMk_v
  条件: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  simp [fromSingleMk]

Depends on / 依赖: fromSingleMk
-/
lemma fromSingleMk_v {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up Int) p X).hom ≫ f := by
  simp [fromSingleMk]

/--
lemma `fromSingleMk_v_eq_zero` / 引理 `fromSingleMk_v_eq_zero`

English:
lemma fromSingleMk_v_eq_zero
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: single_v_eq_zero _ _ _ _ _ hp'

中文:
引理 fromSingleMk_v_eq_zero
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: single_v_eq_zero _ _ _ _ _ hp'

Depends on / 依赖: single_v_eq_zero
-/
lemma fromSingleMk_v_eq_zero {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (p' q' : Int) (hpq' : p' + n = q') (hp' : p' != p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_fromSingleMk` / 引理 `δ_fromSingleMk`

English:
lemma δ_fromSingleMk
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

中文:
引理 δ_fromSingleMk
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shape, fromSingleMk
-/
lemma δ_fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (n' q' : Int) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromSingleEquiv` / `fromSingleEquiv` 的定义

English:
definition fromSingleEquiv
  signature: {p q n : Int} (h : p + n = q)
  body: (HomologicalComplex.singleObjXSelf (.up Int) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

中文:
定义 fromSingleEquiv
  签名: {p q n : 整数} (h : p + n = q)
  定义体: (HomologicalComplex.singleObjXSelf (.up Int) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

Depends on / 依赖: HomologicalComplex, HomologicalComplex.singleObjXSelf, singleObjXSelf
-/
noncomputable def fromSingleEquiv {p q n : Int} (h : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n ≃+ (X ⟶ K.X q) where
  toFun α := (HomologicalComplex.singleObjXSelf (.up Int) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `fromSingleEquiv_fromSingleMk` / 引理 `fromSingleEquiv_fromSingleMk`

English:
lemma fromSingleEquiv_fromSingleMk
  given: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  simp [fromSingleEquiv]

@[simp]

中文:
引理 fromSingleEquiv_fromSingleMk
  条件: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  simp [fromSingleEquiv]

@[simp]

Depends on / 依赖: fromSingleEquiv
-/
lemma fromSingleEquiv_fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    fromSingleEquiv h (fromSingleMk f h) = f := by
  simp [fromSingleEquiv]

@[simp]
/--
lemma `fromSingleMk_add` / 引理 `fromSingleMk_add`

English:
lemma fromSingleMk_add
  given: {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: (fromSingleEquiv h).symm.map_add _ _

@[simp]

中文:
引理 fromSingleMk_add
  条件: {p q : 整数} (f g : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: (fromSingleEquiv h).symm.map_add _ _

@[simp]

Depends on / 依赖: fromSingleEquiv, map_add, symm.map_add
-/
lemma fromSingleMk_add {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_add _ _

@[simp]
/--
lemma `fromSingleMk_sub` / 引理 `fromSingleMk_sub`

English:
lemma fromSingleMk_sub
  given: {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: (fromSingleEquiv h).symm.map_sub _ _

@[simp]

中文:
引理 fromSingleMk_sub
  条件: {p q : 整数} (f g : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: (fromSingleEquiv h).symm.map_sub _ _

@[simp]

Depends on / 依赖: fromSingleEquiv, map_sub, symm.map_sub
-/
lemma fromSingleMk_sub {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_sub _ _

@[simp]
/--
lemma `fromSingleMk_neg` / 引理 `fromSingleMk_neg`

English:
lemma fromSingleMk_neg
  given: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: (fromSingleEquiv h).symm.map_neg _

中文:
引理 fromSingleMk_neg
  条件: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: (fromSingleEquiv h).symm.map_neg _

Depends on / 依赖: fromSingleEquiv, map_neg, symm.map_neg
-/
lemma fromSingleMk_neg {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    fromSingleMk (-f) h = -fromSingleMk f h :=
  (fromSingleEquiv h).symm.map_neg _

/--
lemma `fromSingleMk_surjective` / 引理 `fromSingleMk_surjective`

English:
lemma fromSingleMk_surjective
  statement: {p n : Int} (α : Cochain ((singleFunctor C p).obj X) K n)
  proof: (fromSingleEquiv h).symm.surjective α

中文:
引理 fromSingleMk_surjective
  结论: {p n : 整数} (α : Cochain ((singleFunctor C p).obj X) K n)
  证明: (fromSingleEquiv h).symm.surjective α

Depends on / 依赖: fromSingleEquiv, surjective, symm.surjective
-/
lemma fromSingleMk_surjective {p n : Int} (α : Cochain ((singleFunctor C p).obj X) K n)
    (q : Int) (h : p + n = q) :
    exists (f : X ⟶ K.X q), fromSingleMk f h = α :=
  (fromSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSingleMk_precomp` / 引理 `fromSingleMk_precomp`

English:
lemma fromSingleMk_precomp
  proof: by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

中文:
引理 fromSingleMk_precomp
  证明: by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.single_map_f_self, ShortComplex, ShortComplex.cyclesMap_i, comp_id, cyclesIsoSc, cyclesMap_i, fromSingleEquiv, injective, natIsoSc, shortComplexFunctor, singleFunctor, singleFunctors, single_map_f_self
-/
lemma fromSingleMk_precomp
    {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) :
    fromSingleMk (g ≫ f) h =
      (Cochain.ofHom ((singleFunctor C p).map g)).comp (fromSingleMk f h) (zero_add n) := by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSingleMk_postcomp` / 引理 `fromSingleMk_postcomp`

English:
lemma fromSingleMk_postcomp
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])

中文:
引理 fromSingleMk_postcomp
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])

Depends on / 依赖: cyclesIsoSc, fromSingleEquiv, iCycles, injective, singleFunctor, singleFunctors
-/
lemma fromSingleMk_postcomp {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    {L : CochainComplex C Int} (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h =
      (fromSingleMk f h).comp (.ofHom g) (add_zero n) :=
  (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])

/-- Constructor for cochains to a single complex. -/
@[nolint unusedArguments]
/--
Definition of `toSingleMk` / `toSingleMk` 的定义

English:
definition toSingleMk
  signature: {p q : Int} (f : K.X p ⟶ X) {n : Int} (_ : p + n = q)
  body: Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).inv) n

中文:
定义 toSingleMk
  签名: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (_ : p + n = q)
  定义体: Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).inv) n

Depends on / 依赖: Cochain, Cochain.single, HomologicalComplex, HomologicalComplex.singleObjXSelf, single, singleObjXSelf
-/
noncomputable def toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (_ : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n :=
  Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).inv) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
@[simp]
/--
lemma `toSingleMk_zero` / 引理 `toSingleMk_zero`

English:
lemma toSingleMk_zero
  given: (p q n : Int) (h : p + n = q)
  proof: by
  simp [toSingleMk]

中文:
引理 toSingleMk_zero
  条件: (p q n : 整数) (h : p + n = q)
  证明: by
  simp [toSingleMk]

Depends on / 依赖: toSingleMk
-/
lemma toSingleMk_zero (p q n : Int) (h : p + n = q) :
    toSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [toSingleMk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toSingleMk_v` / 引理 `toSingleMk_v`

English:
lemma toSingleMk_v
  given: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  simp [toSingleMk]

中文:
引理 toSingleMk_v
  条件: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  simp [toSingleMk]

Depends on / 依赖: toSingleMk
-/
lemma toSingleMk_v {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) :
    (toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).inv := by
  simp [toSingleMk]

/--
lemma `toSingleMk_v_eq_zero` / 引理 `toSingleMk_v_eq_zero`

English:
lemma toSingleMk_v_eq_zero
  statement: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: single_v_eq_zero _ _ _ _ _ hp'

中文:
引理 toSingleMk_v_eq_zero
  结论: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: single_v_eq_zero _ _ _ _ _ hp'

Depends on / 依赖: opcyclesIsoSc, pOpcycles, single_v_eq_zero
-/
lemma toSingleMk_v_eq_zero {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' q' : Int) (hpq' : p' + n = q') (hp' : p' != p) :
    (toSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_toSingleMk` / 引理 `δ_toSingleMk`

English:
lemma δ_toSingleMk
  statement: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

中文:
引理 δ_toSingleMk
  结论: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shape, K.sc, ShortComplex, ShortComplex.p_fromOpcycles, _inv_assoc, _obj_g, cancel_epi, pOpcycles, pOpcycles_opcyclesIsoSc, p_fromOpcycles, shortComplexFunctor, toSingleMk
-/
lemma δ_toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (n' p' : Int) (h' : p' + n' = q) :
    δ n n' (toSingleMk f h) = n'.negOnePow • toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toSingleEquiv` / `toSingleEquiv` 的定义

English:
definition toSingleEquiv
  signature: {p q n : Int} (h : p + n = q)
  body: α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

中文:
定义 toSingleEquiv
  签名: {p q n : 整数} (h : p + n = q)
  定义体: α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

Depends on / 依赖: HomologicalComplex, HomologicalComplex.singleObjXSelf, singleObjXSelf
-/
noncomputable def toSingleEquiv {p q n : Int} (h : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n ≃+ (K.X p ⟶ X) where
  toFun α := α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toSingleEquiv_toSingleMk` / 引理 `toSingleEquiv_toSingleMk`

English:
lemma toSingleEquiv_toSingleMk
  given: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  simp [toSingleEquiv]

@[simp]

中文:
引理 toSingleEquiv_toSingleMk
  条件: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  simp [toSingleEquiv]

@[simp]

Depends on / 依赖: toSingleEquiv
-/
lemma toSingleEquiv_toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) :
    toSingleEquiv h (toSingleMk f h) = f := by
  simp [toSingleEquiv]

@[simp]
/--
lemma `toSingleMk_add` / 引理 `toSingleMk_add`

English:
lemma toSingleMk_add
  given: {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: (toSingleEquiv h).symm.map_add _ _

@[simp]

中文:
引理 toSingleMk_add
  条件: {p q : 整数} (f g : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: (toSingleEquiv h).symm.map_add _ _

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.homologyMap_id, homologyMap_id, map_add, symm.map_add, toSingleEquiv
-/
lemma toSingleMk_add {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) :
    toSingleMk (f + g) h = toSingleMk f h + toSingleMk g h :=
  (toSingleEquiv h).symm.map_add _ _

@[simp]
/--
lemma `toSingleMk_sub` / 引理 `toSingleMk_sub`

English:
lemma toSingleMk_sub
  given: {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: (toSingleEquiv h).symm.map_sub _ _

@[simp]

中文:
引理 toSingleMk_sub
  条件: {p q : 整数} (f g : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: (toSingleEquiv h).symm.map_sub _ _

@[simp]

Depends on / 依赖: map_sub, symm.map_sub, toSingleEquiv
-/
lemma toSingleMk_sub {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) :
    toSingleMk (f - g) h = toSingleMk f h - toSingleMk g h :=
  (toSingleEquiv h).symm.map_sub _ _

@[simp]
/--
lemma `toSingleMk_neg` / 引理 `toSingleMk_neg`

English:
lemma toSingleMk_neg
  given: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: (toSingleEquiv h).symm.map_neg _

中文:
引理 toSingleMk_neg
  条件: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: (toSingleEquiv h).symm.map_neg _

Depends on / 依赖: ShortComplex, ShortComplex.homology, map_neg, symm.map_neg, toSingleEquiv
-/
lemma toSingleMk_neg {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) :
    toSingleMk (-f) h = -toSingleMk f h :=
  (toSingleEquiv h).symm.map_neg _

/--
lemma `toSingleMk_surjective` / 引理 `toSingleMk_surjective`

English:
lemma toSingleMk_surjective
  statement: {q n : Int} (α : Cochain K ((singleFunctor C q).obj X) n)
  proof: (toSingleEquiv h).symm.surjective α

中文:
引理 toSingleMk_surjective
  结论: {q n : 整数} (α : Cochain K ((singleFunctor C q).obj X) n)
  证明: (toSingleEquiv h).symm.surjective α

Depends on / 依赖: ShortComplex, ShortComplex.homology, surjective, symm.surjective, toSingleEquiv
-/
lemma toSingleMk_surjective {q n : Int} (α : Cochain K ((singleFunctor C q).obj X) n)
    (p : Int) (h : p + n = q) :
    exists (f : K.X p ⟶ X), toSingleMk f h = α :=
  (toSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSingleMk_postcomp` / 引理 `toSingleMk_postcomp`

English:
lemma toSingleMk_postcomp
  proof: by
  apply (toSingleEquiv h).injective
  simp [toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

中文:
引理 toSingleMk_postcomp
  证明: by
  apply (toSingleEquiv h).injective
  simp [toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.single_map_f_self, ShortComplex, ShortComplex.homology, injective, singleFunctor, singleFunctors, single_map_f_self, toSingleEquiv
-/
lemma toSingleMk_postcomp
    {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h =
      (toSingleMk f h).comp (.ofHom ((singleFunctor C q).map g)) (add_zero n) := by
  apply (toSingleEquiv h).injective
  simp [toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSingleMk_precomp` / 引理 `toSingleMk_precomp`

English:
lemma toSingleMk_precomp
  proof: (toSingleEquiv h).injective (by simp [toSingleEquiv, singleFunctor, singleFunctors])

中文:
引理 toSingleMk_precomp
  证明: (toSingleEquiv h).injective (by simp [toSingleEquiv, singleFunctor, singleFunctors])

Depends on / 依赖: injective, singleFunctor, singleFunctors, toSingleEquiv
-/
lemma toSingleMk_precomp
    {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    {L : CochainComplex C Int} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h =
      (Cochain.ofHom g).comp (toSingleMk f h) (zero_add n) :=
  (toSingleEquiv h).injective (by simp [toSingleEquiv, singleFunctor, singleFunctors])

end Cochain

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
@[simps!]
/--
Definition of `fromSingleMk` / `fromSingleMk` 的定义

English:
definition fromSingleMk
  signature: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  body: Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)]; rw [hf]
    simp)

中文:
定义 fromSingleMk
  签名: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  定义体: Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)]; rw [hf]
    simp)

Depends on / 依赖: Cochain, Cochain.fromSingleMk, Cocycle, Cocycle.mk, fromSingleMk
-/
noncomputable def fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)]; rw [hf]
    simp)

/--
lemma `fromSingleMk_precomp` / 引理 `fromSingleMk_precomp`

English:
lemma fromSingleMk_precomp
  statement: {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

中文:
引理 fromSingleMk_precomp
  结论: {X' : C} (g : X' ⟶ X) {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

Depends on / 依赖: Cochain, Cochain.fromSingleEquiv, Cochain.fromSingleMk_precomp, fromSingleEquiv, fromSingleMk_precomp, injective
-/
lemma fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (g ≫ f) h q' hq' (by simp [hf]) =
      (fromSingleMk f h q' hq' hf).precomp ((singleFunctor C p).map g) := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

/--
lemma `fromSingleMk_postcomp` / 引理 `fromSingleMk_postcomp`

English:
lemma fromSingleMk_postcomp
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

中文:
引理 fromSingleMk_postcomp
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

Depends on / 依赖: Cochain, Cochain.fromSingleEquiv, Cochain.fromSingleMk_postcomp, fromSingleEquiv, fromSingleMk_postcomp, injective
-/
lemma fromSingleMk_postcomp {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C Int}
    (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) =
      (fromSingleMk f h q' hq' hf).postcomp g := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fromSingleMk_surjective` / 引理 `fromSingleMk_surjective`

English:
lemma fromSingleMk_surjective
  statement: {p n : Int} (α : Cocycle ((singleFunctor C p).obj X) K n)
  proof: by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf]; rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

中文:
引理 fromSingleMk_surjective
  结论: {p n : 整数} (α : Cocycle ((singleFunctor C p).obj X) K n)
  证明: by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf]; rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

Depends on / 依赖: Cochain, Cochain.congr_v, Cochain.fromSingleMk_surjective, congr_v, fromSingleMk_surjective, replace
-/
lemma fromSingleMk_surjective {p n : Int} (α : Cocycle ((singleFunctor C p).obj X) K n)
    (q : Int) (h : p + n = q) (q' : Int) (hq' : q + 1 = q') :
    exists (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf]; rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

/--
lemma `fromSingleMk_add` / 引理 `fromSingleMk_add`

English:
lemma fromSingleMk_add
  statement: {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 fromSingleMk_add
  结论: {p q : 整数} (f g : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma fromSingleMk_add {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf + fromSingleMk g h q' hq' hg := by
  cat_disch

/--
lemma `fromSingleMk_sub` / 引理 `fromSingleMk_sub`

English:
lemma fromSingleMk_sub
  statement: {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 fromSingleMk_sub
  结论: {p q : 整数} (f g : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma fromSingleMk_sub {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f - g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf - fromSingleMk g h q' hq' hg := by
  cat_disch

/--
lemma `fromSingleMk_neg` / 引理 `fromSingleMk_neg`

English:
lemma fromSingleMk_neg
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 fromSingleMk_neg
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma fromSingleMk_neg {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (-f) h q' hq' (by simp [hf]) = - fromSingleMk f h q' hq' hf := by
  cat_disch

variable (X K) in
@[simp]
/--
lemma `fromSingleMk_zero` / 引理 `fromSingleMk_zero`

English:
lemma fromSingleMk_zero
  statement: {p q : Int} {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 fromSingleMk_zero
  结论: {p q : 整数} {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma fromSingleMk_zero {p q : Int} {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') :
    fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  cat_disch

/--
lemma `fromSingleMk_mem_coboundaries_iff` / 引理 `fromSingleMk_mem_coboundaries_iff`

English:
lemma fromSingleMk_mem_coboundaries_iff
  statement: {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
  proof: by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg]; rw [fromSingleMk_coe]; rw [Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

中文:
引理 fromSingleMk_mem_coboundaries_iff
  结论: {p q : 整数} (f : X ⟶ K.X q) {n : 整数} (h : p + n = q)
  证明: by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg]; rw [fromSingleMk_coe]; rw [Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

Depends on / 依赖: Cochain, Cochain.fromSingleEquiv, Cochain.fromSingleMk, Cochain.fromSingleMk_surjective, fromSingleEquiv, fromSingleMk, fromSingleMk_coe, fromSingleMk_surjective, injective, mem_coboundaries_iff, symm.injective
-/
lemma fromSingleMk_mem_coboundaries_iff {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
    (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : Int) (hq'' : q'' + 1 = q) :
    fromSingleMk f h q' hq' hf in coboundaries _ _ _ ↔
      exists (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg]; rw [fromSingleMk_coe]; rw [Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

/-- Constructor for cocycles to a single complex. -/
@[simps!]
/--
Definition of `toSingleMk` / `toSingleMk` 的定义

English:
definition toSingleMk
  signature: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  body: Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [hf]
    simp)

中文:
定义 toSingleMk
  签名: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  定义体: Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [hf]
    simp)

Depends on / 依赖: Cochain, Cochain.toSingleMk, Cocycle, Cocycle.mk, toSingleMk
-/
noncomputable def toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    Cocycle K ((singleFunctor C q).obj X) n :=
  Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [hf]
    simp)

/--
lemma `toSingleMk_postcomp` / 引理 `toSingleMk_postcomp`

English:
lemma toSingleMk_postcomp
  statement: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])

中文:
引理 toSingleMk_postcomp
  结论: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])

Depends on / 依赖: Cochain, Cochain.toSingleEquiv, Cochain.toSingleMk_postcomp, injective, toSingleEquiv, toSingleMk_postcomp
-/
lemma toSingleMk_postcomp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) =
      (toSingleMk f h p' hp' hf).postcomp ((singleFunctor C q).map g) := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])

/--
lemma `toSingleMk_precomp` / 引理 `toSingleMk_precomp`

English:
lemma toSingleMk_precomp
  proof: by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

中文:
引理 toSingleMk_precomp
  证明: by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

Depends on / 依赖: Cochain, Cochain.toSingleEquiv, Cochain.toSingleMk_precomp, injective, toSingleEquiv, toSingleMk_precomp
-/
lemma toSingleMk_precomp
    {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    {L : CochainComplex C Int} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h p' hp' (by simp [← g.comm_assoc, hf]) =
      (toSingleMk f h p' hp' hf).precomp g := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSingleMk_surjective` / 引理 `toSingleMk_surjective`

English:
lemma toSingleMk_surjective
  statement: {q n : Int} (α : Cocycle K ((singleFunctor C q).obj X) n)
  proof: by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul]; rw [δ_units_smul]; rw [← hf]; rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up Int) q X).inv] using!
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

中文:
引理 toSingleMk_surjective
  结论: {q n : 整数} (α : Cocycle K ((singleFunctor C q).obj X) n)
  证明: by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul]; rw [δ_units_smul]; rw [← hf]; rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up Int) q X).inv] using!
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

Depends on / 依赖: Cochain, Cochain.congr_v, Cochain.toSingleMk_surjective, HomologicalComplex, HomologicalComplex.singleObjXSelf, Int.units_mul_self, cancel_mono, coe_units_smul, congr_v, negOnePow, one_smul, singleObjXSelf, smul_smul, toSingleMk_surjective, units_mul_self
-/
lemma toSingleMk_surjective {q n : Int} (α : Cocycle K ((singleFunctor C q).obj X) n)
    (p : Int) (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) :
    exists (f : K.X p ⟶ X) (hf : K.d p' p ≫ f = 0), toSingleMk f h p' hp' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul]; rw [δ_units_smul]; rw [← hf]; rw [Cochain.δ_toSingleMk _ _ _ p' (by lia)]; rw [smul_smul]; rw [Int.units_mul_self]; rw [one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up Int) q X).inv] using!
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

/--
lemma `toSingleMk_add` / 引理 `toSingleMk_add`

English:
lemma toSingleMk_add
  statement: {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 toSingleMk_add
  结论: {p q : 整数} (f g : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma toSingleMk_add {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f + g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf + toSingleMk g h p' hp' hg := by
  cat_disch

/--
lemma `toSingleMk_sub` / 引理 `toSingleMk_sub`

English:
lemma toSingleMk_sub
  statement: {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 toSingleMk_sub
  结论: {p q : 整数} (f g : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma toSingleMk_sub {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f - g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf - toSingleMk g h p' hp' hg := by
  cat_disch

/--
lemma `toSingleMk_neg` / 引理 `toSingleMk_neg`

English:
lemma toSingleMk_neg
  statement: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 toSingleMk_neg
  结论: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma toSingleMk_neg {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    toSingleMk (-f) h p' hp' (by simp [hf]) =
      - toSingleMk f h p' hp' hf := by
  cat_disch

variable (X K) in
@[simp]
/--
lemma `toSingleMk_zero` / 引理 `toSingleMk_zero`

English:
lemma toSingleMk_zero
  statement: {p q : Int} {n : Int} (h : p + n = q)
  proof: by
  cat_disch

中文:
引理 toSingleMk_zero
  结论: {p q : 整数} {n : 整数} (h : p + n = q)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma toSingleMk_zero {p q : Int} {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) :
    toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0 := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSingleMk_mem_coboundaries_iff` / 引理 `toSingleMk_mem_coboundaries_iff`

English:
lemma toSingleMk_mem_coboundaries_iff
  statement: {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
  proof: by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg]; rw [toSingleMk_coe]; rw [Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

中文:
引理 toSingleMk_mem_coboundaries_iff
  结论: {p q : 整数} (f : K.X p ⟶ X) {n : 整数} (h : p + n = q)
  证明: by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg]; rw [toSingleMk_coe]; rw [Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

Depends on / 依赖: Cochain, Cochain.toSingleEquiv, Cochain.toSingleMk, Cochain.toSingleMk_surjective, injective, mem_coboundaries_iff, n.negOnePow, negOnePow, smul_smul, symm.injective, toSingleEquiv, toSingleMk, toSingleMk_coe, toSingleMk_surjective
-/
lemma toSingleMk_mem_coboundaries_iff {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
    (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (p'' : Int) (hp'' : p + 1 = p'') :
    toSingleMk f h p' hp' hf in coboundaries _ _ _ ↔
      exists (g : K.X p'' ⟶ X), K.d p p'' ≫ g = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg]; rw [toSingleMk_coe]; rw [Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

end Cocycle

end HomComplex

end CochainComplex
