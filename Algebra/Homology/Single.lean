/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Homological complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

In `ChainComplex.toSingle₀Equiv` we characterize chain maps to an
`ℕ`-indexed complex concentrated in degree 0; they are equivalent to
`{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (j : ι)
  body: { X := fun i => if i = j then A else 0
      d := fun _ _ => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · #a

中文:
定义 single
  签名: (j : ι)
  定义体: { X := fun i => if i = j then A else 0
      d := fun _ _ => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · #a

Depends on / 依赖: adaptation_note, because, correct, eqToHom, github, github.com, if_neg, if_pos, leanprover, map_id, motive, nightly, numerals, previously, removable, should, simplify, split_ifs
-/
noncomputable def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj A :=
    { X := fun i => if i = j then A else 0
      d := fun _ _ => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · #adaptation_note /-- nightly-2024-03-07
      previously was `rw [if_neg h]; simp`, but that fails with "motive not type correct"
      This is because dsimp does not simplify numerals;
      this note should be removable once https://github.com/leanprover/lean4/pull/8433 lands. -/
      convert! (id_zero (C := V)).symm
      all_goals simp [if_neg h]
  map_comp f g := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · simp

variable {V}

@[simp]
/--
lemma `single_obj_X_self` / 引理 `single_obj_X_self`

English:
lemma single_obj_X_self
  given: (j : ι) (A : V)
  proof: if_pos rfl

中文:
引理 single_obj_X_self
  条件: (j : ι) (A : V)
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
lemma single_obj_X_self (j : ι) (A : V) :
    ((single V c j).obj A).X j = A := if_pos rfl

/--
lemma `isZero_single_obj_X` / 引理 `isZero_single_obj_X`

English:
lemma isZero_single_obj_X
  given: (j : ι) (A : V) (i : ι) (hi : i != j)
  proof: by
  dsimp [single]
  rw [if_neg hi]
  exact Limits.isZero_zero V

中文:
引理 isZero_single_obj_X
  条件: (j : ι) (A : V) (i : ι) (hi : i != j)
  证明: by
  dsimp [single]
  rw [if_neg hi]
  exact Limits.isZero_zero V

Depends on / 依赖: Limits, Limits.isZero_zero, if_neg, isZero_zero, single
-/
lemma isZero_single_obj_X (j : ι) (A : V) (i : ι) (hi : i != j) :
    IsZero (((single V c j).obj A).X i) := by
  dsimp [single]
  rw [if_neg hi]
  exact Limits.isZero_zero V

/--
Definition of `singleObjXIsoOfEq` / `singleObjXIsoOfEq` 的定义

English:
definition singleObjXIsoOfEq
  signature: (j : ι) (A : V) (i : ι) (hi : i = j)
  body: eqToIso (by subst hi; simp [single])

中文:
定义 singleObjXIsoOfEq
  签名: (j : ι) (A : V) (i : ι) (hi : i = j)
  定义体: eqToIso (by subst hi; simp [single])

Depends on / 依赖: eqToIso, single
-/
noncomputable def singleObjXIsoOfEq (j : ι) (A : V) (i : ι) (hi : i = j) :
    ((single V c j).obj A).X i ≅ A :=
  eqToIso (by subst hi; simp [single])

/--
Definition of `singleObjXSelf` / `singleObjXSelf` 的定义

English:
definition singleObjXSelf
  signature: (j : ι) (A : V)
  body: singleObjXIsoOfEq c j A j rfl

@[simp]

中文:
定义 singleObjXSelf
  签名: (j : ι) (A : V)
  定义体: singleObjXIsoOfEq c j A j rfl

@[simp]

Depends on / 依赖: singleObjXIsoOfEq
-/
noncomputable def singleObjXSelf (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
  singleObjXIsoOfEq c j A j rfl

@[simp]
/--
lemma `single_obj_d` / 引理 `single_obj_d`

English:
lemma single_obj_d
  given: (j : ι) (A : V) (k l : ι)
  proof: rfl

@[reassoc]

中文:
引理 single_obj_d
  条件: (j : ι) (A : V) (k l : ι)
  证明: rfl

@[reassoc]
-/
lemma single_obj_d (j : ι) (A : V) (k l : ι) :
    ((single V c j).obj A).d k l = 0 := rfl

@[reassoc]
/--
theorem `single_map_f_self` / 定理 `single_map_f_self`

English:
theorem single_map_f_self
  given: (j : ι) {A B : V} (f : A ⟶ B)
  proof: by
  dsimp [single]
  rw [dif_pos rfl]
  rfl

中文:
定理 single_map_f_self
  条件: (j : ι) {A B : V} (f : A ⟶ B)
  证明: by
  dsimp [single]
  rw [dif_pos rfl]
  rfl

Depends on / 依赖: dif_pos, single
-/
theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫
      f ≫ (singleObjXSelf c j B).inv := by
  dsimp [single]
  rw [dif_pos rfl]
  rfl

variable (V)

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `single V c j ⋙ eval V c j ≅ 𝟭 V`. -/
@[simps!]
/--
Definition of `singleCompEvalIsoSelf` / `singleCompEvalIsoSelf` 的定义

English:
definition singleCompEvalIsoSelf
  signature: (j : ι)
  body: NatIso.ofComponents (singleObjXSelf c j) (fun {A B} f => by simp [single_map_f_self])

中文:
定义 singleCompEvalIsoSelf
  签名: (j : ι)
  定义体: NatIso.ofComponents (singleObjXSelf c j) (fun {A B} f => by simp [single_map_f_self])

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, singleObjXSelf, single_map_f_self
-/
noncomputable def singleCompEvalIsoSelf (j : ι) : single V c j ⋙ eval V c j ≅ 𝟭 V :=
  NatIso.ofComponents (singleObjXSelf c j) (fun {A B} f => by simp [single_map_f_self])

/--
lemma `isZero_single_comp_eval` / 引理 `isZero_single_comp_eval`

English:
lemma isZero_single_comp_eval
  given: (j i : ι) (hi : i != j)
  statement: IsZero (single V c j ⋙ eval V c i)
  proof: Functor.isZero _ (fun _ => isZero_single_obj_X c _ _ _ hi)

中文:
引理 isZero_single_comp_eval
  条件: (j i : ι) (hi : i != j)
  结论: IsZero (single V c j ⋙ eval V c i)
  证明: Functor.isZero _ (fun _ => isZero_single_obj_X c _ _ _ hi)

Depends on / 依赖: Functor, Functor.isZero, isZero, isZero_single_obj_X
-/
lemma isZero_single_comp_eval (j i : ι) (hi : i != j) : IsZero (single V c j ⋙ eval V c i) :=
  Functor.isZero _ (fun _ => isZero_single_obj_X c _ _ _ hi)

variable {V c}

@[ext]
/--
lemma `from_single_hom_ext` / 引理 `from_single_hom_ext`

English:
lemma from_single_hom_ext
  statement: {K : HomologicalComplex V c} {j : ι} {A : V}
  proof: by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]

中文:
引理 from_single_hom_ext
  结论: {K : HomologicalComplex V c} {j : ι} {A : V}
  证明: by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]

Depends on / 依赖: eq_of_src, isZero_single_obj_X
-/
lemma from_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : (single V c j).obj A ⟶ K} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_src

@[ext]
/--
lemma `to_single_hom_ext` / 引理 `to_single_hom_ext`

English:
lemma to_single_hom_ext
  statement: {K : HomologicalComplex V c} {j : ι} {A : V}
  proof: by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_tgt

中文:
引理 to_single_hom_ext
  结论: {K : HomologicalComplex V c} {j : ι} {A : V}
  证明: by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_tgt

Depends on / 依赖: eq_of_tgt, isZero_single_obj_X
-/
lemma to_single_hom_ext {K : HomologicalComplex V c} {j : ι} {A : V}
    {f g : K ⟶ (single V c j).obj A} (hfg : f.f j = g.f j) : f = g := by
  ext i
  by_cases h : i = j
  · subst h
    exact hfg
  · apply (isZero_single_obj_X c j A i h).eq_of_tgt

instance (j : ι) : (single V c j).Faithful where
  map_injective {A B f g} w := by
    rw [← cancel_mono (singleObjXSelf c j B).inv]; rw [← cancel_epi (singleObjXSelf c j A).hom]; rw [← single_map_f_self]; rw [← single_map_f_self]; rw [w]

instance (j : ι) : (single V c j).Full where
  map_surjective {A B} f :=
    ⟨(singleObjXSelf c j A).inv ≫ f.f j ≫ (singleObjXSelf c j B).hom, by
      ext
      simp [single_map_f_self]⟩

/--
Definition of `mkHomToSingle` / `mkHomToSingle` 的定义

English:
definition mkHomToSingle
  signature: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
  body: if hi : i = j
      then (K.XIsoOfEq hi).hom ≫ φ ≫ (singleObjXIsoOfEq c j A i hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [comp_zero]
    split_ifs with hk
    · subst hk
      simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, reassoc_of% hφ i hik, zero_comp]
    · apply (isZero_single

中文:
定义 mkHomToSingle
  签名: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
  定义体: if hi : i = j
      then (K.XIsoOfEq hi).hom ≫ φ ≫ (singleObjXIsoOfEq c j A i hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [comp_zero]
    split_ifs with hk
    · subst hk
      simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, reassoc_of% hφ i hik, zero_comp]
    · apply (isZero_single

Depends on / 依赖: Iso.refl_hom, K.XIsoOfEq, XIsoOfEq, XIsoOfEq_rfl, comp_zero, eq_of_tgt, id_comp, isZero_single_obj_X, reassoc_of, refl_hom, singleObjXIsoOfEq, split_ifs, zero_comp
-/
noncomputable def mkHomToSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0) :
    K ⟶ (single V c j).obj A where
  f i :=
    if hi : i = j
      then (K.XIsoOfEq hi).hom ≫ φ ≫ (singleObjXIsoOfEq c j A i hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [comp_zero]
    split_ifs with hk
    · subst hk
      simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, reassoc_of% hφ i hik, zero_comp]
    · apply (isZero_single_obj_X c j A k hk).eq_of_tgt

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mkHomToSingle_f` / 引理 `mkHomToSingle_f`

English:
lemma mkHomToSingle_f
  statement: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
  proof: by
  dsimp [mkHomToSingle]
  rw [dif_pos rfl]; rw [id_comp]
  rfl

中文:
引理 mkHomToSingle_f
  结论: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
  证明: by
  dsimp [mkHomToSingle]
  rw [dif_pos rfl]; rw [id_comp]
  rfl

Depends on / 依赖: dif_pos, id_comp, mkHomToSingle
-/
lemma mkHomToSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : K.X j ⟶ A)
    (hφ : forall (i : ι), c.Rel i j -> K.d i j ≫ φ = 0) :
    (mkHomToSingle φ hφ).f j = φ ≫ (singleObjXSelf c j A).inv := by
  dsimp [mkHomToSingle]
  rw [dif_pos rfl]; rw [id_comp]
  rfl

/--
Definition of `mkHomFromSingle` / `mkHomFromSingle` 的定义

English:
definition mkHomFromSingle
  signature: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
  body: if hi : i = j
      then (singleObjXIsoOfEq c j A i hi).hom ≫ φ ≫ (K.XIsoOfEq hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [zero_comp]
    split_ifs with hi
    · subst hi
      simp only [XIsoOfEq_rfl, Iso.refl_inv, comp_id, assoc, hφ k hik, comp_zero]
    · apply (isZero_single_obj_

中文:
定义 mkHomFromSingle
  签名: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
  定义体: if hi : i = j
      then (singleObjXIsoOfEq c j A i hi).hom ≫ φ ≫ (K.XIsoOfEq hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [zero_comp]
    split_ifs with hi
    · subst hi
      simp only [XIsoOfEq_rfl, Iso.refl_inv, comp_id, assoc, hφ k hik, comp_zero]
    · apply (isZero_single_obj_

Depends on / 依赖: Iso.refl_inv, K.XIsoOfEq, XIsoOfEq, XIsoOfEq_rfl, comp_id, comp_zero, eq_of_src, isZero_single_obj_X, refl_inv, singleObjXIsoOfEq, split_ifs, zero_comp
-/
noncomputable def mkHomFromSingle {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0) :
    (single V c j).obj A ⟶ K where
  f i :=
    if hi : i = j
      then (singleObjXIsoOfEq c j A i hi).hom ≫ φ ≫ (K.XIsoOfEq hi).inv
      else 0
  comm' i k hik := by
    dsimp
    rw [zero_comp]
    split_ifs with hi
    · subst hi
      simp only [XIsoOfEq_rfl, Iso.refl_inv, comp_id, assoc, hφ k hik, comp_zero]
    · apply (isZero_single_obj_X c j A i hi).eq_of_src

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `mkHomFromSingle_f` / 引理 `mkHomFromSingle_f`

English:
lemma mkHomFromSingle_f
  statement: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
  proof: by
  dsimp [mkHomFromSingle]
  rw [dif_pos rfl]; rw [comp_id]
  rfl

中文:
引理 mkHomFromSingle_f
  结论: {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
  证明: by
  dsimp [mkHomFromSingle]
  rw [dif_pos rfl]; rw [comp_id]
  rfl

Depends on / 依赖: comp_id, dif_pos, mkHomFromSingle
-/
lemma mkHomFromSingle_f {K : HomologicalComplex V c} {j : ι} {A : V} (φ : A ⟶ K.X j)
    (hφ : forall (k : ι), c.Rel j k -> φ ≫ K.d j k = 0) :
    (mkHomFromSingle φ hφ).f j = (singleObjXSelf c j A).hom ≫ φ := by
  dsimp [mkHomFromSingle]
  rw [dif_pos rfl]; rw [comp_id]
  rfl

instance (j : ι) : (single V c j).PreservesZeroMorphisms where

end HomologicalComplex

namespace ChainComplex

/--
Definition of `single₀` / `single₀` 的定义

English:
abbreviation single₀
  signature: : V ⥤ ChainComplex V Nat
  body: HomologicalComplex.single V (ComplexShape.down Nat) 0

中文:
缩写 single₀
  签名: : V ⥤ ChainComplex V 自然数
  定义体: HomologicalComplex.single V (ComplexShape.down Nat) 0

Depends on / 依赖: ComplexShape, ComplexShape.down, HomologicalComplex, HomologicalComplex.single, single
-/
noncomputable abbrev single₀ : V ⥤ ChainComplex V Nat :=
  HomologicalComplex.single V (ComplexShape.down Nat) 0

variable {V}

@[simp]
/--
lemma `single₀_obj_zero` / 引理 `single₀_obj_zero`

English:
lemma single₀_obj_zero
  given: (A : V)
  proof: rfl

中文:
引理 single₀_obj_zero
  条件: (A : V)
  证明: rfl
-/
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `single₀_map_f_zero` / 引理 `single₀_map_f_zero`

English:
lemma single₀_map_f_zero
  given: {A B : V} (f : A ⟶ B)
  proof: by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]


@[simp]

中文:
引理 single₀_map_f_zero
  条件: {A B : V} (f : A ⟶ B)
  证明: by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]


@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.singleObjXSelf, HomologicalComplex.single_map_f_self, comp_id, id_comp, singleObjXIsoOfEq, singleObjXSelf, single_map_f_self
-/
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]


@[simp]
/--
lemma `single₀ObjXSelf` / 引理 `single₀ObjXSelf`

English:
lemma single₀ObjXSelf
  given: (X : V)
  proof: rfl

中文:
引理 single₀ObjXSelf
  条件: (X : V)
  证明: rfl
-/
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.down Nat) 0 X = Iso.refl _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from an `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
@[simps apply_coe]
/--
Definition of `toSingle₀Equiv` / `toSingle₀Equiv` 的定义

English:
definition toSingle₀Equiv
  signature: (C : ChainComplex V Nat) (X : V)
  body: ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv f := by simp

中文:
定义 toSingle₀Equiv
  签名: (C : ChainComplex V 自然数) (X : V)
  定义体: ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv f := by simp

Depends on / 依赖: HomologicalComplex, HomologicalComplex.single_obj_d, comp_zero, single_obj_d
-/
noncomputable def toSingle₀Equiv (C : ChainComplex V Nat) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } where
  toFun φ := ⟨φ.f 0, by rw [← φ.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]⟩
  invFun f := HomologicalComplex.mkHomToSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toSingle₀Equiv_symm_apply_f_zero` / 引理 `toSingle₀Equiv_symm_apply_f_zero`

English:
lemma toSingle₀Equiv_symm_apply_f_zero
  statement: {C : ChainComplex V Nat} {X : V}
  proof: by
  simp [toSingle₀Equiv]

中文:
引理 toSingle₀Equiv_symm_apply_f_zero
  结论: {C : ChainComplex V 自然数} {X : V}
  证明: by
  simp [toSingle₀Equiv]
-/
lemma toSingle₀Equiv_symm_apply_f_zero {C : ChainComplex V Nat} {X : V}
    (f : C.X 0 ⟶ X) (hf : C.d 1 0 ≫ f = 0) :
    ((toSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [toSingle₀Equiv]

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms from a single object chain complex with `X` concentrated in degree 0
to an `ℕ`-indexed chain complex `C` are the same as morphisms `f : X → C.X 0`.
-/
@[simps apply]
/--
Definition of `fromSingle₀Equiv` / `fromSingle₀Equiv` 的定义

English:
definition fromSingle₀Equiv
  signature: (C : ChainComplex V Nat) (X : V)
  body: f.f 0
  invFun f := HomologicalComplex.mkHomFromSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 fromSingle₀Equiv
  签名: (C : ChainComplex V 自然数) (X : V)
  定义体: f.f 0
  invFun f := HomologicalComplex.mkHomFromSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
noncomputable def fromSingle₀Equiv (C : ChainComplex V Nat) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ (X ⟶ C.X 0) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomFromSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `fromSingle₀Equiv_symm_apply_f_zero` / 引理 `fromSingle₀Equiv_symm_apply_f_zero`

English:
lemma fromSingle₀Equiv_symm_apply_f_zero
  proof: by
  simp [fromSingle₀Equiv]

@[simp]

中文:
引理 fromSingle₀Equiv_symm_apply_f_zero
  证明: by
  simp [fromSingle₀Equiv]

@[simp]
-/
lemma fromSingle₀Equiv_symm_apply_f_zero
    {C : ChainComplex V Nat} {X : V} (f : X ⟶ C.X 0) :
    dsimp% ((fromSingle₀Equiv C X).symm f).f 0 = f := by
  simp [fromSingle₀Equiv]

@[simp]
/--
lemma `fromSingle₀Equiv_symm_apply_f_succ` / 引理 `fromSingle₀Equiv_symm_apply_f_succ`

English:
lemma fromSingle₀Equiv_symm_apply_f_succ
  proof: rfl

中文:
引理 fromSingle₀Equiv_symm_apply_f_succ
  证明: rfl
-/
lemma fromSingle₀Equiv_symm_apply_f_succ
    {C : ChainComplex V Nat} {X : V} (f : X ⟶ C.X 0) (n : Nat) :
    ((fromSingle₀Equiv C X).symm f).f (n + 1) = 0 := rfl

end ChainComplex

namespace CochainComplex

/--
Definition of `single₀` / `single₀` 的定义

English:
abbreviation single₀
  signature: : V ⥤ CochainComplex V Nat
  body: HomologicalComplex.single V (ComplexShape.up Nat) 0

中文:
缩写 single₀
  签名: : V ⥤ CochainComplex V 自然数
  定义体: HomologicalComplex.single V (ComplexShape.up Nat) 0

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.single, single
-/
noncomputable abbrev single₀ : V ⥤ CochainComplex V Nat :=
  HomologicalComplex.single V (ComplexShape.up Nat) 0

variable {V}

@[simp]
/--
lemma `single₀_obj_zero` / 引理 `single₀_obj_zero`

English:
lemma single₀_obj_zero
  given: (A : V)
  proof: rfl

中文:
引理 single₀_obj_zero
  条件: (A : V)
  证明: rfl
-/
lemma single₀_obj_zero (A : V) :
    ((single₀ V).obj A).X 0 = A := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `single₀_map_f_zero` / 引理 `single₀_map_f_zero`

English:
lemma single₀_map_f_zero
  given: {A B : V} (f : A ⟶ B)
  proof: by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]

@[simp]

中文:
引理 single₀_map_f_zero
  条件: {A B : V} (f : A ⟶ B)
  证明: by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.singleObjXSelf, HomologicalComplex.single_map_f_self, comp_id, id_comp, singleObjXIsoOfEq, singleObjXSelf, single_map_f_self
-/
lemma single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id]; rw [id_comp]

@[simp]
/--
lemma `single₀ObjXSelf` / 引理 `single₀ObjXSelf`

English:
lemma single₀ObjXSelf
  given: (X : V)
  proof: rfl

中文:
引理 single₀ObjXSelf
  条件: (X : V)
  证明: rfl
-/
lemma single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up Nat) 0 X = Iso.refl _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`. -/
@[simps apply_coe]
/--
Definition of `fromSingle₀Equiv` / `fromSingle₀Equiv` 的定义

English:
definition fromSingle₀Equiv
  signature: (C : CochainComplex V Nat) (X : V)
  body: ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv := by cat_disch

中文:
定义 fromSingle₀Equiv
  签名: (C : CochainComplex V 自然数) (X : V)
  定义体: ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: HomologicalComplex, HomologicalComplex.single_obj_d, single_obj_d, zero_comp
-/
noncomputable def fromSingle₀Equiv (C : CochainComplex V Nat) (X : V) :
    ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } where
  toFun φ := ⟨φ.f 0, by rw [φ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]⟩
  invFun f := HomologicalComplex.mkHomFromSingle f.1 (fun i hi => by
    obtain rfl : i = 1 := by simpa using hi.symm
    exact f.2)
  left_inv φ := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `fromSingle₀Equiv_symm_apply_f_zero` / 引理 `fromSingle₀Equiv_symm_apply_f_zero`

English:
lemma fromSingle₀Equiv_symm_apply_f_zero
  statement: {C : CochainComplex V Nat} {X : V}
  proof: by
  simp [fromSingle₀Equiv]

中文:
引理 fromSingle₀Equiv_symm_apply_f_zero
  结论: {C : CochainComplex V 自然数} {X : V}
  证明: by
  simp [fromSingle₀Equiv]
-/
lemma fromSingle₀Equiv_symm_apply_f_zero {C : CochainComplex V Nat} {X : V}
    (f : X ⟶ C.X 0) (hf : f ≫ C.d 0 1 = 0) :
    ((fromSingle₀Equiv C X).symm ⟨f, hf⟩).f 0 = f := by
  simp [fromSingle₀Equiv]

set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms to a single object cochain complex with `X` concentrated in degree 0
to an `ℕ`-indexed cochain complex `C` are the same as morphisms `f : C.X 0 ⟶ X`.
-/
@[simps apply]
/--
Definition of `toSingle₀Equiv` / `toSingle₀Equiv` 的定义

English:
definition toSingle₀Equiv
  signature: (C : CochainComplex V Nat) (X : V)
  body: f.f 0
  invFun f := HomologicalComplex.mkHomToSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 toSingle₀Equiv
  签名: (C : CochainComplex V 自然数) (X : V)
  定义体: f.f 0
  invFun f := HomologicalComplex.mkHomToSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
noncomputable def toSingle₀Equiv (C : CochainComplex V Nat) (X : V) :
    (C ⟶ (single₀ V).obj X) ≃ (C.X 0 ⟶ X) where
  toFun f := f.f 0
  invFun f := HomologicalComplex.mkHomToSingle f (fun i hi => by simp at hi)
  left_inv := by cat_disch
  right_inv := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `toSingle₀Equiv_symm_apply_f_zero` / 引理 `toSingle₀Equiv_symm_apply_f_zero`

English:
lemma toSingle₀Equiv_symm_apply_f_zero
  proof: by
  simp [toSingle₀Equiv]

@[simp]

中文:
引理 toSingle₀Equiv_symm_apply_f_zero
  证明: by
  simp [toSingle₀Equiv]

@[simp]
-/
lemma toSingle₀Equiv_symm_apply_f_zero
    {C : CochainComplex V Nat} {X : V} (f : C.X 0 ⟶ X) :
    ((toSingle₀Equiv C X).symm f).f 0 = f := by
  simp [toSingle₀Equiv]

@[simp]
/--
lemma `toSingle₀Equiv_symm_apply_f_succ` / 引理 `toSingle₀Equiv_symm_apply_f_succ`

English:
lemma toSingle₀Equiv_symm_apply_f_succ
  proof: by
  rfl

中文:
引理 toSingle₀Equiv_symm_apply_f_succ
  证明: by
  rfl
-/
lemma toSingle₀Equiv_symm_apply_f_succ
    {C : CochainComplex V Nat} {X : V} (f : C.X 0 ⟶ X) (n : Nat) :
    ((toSingle₀Equiv C X).symm f).f (n + 1) = 0 := by
  rfl

end CochainComplex
