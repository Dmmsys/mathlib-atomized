/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HasNoLoop
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Yoneda

/-!
# A homological complex lying in two degrees

Given `c : ComplexShape ι`, distinct indices `i₀` and `i₁` such that `hi₀₁ : c.Rel i₀ i₁`,
we construct a homological complex `double f hi₀₁` for any morphism `f : X₀ ⟶ X₁`.
It consists of the objects `X₀` and `X₁` in degrees `i₀` and `i₁`, respectively,
with the differential `X₀ ⟶ X₁` given by `f`, and zero everywhere else.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject Opposite

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

section

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

open scoped Classical in
/--
Definition of `double` / `double` 的定义

English:
definition double
  signature: : HomologicalComplex C c where
  body: if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ != i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        rw [if_neg]; rw [if_pos hk.2.1]
        aesop)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    ·

中文:
定义 double
  签名: : HomologicalComplex C c where
  定义体: if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ != i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        rw [if_neg]; rw [if_pos hk.2.1]
        aesop)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    ·
-/
noncomputable def double : HomologicalComplex C c where
  X k := if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ != i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        rw [if_neg]; rw [if_pos hk.2.1]
        aesop)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = i₁
      · subst hj
        nth_rw 2 [dif_neg (by tauto)]
        rw [comp_zero]
      · rw [dif_neg (by tauto), zero_comp]
    · rw [dif_neg (by tauto), zero_comp]
  shape i j hij := dif_neg (by aesop)

/--
lemma `isZero_double_X` / 引理 `isZero_double_X`

English:
lemma isZero_double_X
  given: (k : ι) (h₀ : k != i₀) (h₁ : k != i₁)
  proof: by
  dsimp [double]
  rw [if_neg h₀]; rw [if_neg h₁]
  exact Limits.isZero_zero C

中文:
引理 isZero_double_X
  条件: (k : ι) (h₀ : k != i₀) (h₁ : k != i₁)
  证明: by
  dsimp [double]
  rw [if_neg h₀]; rw [if_neg h₁]
  exact Limits.isZero_zero C

Depends on / 依赖: Limits, Limits.isZero_zero, double, if_neg, isZero_zero
-/
lemma isZero_double_X (k : ι) (h₀ : k != i₀) (h₁ : k != i₁) :
    IsZero ((double f hi₀₁).X k) := by
  dsimp [double]
  rw [if_neg h₀]; rw [if_neg h₁]
  exact Limits.isZero_zero C

/--
Definition of `doubleXIso₀` / `doubleXIso₀` 的定义

English:
definition doubleXIso₀
  signature: : (double f hi₀₁).X i₀ ≅ X₀
  body: eqToIso (dif_pos rfl)

中文:
定义 doubleXIso₀
  签名: : (double f hi₀₁).X i₀ ≅ X₀
  定义体: eqToIso (dif_pos rfl)

Depends on / 依赖: dif_pos, eqToIso
-/
noncomputable def doubleXIso₀ : (double f hi₀₁).X i₀ ≅ X₀ :=
  eqToIso (dif_pos rfl)

/--
Definition of `doubleXIso₁` / `doubleXIso₁` 的定义

English:
definition doubleXIso₁
  signature: (h : i₀ != i₁)
  body: eqToIso (by
    dsimp [double]
    rw [if_neg h.symm]; rw [if_pos rfl])

中文:
定义 doubleXIso₁
  签名: (h : i₀ != i₁)
  定义体: eqToIso (by
    dsimp [double]
    rw [if_neg h.symm]; rw [if_pos rfl])

Depends on / 依赖: double, eqToIso, h.symm, if_neg, if_pos
-/
noncomputable def doubleXIso₁ (h : i₀ != i₁) : (double f hi₀₁).X i₁ ≅ X₁ :=
  eqToIso (by
    dsimp [double]
    rw [if_neg h.symm]; rw [if_pos rfl])

/--
lemma `double_d` / 引理 `double_d`

English:
lemma double_d
  given: (h : i₀ != i₁)
  proof: dif_pos ⟨rfl, rfl, h⟩

中文:
引理 double_d
  条件: (h : i₀ != i₁)
  证明: dif_pos ⟨rfl, rfl, h⟩

Depends on / 依赖: dif_pos
-/
lemma double_d (h : i₀ != i₁) :
    (double f hi₀₁).d i₀ i₁ =
      (doubleXIso₀ f hi₀₁).hom ≫ f ≫ (doubleXIso₁ f hi₀₁ h).inv :=
  dif_pos ⟨rfl, rfl, h⟩

/--
lemma `double_d_eq_zero₀` / 引理 `double_d_eq_zero₀`

English:
lemma double_d_eq_zero₀
  given: (a b : ι) (ha : a != i₀)
  proof: dif_neg (by tauto)

中文:
引理 double_d_eq_zero₀
  条件: (a b : ι) (ha : a != i₀)
  证明: dif_neg (by tauto)

Depends on / 依赖: dif_neg
-/
lemma double_d_eq_zero₀ (a b : ι) (ha : a != i₀) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by tauto)

/--
lemma `double_d_eq_zero₁` / 引理 `double_d_eq_zero₁`

English:
lemma double_d_eq_zero₁
  given: (a b : ι) (hb : b != i₁)
  proof: dif_neg (by tauto)

中文:
引理 double_d_eq_zero₁
  条件: (a b : ι) (hb : b != i₁)
  证明: dif_neg (by tauto)

Depends on / 依赖: dif_neg
-/
lemma double_d_eq_zero₁ (a b : ι) (hb : b != i₁) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by tauto)

variable {f hi₀₁} in
@[ext]
/--
lemma `from_double_hom_ext` / 引理 `from_double_hom_ext`

English:
lemma from_double_hom_ext
  statement: {K : HomologicalComplex C c} {φ φ' : double f hi₀₁ ⟶ K}
  proof: by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_src

中文:
引理 from_double_hom_ext
  结论: {K : HomologicalComplex C c} {φ φ' : double f hi₀₁ ⟶ K}
  证明: by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_src

Depends on / 依赖: eq_of_src, isZero_double_X, not_or
-/
lemma from_double_hom_ext {K : HomologicalComplex C c} {φ φ' : double f hi₀₁ ⟶ K}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_src

variable {f hi₀₁} in
@[ext]
/--
lemma `to_double_hom_ext` / 引理 `to_double_hom_ext`

English:
lemma to_double_hom_ext
  statement: {K : HomologicalComplex C c} {φ φ' : K ⟶ double f hi₀₁}
  proof: by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

中文:
引理 to_double_hom_ext
  结论: {K : HomologicalComplex C c} {φ φ' : K ⟶ double f hi₀₁}
  证明: by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

Depends on / 依赖: eq_of_tgt, isZero_double_X, not_or
-/
lemma to_double_hom_ext {K : HomologicalComplex C c} {φ φ' : K ⟶ double f hi₀₁}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

section

variable {f} (h : i₀ != i₁) {K : HomologicalComplex C c} (φ₀ : X₀ ⟶ K.X i₀) (φ₁ : X₁ ⟶ K.X i₁)
  (comm : φ₀ ≫ K.d i₀ i₁ = f ≫ φ₁)
  (hφ : forall (k : ι), c.Rel i₁ k -> φ₁ ≫ K.d i₁ k = 0)

open scoped Classical in
/--
Definition of `mkHomFromDouble` / `mkHomFromDouble` 的定义

English:
definition mkHomFromDouble
  signature: : double f hi₀₁ ⟶ K where
  body: if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ (doubleXIso₀ f hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
    

中文:
定义 mkHomFromDouble
  签名: : double f hi₀₁ ⟶ K where
  定义体: if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ (doubleXIso₀ f hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
    

Depends on / 依赖: c.next_eq, comp_, comp_id, dif_neg, dif_pos, double_d, eqToHom, h.symm, id_comp, if_pos, next_eq
-/
noncomputable def mkHomFromDouble : double f hi₀₁ ⟶ K where
  f k :=
    if hk₀ : k = i₀ then
      eqToHom (by rw [hk₀]) ≫ (doubleXIso₀ f hi₀₁).hom ≫ φ₀ ≫ eqToHom (by rw [hk₀])
    else if hk₁ : k = i₁ then
      eqToHom (by rw [hk₁]) ≫ (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ ≫ eqToHom (by rw [hk₁])
    else 0
  comm' k₀ k₁ hk := by
    by_cases h₀ : k₀ = i₀
    · subst h₀
      rw [dif_pos rfl]
      obtain rfl := c.next_eq hk hi₀₁
      simp [dif_neg h.symm, double_d f hi₀₁ h, comm]
    · rw [dif_neg h₀]
      by_cases h₁ : k₀ = i₁
      · subst h₁
        dsimp
        rw [if_pos rfl]; rw [comp_id]; rw [id_comp]; rw [assoc]; rw [hφ k₁ hk]; rw [comp_zero]; rw [double_d_eq_zero₀ _ _ _ _ h.symm]; rw [zero_comp]
      · apply (isZero_double_X f hi₀₁ k₀ h₀ h₁).eq_of_src

@[simp, reassoc]
/--
lemma `mkHomFromDouble_f₀` / 引理 `mkHomFromDouble_f₀`

English:
lemma mkHomFromDouble_f₀
  proof: by
  dsimp [mkHomFromDouble]
  rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

@[simp, reassoc]

中文:
引理 mkHomFromDouble_f₀
  证明: by
  dsimp [mkHomFromDouble]
  rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

@[simp, reassoc]

Depends on / 依赖: comp_id, id_comp, if_pos, mkHomFromDouble
-/
lemma mkHomFromDouble_f₀ :
    (mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₀ =
      (doubleXIso₀ f hi₀₁).hom ≫ φ₀ := by
  dsimp [mkHomFromDouble]
  rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

@[simp, reassoc]
/--
lemma `mkHomFromDouble_f₁` / 引理 `mkHomFromDouble_f₁`

English:
lemma mkHomFromDouble_f₁
  proof: by
  dsimp [mkHomFromDouble]
  rw [dif_neg h.symm]; rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

中文:
引理 mkHomFromDouble_f₁
  证明: by
  dsimp [mkHomFromDouble]
  rw [dif_neg h.symm]; rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

Depends on / 依赖: comp_id, dif_neg, h.symm, id_comp, if_pos, mkHomFromDouble
-/
lemma mkHomFromDouble_f₁ :
    (mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₁ =
      (doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ := by
  dsimp [mkHomFromDouble]
  rw [dif_neg h.symm]; rw [if_pos rfl]; rw [id_comp]; rw [comp_id]

end

set_option backward.isDefEq.respectTransparency false in
/-- Let `c : ComplexShape ι`, and `i₀` and `i₁` be distinct indices such
that `hi₀₁ : c.Rel i₀ i₁`, then for any `X : C`, the functor which sends
`K : HomologicalComplex C c` to `X ⟶ K.X i` is corepresentable by `double (𝟙 X) hi₀₁`. -/
@[simps -isSimp]
/--
Definition of `evalCompCoyonedaCorepresentableByDoubleId` / `evalCompCoyonedaCorepresentableByDoubleId` 的定义

English:
definition evalCompCoyonedaCorepresentableByDoubleId
  signature: (h : i₀ != i₁) (X : C)
  body: { toFun g := (doubleXIso₀ _ hi₀₁).inv ≫ g.f i₀
      invFun φ₀ := mkHomFromDouble _ h φ₀ (φ₀ ≫ K.d i₀ i₁) (by simp) (by simp)
      left_inv g := by
        ext
        · simp
        · simp [double_d _ _ h]
      right_inv _ := by simp }
  homEquiv_comp _ _ := by simp

中文:
定义 evalCompCoyonedaCorepresentableByDoubleId
  签名: (h : i₀ != i₁) (X : C)
  定义体: { toFun g := (doubleXIso₀ _ hi₀₁).inv ≫ g.f i₀
      invFun φ₀ := mkHomFromDouble _ h φ₀ (φ₀ ≫ K.d i₀ i₁) (by simp) (by simp)
      left_inv g := by
        ext
        · simp
        · simp [double_d _ _ h]
      right_inv _ := by simp }
  homEquiv_comp _ _ := by simp

Depends on / 依赖: double_d, homEquiv_comp, invFun, left_inv, mkHomFromDouble, right_inv
-/
noncomputable def evalCompCoyonedaCorepresentableByDoubleId (h : i₀ != i₁) (X : C) :
    (eval C c i₀ ⋙ coyoneda.obj (op X)).CorepresentableBy (double (𝟙 X) hi₀₁) where
  homEquiv {K} :=
    { toFun g := (doubleXIso₀ _ hi₀₁).inv ≫ g.f i₀
      invFun φ₀ := mkHomFromDouble _ h φ₀ (φ₀ ≫ K.d i₀ i₁) (by simp) (by simp)
      left_inv g := by
        ext
        · simp
        · simp [double_d _ _ h]
      right_inv _ := by simp }
  homEquiv_comp _ _ := by simp

end

variable {ι : Type*} (c : ComplexShape ι)

set_option backward.isDefEq.respectTransparency false in
/-- If `i` has no successor for the complex shape `c`,
then for any `X : C`, the functor which sends `K : HomologicalComplex C c`
to `X ⟶ K.X i` is corepresentable by `(single C c i).obj X`. -/
@[simps -isSimp]
/--
Definition of `evalCompCoyonedaCorepresentableBySingle` / `evalCompCoyonedaCorepresentableBySingle` 的定义

English:
definition evalCompCoyonedaCorepresentableBySingle
  signature: (i : ι) [DecidableEq ι]
  body: { toFun g := (singleObjXSelf c i X).inv ≫ g.f i
      invFun f := mkHomFromSingle f (fun j hj => (hi j hj).elim)
      left_inv g := by cat_disch
      right_inv f := by simp }
  homEquiv_comp := by simp

中文:
定义 evalCompCoyonedaCorepresentableBySingle
  签名: (i : ι) [DecidableEq ι]
  定义体: { toFun g := (singleObjXSelf c i X).inv ≫ g.f i
      invFun f := mkHomFromSingle f (fun j hj => (hi j hj).elim)
      left_inv g := by cat_disch
      right_inv f := by simp }
  homEquiv_comp := by simp

Depends on / 依赖: cat_disch, homEquiv_comp, invFun, left_inv, mkHomFromSingle, right_inv, singleObjXSelf
-/
noncomputable def evalCompCoyonedaCorepresentableBySingle (i : ι) [DecidableEq ι]
    (hi : forall (j : ι), ¬ c.Rel i j) (X : C) :
    (eval C c i ⋙ coyoneda.obj (op X)).CorepresentableBy ((single C c i).obj X) where
  homEquiv {K} :=
    { toFun g := (singleObjXSelf c i X).inv ≫ g.f i
      invFun f := mkHomFromSingle f (fun j hj => (hi j hj).elim)
      left_inv g := by cat_disch
      right_inv f := by simp }
  homEquiv_comp := by simp

variable [c.HasNoLoop]

open scoped Classical in
/--
Definition of `evalCompCoyonedaCorepresentative` / `evalCompCoyonedaCorepresentative` 的定义

English:
definition evalCompCoyonedaCorepresentative
  signature: (X : C) (j : ι)
  body: if hj : exists (k : ι), c.Rel j k then
    double (𝟙 X) hj.choose_spec
  else (single C c j).obj X

中文:
定义 evalCompCoyonedaCorepresentative
  签名: (X : C) (j : ι)
  定义体: if hj : exists (k : ι), c.Rel j k then
    double (𝟙 X) hj.choose_spec
  else (single C c j).obj X

Depends on / 依赖: c.Rel, choose_spec, double, hj.choose_spec, single
-/
noncomputable def evalCompCoyonedaCorepresentative (X : C) (j : ι) :
    HomologicalComplex C c :=
  if hj : exists (k : ι), c.Rel j k then
    double (𝟙 X) hj.choose_spec
  else (single C c j).obj X

/--
Definition of `evalCompCoyonedaCorepresentable` / `evalCompCoyonedaCorepresentable` 的定义

English:
definition evalCompCoyonedaCorepresentable
  signature: (X : C) (j : ι)
  body: by
  dsimp [evalCompCoyonedaCorepresentative]
  classical
  split_ifs with h
  · exact evalCompCoyonedaCorepresentableByDoubleId _
      (fun hj => c.not_rel_of_eq hj h.choose_spec) _
  · apply evalCompCoyonedaCorepresentableBySingle
    obtain _ | _ := c.exists_distinct_prev_or j <;> tauto

中文:
定义 evalCompCoyonedaCorepresentable
  签名: (X : C) (j : ι)
  定义体: by
  dsimp [evalCompCoyonedaCorepresentative]
  classical
  split_ifs with h
  · exact evalCompCoyonedaCorepresentableByDoubleId _
      (fun hj => c.not_rel_of_eq hj h.choose_spec) _
  · apply evalCompCoyonedaCorepresentableBySingle
    obtain _ | _ := c.exists_distinct_prev_or j <;> tauto

Depends on / 依赖: c.exists_distinct_prev_or, c.not_rel_of_eq, choose_spec, classical, evalCompCoyonedaCorepresentableByDoubleId, evalCompCoyonedaCorepresentableBySingle, evalCompCoyonedaCorepresentative, exists_distinct_prev_or, h.choose_spec, not_rel_of_eq, split_ifs
-/
noncomputable def evalCompCoyonedaCorepresentable (X : C) (j : ι) :
    (eval C c j ⋙ coyoneda.obj (op X)).CorepresentableBy
      (evalCompCoyonedaCorepresentative c X j) := by
  dsimp [evalCompCoyonedaCorepresentative]
  classical
  split_ifs with h
  · exact evalCompCoyonedaCorepresentableByDoubleId _
      (fun hj => c.not_rel_of_eq hj h.choose_spec) _
  · apply evalCompCoyonedaCorepresentableBySingle
    obtain _ | _ := c.exists_distinct_prev_or j <;> tauto

instance (X : C) (j : ι) : (eval C c j ⋙ coyoneda.obj (op X)).IsCorepresentable where
  has_corepresentation := ⟨_, ⟨evalCompCoyonedaCorepresentable c X j⟩⟩

end HomologicalComplex
