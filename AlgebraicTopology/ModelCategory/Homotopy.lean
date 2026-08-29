/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

/-!
# Homotopies in model categories

In this file, we relate left and right homotopies between
morphisms `X ⟶ Y` in model categories. In particular, if `X` is cofibrant
and `Y` is fibrant, these notions coincide (for arbitrary choices of good
cylinders or good path objects).

Using the factorization lemma by K. S. Brown, we deduce versions of the Whitehead
theorem (`LeftHomotopyClass.whitehead` and `RightHomotopyClass.whitehead`)
which assert that when both `X` and `Y` are fibrant and cofibrant,
then any weak equivalence `X ⟶ Y` is a homotopy equivalence.

## References
* [Daniel G. Quillen, Homotopical algebra, section I.1][Quillen1967]

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y Z : C}

namespace LeftHomotopyRel

variable {f g : X ⟶ Y} [IsCofibrant X]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rightHomotopy` / `rightHomotopy` 的定义

English:
definition rightHomotopy
  signature: (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood]
  body: let P := h.exists_good_cylinder.choose
  have h := h.exists_good_cylinder.choose_spec.2.some
  have h' := h.exists_good_cylinder.choose_spec.1
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := { }
  { h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc]; rw [Q.p_fst]; rw [prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc]; rw [Q.p_snd]; rw [prod.lift_snd] at this
      simp [this] }

中文:
定义 rightHomotopy
  签名: (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.是Good]
  定义体: let P := h.exists_good_cylinder.choose
  have h := h.exists_good_cylinder.choose_spec.2.some
  have h' := h.exists_good_cylinder.choose_spec.1
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := { }
  { h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc]; rw [Q.p_fst]; rw [prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc]; rw [Q.p_snd]; rw [prod.lift_snd] at this
      simp [this] }

Depends on / 依赖: Category, Category.assoc, CommSq, Q.p_fst, Q.p_snd, choose_spec, exists_good_cylinder, fac_right, h.exists_good_cylinder.choose, h.exists_good_cylinder.choose_spec, lift_fst, lift_snd, p_fst, p_snd, prod.fst, prod.lift, prod.lift_fst, prod.lift_snd, prod.snd, sq.fac_right
-/
noncomputable def rightHomotopy (h : LeftHomotopyRel f g) (Q : PathObject Y) [Q.IsGood] :
    Q.RightHomotopy f g :=
  let P := h.exists_good_cylinder.choose
  have h := h.exists_good_cylinder.choose_spec.2.some
  have h' := h.exists_good_cylinder.choose_spec.1
  have sq : CommSq (f ≫ Q.ι) P.i₀ Q.p (prod.lift (P.π ≫ f) h.h) := { }
  { h := P.i₁ ≫ sq.lift
    h₀ := by
      have := sq.fac_right =≫ prod.fst
      rw [Category.assoc]; rw [Q.p_fst]; rw [prod.lift_fst] at this
      simp [this]
    h₁ := by
      have := sq.fac_right =≫ prod.snd
      rw [Category.assoc]; rw [Q.p_snd]; rw [prod.lift_snd] at this
      simp [this] }

/--
lemma `rightHomotopyRel` / 引理 `rightHomotopyRel`

English:
lemma rightHomotopyRel
  given: (h : LeftHomotopyRel f g)
  statement: RightHomotopyRel f g
  proof: by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨_, ⟨h.rightHomotopy P⟩⟩

中文:
引理 rightHomotopyRel
  条件: (h : LeftHomotopyRel f g)
  结论: RightHomotopyRel f g
  证明: by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨_, ⟨h.rightHomotopy P⟩⟩

Depends on / 依赖: PathObject, PathObject.exists_very_good, exists_very_good, h.rightHomotopy, rightHomotopy
-/
lemma rightHomotopyRel (h : LeftHomotopyRel f g) : RightHomotopyRel f g := by
  obtain ⟨P, _⟩ := PathObject.exists_very_good Y
  exact ⟨_, ⟨h.rightHomotopy P⟩⟩

end LeftHomotopyRel

namespace RightHomotopyRel

variable {f g : X ⟶ Y} [IsFibrant Y]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leftHomotopy` / `leftHomotopy` 的定义

English:
definition leftHomotopy
  signature: (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood]
  body: let P := h.exists_good_pathObject.choose
  have h := h.exists_good_pathObject.choose_spec.2.some
  have h' := h.exists_good_pathObject.choose_spec.1
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := { }
  { h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc]; rw [coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc]; rw [coprod.inr_desc] at this
      simp [reassoc_of% this, P] }

中文:
定义 leftHomotopy
  签名: (h : RightHomotopyRel f g) (Q : 柱 X) [Q.是Good]
  定义体: let P := h.exists_good_pathObject.choose
  have h := h.exists_good_pathObject.choose_spec.2.some
  have h' := h.exists_good_pathObject.choose_spec.1
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := { }
  { h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc]; rw [coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc]; rw [coprod.inr_desc] at this
      simp [reassoc_of% this, P] }

Depends on / 依赖: CommSq, Q.inl_i_assoc, Q.inr_i_assoc, choose_spec, coprod, coprod.desc, coprod.inl, coprod.inl_desc, coprod.inr, coprod.inr_desc, exists_good_pathObject, fac_left, h.exists_good_pathObject.choose, h.exists_good_pathObject.choose_spec, inl_desc, inl_i_assoc, inr_desc, inr_i_assoc, reassoc_of, sq.fac_left
-/
noncomputable def leftHomotopy (h : RightHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g :=
  let P := h.exists_good_pathObject.choose
  have h := h.exists_good_pathObject.choose_spec.2.some
  have h' := h.exists_good_pathObject.choose_spec.1
  have sq : CommSq (coprod.desc (f ≫ P.ι) h.h) Q.i P.p₀ (Q.π ≫ f) := { }
  { h := sq.lift ≫ P.p₁
    h₀ := by
      have := coprod.inl ≫= sq.fac_left
      rw [Q.inl_i_assoc]; rw [coprod.inl_desc] at this
      simp [reassoc_of% this]
    h₁ := by
      have := coprod.inr ≫= sq.fac_left
      rw [Q.inr_i_assoc]; rw [coprod.inr_desc] at this
      simp [reassoc_of% this, P] }

/--
lemma `leftHomotopyRel` / 引理 `leftHomotopyRel`

English:
lemma leftHomotopyRel
  given: (h : RightHomotopyRel f g)
  statement: LeftHomotopyRel f g
  proof: by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

中文:
引理 leftHomotopyRel
  条件: (h : RightHomotopyRel f g)
  结论: LeftHomotopyRel f g
  证明: by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

Depends on / 依赖: Cylinder, Cylinder.exists_very_good, exists_very_good, h.leftHomotopy, leftHomotopy
-/
lemma leftHomotopyRel (h : RightHomotopyRel f g) : LeftHomotopyRel f g := by
  obtain ⟨P, _⟩ := Cylinder.exists_very_good X
  exact ⟨P, ⟨h.leftHomotopy P⟩⟩

end RightHomotopyRel

section

variable {f g : X ⟶ Y} [IsCofibrant X] [IsFibrant Y]

/--
lemma `leftHomotopyRel_iff_rightHomotopyRel` / 引理 `leftHomotopyRel_iff_rightHomotopyRel`

English:
lemma leftHomotopyRel_iff_rightHomotopyRel
  proof: ⟨fun h => h.rightHomotopyRel, fun h => h.leftHomotopyRel⟩

中文:
引理 leftHomotopyRel_iff_rightHomotopyRel
  证明: ⟨fun h => h.rightHomotopyRel, fun h => h.leftHomotopyRel⟩

Depends on / 依赖: h.leftHomotopyRel, h.rightHomotopyRel, leftHomotopyRel, rightHomotopyRel
-/
lemma leftHomotopyRel_iff_rightHomotopyRel :
    LeftHomotopyRel f g ↔ RightHomotopyRel f g :=
  ⟨fun h => h.rightHomotopyRel, fun h => h.leftHomotopyRel⟩

/--
Definition of `LeftHomotopyRel.leftHomotopy` / `LeftHomotopyRel.leftHomotopy` 的定义

English:
definition LeftHomotopyRel.leftHomotopy
  body: RightHomotopyRel.leftHomotopy (by rwa [← leftHomotopyRel_iff_rightHomotopyRel]) _

中文:
定义 LeftHomotopyRel.leftHomotopy
  定义体: RightHomotopyRel.leftHomotopy (by rwa [← leftHomotopyRel_iff_rightHomotopyRel]) _

Depends on / 依赖: RightHomotopyRel, RightHomotopyRel.leftHomotopy, leftHomotopy, leftHomotopyRel_iff_rightHomotopyRel
-/
noncomputable def LeftHomotopyRel.leftHomotopy
    (h : LeftHomotopyRel f g) (Q : Cylinder X) [Q.IsGood] :
    Q.LeftHomotopy f g :=
  RightHomotopyRel.leftHomotopy (by rwa [← leftHomotopyRel_iff_rightHomotopyRel]) _

/--
Definition of `RightHomotopyRel.rightHomotopy` / `RightHomotopyRel.rightHomotopy` 的定义

English:
definition RightHomotopyRel.rightHomotopy
  body: LeftHomotopyRel.rightHomotopy (by rwa [leftHomotopyRel_iff_rightHomotopyRel]) _

中文:
定义 RightHomotopyRel.rightHomotopy
  定义体: LeftHomotopyRel.rightHomotopy (by rwa [leftHomotopyRel_iff_rightHomotopyRel]) _

Depends on / 依赖: LeftHomotopyRel, LeftHomotopyRel.rightHomotopy, leftHomotopyRel_iff_rightHomotopyRel, rightHomotopy
-/
noncomputable def RightHomotopyRel.rightHomotopy
    (h : RightHomotopyRel f g) (P : PathObject Y) [P.IsGood] :
    P.RightHomotopy f g :=
  LeftHomotopyRel.rightHomotopy (by rwa [leftHomotopyRel_iff_rightHomotopyRel]) _

end

namespace LeftHomotopyClass

variable (X)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `postcomp_bijective_of_fibration_of_weakEquivalence` / 引理 `postcomp_bijective_of_fibration_of_weakEquivalence`

English:
lemma postcomp_bijective_of_fibration_of_weakEquivalence
  proof: by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := coprod.inl ≫= sq.fac_left
          rwa [P.inl_i_assoc, coprod.inl_desc] at this
        h₁ := by
          have := coprod.inr ≫= sq.fac_left
          rwa [P.inr_i_assoc, coprod.inr_desc] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := { }
    exact ⟨mk sq.lift, by simp⟩

中文:
引理 postcomp_bijective_of_fibration_of_weakEquivalence
  证明: by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := coprod.inl ≫= sq.fac_left
          rwa [P.inl_i_assoc, coprod.inl_desc] at this
        h₁ := by
          have := coprod.inr ≫= sq.fac_left
          rwa [P.inr_i_assoc, coprod.inr_desc] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := { }
    exact ⟨mk sq.lift, by simp⟩

Depends on / 依赖: CommSq, P.inl_i_assoc, P.inr_i_assoc, coprod, coprod.desc, coprod.inl, coprod.inl_desc, coprod.inr, coprod.inr_desc, exists_good_cylinder, fac_left, h.exists_good_cylinder, inl_desc, inl_i_assoc, inr_desc, inr_i_assoc, mk_eq_mk_iff, mk_surjective, postcomp_mk, sq.fac_left
-/
lemma postcomp_bijective_of_fibration_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [Fibration g] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) => f.postcomp g) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [postcomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_cylinder
    have sq : CommSq (coprod.desc f₀ f₁) P.i g h.h := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := coprod.inl ≫= sq.fac_left
          rwa [P.inl_i_assoc, coprod.inl_desc] at this
        h₁ := by
          have := coprod.inr ≫= sq.fac_left
          rwa [P.inr_i_assoc, coprod.inr_desc] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq (initial.to Y) (initial.to X) g φ := { }
    exact ⟨mk sq.lift, by simp⟩

/--
lemma `postcomp_bijective_of_weakEquivalence` / 引理 `postcomp_bijective_of_weakEquivalence`

English:
lemma postcomp_bijective_of_weakEquivalence
  proof: by
  let h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) => f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (postcomp_bijective_of_fibration_of_weakEquivalence X h.r)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (postcomp_bijective_of_fibration_of_weakEquivalence X h.p).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

中文:
引理 postcomp_bijective_of_weakEquivalence
  证明: by
  let h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) => f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (postcomp_bijective_of_fibration_of_weakEquivalence X h.r)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (postcomp_bijective_of_fibration_of_weakEquivalence X h.p).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

Depends on / 依赖: Bijective, Classical, Classical.arbitrary, FibrantBrownFactorization, Function, Function.Bijective, Function.Bijective.of_comp_iff, Function.bijective_id, LeftHomotopyClass, arbitrary, bijective_id, convert, f.postcomp, mk_surjective, of_comp_iff, postcomp, postcomp_bijective_of_fibration_of_weakEquivalence
-/
lemma postcomp_bijective_of_weakEquivalence
    [IsCofibrant X] (g : Y ⟶ Z) [IsFibrant Y] [IsFibrant Z] [WeakEquivalence g] :
    Function.Bijective (fun (f : LeftHomotopyClass X Y) => f.postcomp g) := by
  let h : FibrantBrownFactorization g := Classical.arbitrary _
  have hi : Function.Bijective (fun (f : LeftHomotopyClass X Y) => f.postcomp h.i) := by
    rw [← Function.Bijective.of_comp_iff'
      (postcomp_bijective_of_fibration_of_weakEquivalence X h.r)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (postcomp_bijective_of_fibration_of_weakEquivalence X h.p).comp hi using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

end LeftHomotopyClass

namespace RightHomotopyClass

variable (Z)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `precomp_bijective_of_cofibration_of_weakEquivalence` / 引理 `precomp_bijective_of_cofibration_of_weakEquivalence`

English:
lemma precomp_bijective_of_cofibration_of_weakEquivalence
  proof: by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := sq.fac_right =≫ prod.fst
          rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
        h₁ := by
          have := sq.fac_right =≫ prod.snd
          rwa [Category.assoc, P.p_snd, prod.lift_snd] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := { }
    exact ⟨mk sq.lift, by simp⟩

中文:
引理 precomp_bijective_of_cofibration_of_weakEquivalence
  证明: by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := sq.fac_right =≫ prod.fst
          rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
        h₁ := by
          have := sq.fac_right =≫ prod.snd
          rwa [Category.assoc, P.p_snd, prod.lift_snd] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := { }
    exact ⟨mk sq.lift, by simp⟩

Depends on / 依赖: Category, Category.assoc, CommSq, P.p_fst, P.p_snd, exists_good_pathObject, fac_right, h.exists_good_pathObject, lift_fst, lift_snd, mk_eq_mk_iff, mk_surjective, p_fst, p_snd, precomp_mk, prod.fst, prod.lift, prod.lift_fst, prod.lift_snd, prod.snd
-/
lemma precomp_bijective_of_cofibration_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [Cofibration f] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) => g.precomp f) := by
  constructor
  · intro f₀ f₁ h
    obtain ⟨f₀, rfl⟩ := f₀.mk_surjective
    obtain ⟨f₁, rfl⟩ := f₁.mk_surjective
    simp only [precomp_mk, mk_eq_mk_iff] at h
    obtain ⟨P, _, ⟨h⟩⟩ := h.exists_good_pathObject
    have sq : CommSq h.h f P.p (prod.lift f₀ f₁) := { }
    rw [mk_eq_mk_iff]
    exact ⟨P,
      ⟨{h := sq.lift
        h₀ := by
          have := sq.fac_right =≫ prod.fst
          rwa [Category.assoc, P.p_fst, prod.lift_fst] at this
        h₁ := by
          have := sq.fac_right =≫ prod.snd
          rwa [Category.assoc, P.p_snd, prod.lift_snd] at this }⟩⟩
  · intro φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    have sq : CommSq φ f (terminal.from _) (terminal.from _) := { }
    exact ⟨mk sq.lift, by simp⟩

/--
lemma `precomp_bijective_of_weakEquivalence` / 引理 `precomp_bijective_of_weakEquivalence`

English:
lemma precomp_bijective_of_weakEquivalence
  proof: by
  let h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) => g.precomp h.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (precomp_bijective_of_cofibration_of_weakEquivalence Z h.s)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (precomp_bijective_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

中文:
引理 precomp_bijective_of_weakEquivalence
  证明: by
  let h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) => g.precomp h.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (precomp_bijective_of_cofibration_of_weakEquivalence Z h.s)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (precomp_bijective_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

Depends on / 依赖: Bijective, Classical, Classical.arbitrary, CofibrantBrownFactorization, Function, Function.Bijective, Function.Bijective.of_comp_iff, Function.bijective_id, RightHomotopyClass, arbitrary, bijective_id, convert, g.precomp, mk_surjective, of_comp_iff, precomp, precomp_bijective_of_cofibration_of_weakEquivalence
-/
lemma precomp_bijective_of_weakEquivalence
    [IsFibrant Z] (f : X ⟶ Y) [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f] :
    Function.Bijective (fun (g : RightHomotopyClass Y Z) => g.precomp f) := by
  let h : CofibrantBrownFactorization f := Classical.arbitrary _
  have hj : Function.Bijective (fun (g : RightHomotopyClass Y Z) => g.precomp h.p) := by
    rw [← Function.Bijective.of_comp_iff'
      (precomp_bijective_of_cofibration_of_weakEquivalence Z h.s)]
    convert! Function.bijective_id
    ext φ
    obtain ⟨φ, rfl⟩ := φ.mk_surjective
    simp
  convert! (precomp_bijective_of_cofibration_of_weakEquivalence Z h.i).comp hj using 1
  ext φ
  obtain ⟨φ, rfl⟩ := φ.mk_surjective
  simp

/--
lemma `whitehead` / 引理 `whitehead`

English:
lemma whitehead
  statement: [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
  proof: by
  obtain ⟨g, hg⟩ := (precomp_bijective_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (precomp_bijective_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff]; rw [← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

中文:
引理 whitehead
  结论: [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
  证明: by
  obtain ⟨g, hg⟩ := (precomp_bijective_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (precomp_bijective_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff]; rw [← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

Depends on / 依赖: Category, Category.comp_id, comp_id, g.mk_surjective, hg.postcomp, leftHomotopyRel_iff_rightHomotopyRel, mk_eq_mk_iff, mk_surjective, postcomp, precomp_bijective_of_weakEquivalence, precomp_mk
-/
lemma whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    exists (g : Y ⟶ X), RightHomotopyRel (f ≫ g) (𝟙 X) ∧ RightHomotopyRel (g ≫ f) (𝟙 Y) := by
  obtain ⟨g, hg⟩ := (precomp_bijective_of_weakEquivalence X f).2 (.mk (𝟙 X))
  obtain ⟨g, rfl⟩ := g.mk_surjective
  dsimp at hg
  refine ⟨g, by rwa [← mk_eq_mk_iff], ?_⟩
  rw [← mk_eq_mk_iff]
  apply (precomp_bijective_of_weakEquivalence Y f).1
  simp only [precomp_mk, Category.comp_id]
  rw [mk_eq_mk_iff]; rw [← leftHomotopyRel_iff_rightHomotopyRel] at hg ⊢
  simpa using hg.postcomp f

end RightHomotopyClass

/--
lemma `LeftHomotopyClass.whitehead` / 引理 `LeftHomotopyClass.whitehead`

English:
lemma LeftHomotopyClass.whitehead
  statement: [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
  proof: by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.whitehead

中文:
引理 LeftHomotopyClass.whitehead
  结论: [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
  证明: by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.whitehead

Depends on / 依赖: RightHomotopyClass, RightHomotopyClass.whitehead, leftHomotopyRel_iff_rightHomotopyRel, whitehead
-/
lemma LeftHomotopyClass.whitehead [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] :
    exists (g : Y ⟶ X), LeftHomotopyRel (f ≫ g) (𝟙 X) ∧ LeftHomotopyRel (g ≫ f) (𝟙 Y) := by
  simp only [leftHomotopyRel_iff_rightHomotopyRel]
  apply RightHomotopyClass.whitehead

section

variable [IsCofibrant X] [IsFibrant Y]

/--
Definition of `leftHomotopyClassEquivRightHomotopyClass` / `leftHomotopyClassEquivRightHomotopyClass` 的定义

English:
definition leftHomotopyClassEquivRightHomotopyClass
  signature: :
  body: Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]

中文:
定义 leftHomotopyClassEquivRightHomotopyClass
  签名: :
  定义体: Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]

Depends on / 依赖: LeftHomotopyClass, LeftHomotopyClass.mk_eq_mk_iff, Quot.lift, RightHomotopyClass, RightHomotopyClass.mk_eq_mk_iff, h.leftHomotopyRel, h.rightHomotopyRel, invFun, leftHomotopyRel, left_inv, mk_eq_mk_iff, rightHomotopyRel, right_inv
-/
def leftHomotopyClassEquivRightHomotopyClass :
    LeftHomotopyClass X Y ≃ RightHomotopyClass X Y where
  toFun := Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f => .mk f) (fun _ _ h => by
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
/--
lemma `leftHomotopyClassEquivRightHomotopyClass_mk` / 引理 `leftHomotopyClassEquivRightHomotopyClass_mk`

English:
lemma leftHomotopyClassEquivRightHomotopyClass_mk
  given: (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 leftHomotopyClassEquivRightHomotopyClass_mk
  条件: (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass (.mk f) = .mk f := rfl

@[simp]
/--
lemma `leftHomotopyClassEquivRightHomotopyClass_symm_mk` / 引理 `leftHomotopyClassEquivRightHomotopyClass_symm_mk`

English:
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk
  given: (f : X ⟶ Y)
  proof: rfl

中文:
引理 leftHomotopyClassEquivRightHomotopyClass_symm_mk
  条件: (f : X ⟶ Y)
  证明: rfl
-/
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass.symm (.mk f) = .mk f := rfl

end

end HomotopicalAlgebra
