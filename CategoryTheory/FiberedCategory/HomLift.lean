/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.CommSq

/-!

# HomLift

Given a functor `p : 𝒳 ⥤ 𝒮`, this file provides API for expressing the fact that `p(φ) = f`
for given morphisms `φ` and `f`. The reason this API is needed is because, in general, `p.map φ = f`
does not make sense when the domain and/or codomain of `φ` and `f` are not definitionally equal.

## Main definition

Given morphism `φ : a ⟶ b` in `𝒳` and `f : R ⟶ S` in `𝒮`, `p.IsHomLift f φ` is a class
which expresses the fact that `f = p(φ)`.

We also define a macro `subst_hom_lift p f φ` which can be used to substitute `f` with `p(φ)` in a
goal, this tactic is just short for `obtain ⟨⟩ := (inferInstance : p.IsHomLift f φ)`, and
it is used to make the code more readable.

## Implementation
The class `IsHomLift` is defined as an inductive with the single constructor
`.map (φ : a ⟶ b) : IsHomLift p (p.map φ) φ`, similar to how `Eq a b` has the single constructor
`.rfl (a : α) : Eq a a`.

-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)

namespace CategoryTheory

/--
Definition of `inductive` / `inductive` 的定义

English:
class inductive
  parameters: Functor.IsHomLift
  (no additional axioms)

中文:
类 inductive
  参数: 函子.IsHomLift
  (无附加公理)

Depends on / 依赖: Functor, Functor.IsHomLift, IsHomLift
-/
class inductive Functor.IsHomLift : forall {R S : 𝒮} {a b : 𝒳} (_ : R ⟶ S) (_ : a ⟶ b), Prop
  | map {a b : 𝒳} (φ : a ⟶ b) : IsHomLift (p.map φ) φ

/-- `subst_hom_lift p f φ` tries to substitute `f` with `p(φ)` by using `p.IsHomLift f φ` -/
macro "subst_hom_lift" p:term:max f:term:max φ:term:max : tactic =>
  `(tactic| obtain ⟨⟩ := (inferInstance : Functor.IsHomLift $p $f $φ))

namespace IsHomLift

/-- For any arrow `φ : a ⟶ b` in `𝒳`, `φ` lifts the arrow `p.map φ` in the base `𝒮`. -/
@[simp]
/--
Instance `map` / 实例 `map`

English:
instance map
  signature: {a b : 𝒳} (φ : a ⟶ b)
  body: .map φ

@[simp]

中文:
实例 map
  签名: {a b : 𝒳} (φ : a ⟶ b)
  定义体: .map φ

@[simp]
-/
instance map {a b : 𝒳} (φ : a ⟶ b) : p.IsHomLift (p.map φ) φ := .map φ

@[simp]
instance (a : 𝒳) : p.IsHomLift (𝟙 (p.obj a)) (𝟙 a) := by
  rw [← p.map_id]; infer_instance

/--
lemma `id` / 引理 `id`

English:
lemma id
  given: {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R)
  statement: p.IsHomLift (𝟙 R) (𝟙 a)
  proof: by
  cases ha; infer_instance

中文:
引理 id
  条件: {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R)
  结论: p.IsHomLift (𝟙 R) (𝟙 a)
  证明: by
  cases ha; infer_instance
-/
protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : p.IsHomLift (𝟙 R) (𝟙 a) := by
  cases ha; infer_instance

section

variable {R S : 𝒮} {a b : 𝒳}

/--
lemma `domain_eq` / 引理 `domain_eq`

English:
lemma domain_eq
  given: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  statement: p.obj a = R
  proof: by
  subst_hom_lift p f φ; rfl

中文:
引理 domain_eq
  条件: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  结论: p.obj a = R
  证明: by
  subst_hom_lift p f φ; rfl

Depends on / 依赖: subst_hom_lift
-/
lemma domain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj a = R := by
  subst_hom_lift p f φ; rfl

/--
lemma `codomain_eq` / 引理 `codomain_eq`

English:
lemma codomain_eq
  given: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  statement: p.obj b = S
  proof: by
  subst_hom_lift p f φ; rfl

中文:
引理 codomain_eq
  条件: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  结论: p.obj b = S
  证明: by
  subst_hom_lift p f φ; rfl

Depends on / 依赖: subst_hom_lift
-/
lemma codomain_eq (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : p.obj b = S := by
  subst_hom_lift p f φ; rfl

variable (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]

/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  statement: f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ)
  proof: by
  subst_hom_lift p f φ; simp

中文:
引理 fac
  结论: f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ)
  证明: by
  subst_hom_lift p f φ; simp

Depends on / 依赖: subst_hom_lift
-/
lemma fac : f = eqToHom (domain_eq p f φ).symm ≫ p.map φ ≫ eqToHom (codomain_eq p f φ) := by
  subst_hom_lift p f φ; simp

/--
lemma `fac'` / 引理 `fac'`

English:
lemma fac'
  statement: p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm
  proof: by
  subst_hom_lift p f φ; simp

中文:
引理 fac'
  结论: p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm
  证明: by
  subst_hom_lift p f φ; simp

Depends on / 依赖: subst_hom_lift
-/
lemma fac' : p.map φ = eqToHom (domain_eq p f φ) ≫ f ≫ eqToHom (codomain_eq p f φ).symm := by
  subst_hom_lift p f φ; simp

/--
lemma `commSq` / 引理 `commSq`

English:
lemma commSq
  statement: CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  proof: by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]

中文:
引理 commSq
  结论: 交换Sq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  证明: by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]

Depends on / 依赖: eqToHom_refl, eqToHom_trans_assoc, id_comp
-/
lemma commSq : CommSq (p.map φ) (eqToHom (domain_eq p f φ)) (eqToHom (codomain_eq p f φ)) f where
  w := by simp only [fac p f φ, eqToHom_trans_assoc, eqToHom_refl, id_comp]

end

/--
lemma `eq_of_isHomLift` / 引理 `eq_of_isHomLift`

English:
lemma eq_of_isHomLift
  given: {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ]
  proof: by
  simp only [fac p f φ, eqToHom_refl, comp_id, id_comp]

中文:
引理 eq_of_isHomLift
  条件: {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ]
  证明: by
  simp only [fac p f φ, eqToHom_refl, comp_id, id_comp]

Depends on / 依赖: comp_id, eqToHom_refl, id_comp
-/
lemma eq_of_isHomLift {a b : 𝒳} (f : p.obj a ⟶ p.obj b) (φ : a ⟶ b) [p.IsHomLift f φ] :
    f = p.map φ := by
  simp only [fac p f φ, eqToHom_refl, comp_id, id_comp]

/--
lemma `of_fac` / 引理 `of_fac`

English:
lemma of_fac
  statement: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  proof: by
  subst ha hb h; simp

中文:
引理 of_fac
  结论: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  证明: by
  subst ha hb h; simp
-/
lemma of_fac {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : f = eqToHom ha.symm ≫ p.map φ ≫ eqToHom hb) : p.IsHomLift f φ := by
  subst ha hb h; simp

/--
lemma `of_fac'` / 引理 `of_fac'`

English:
lemma of_fac'
  statement: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  proof: by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

中文:
引理 of_fac'
  结论: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  证明: by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

Depends on / 依赖: h.symm, infer_instance, p.map
-/
lemma of_fac' {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ = eqToHom ha ≫ f ≫ eqToHom hb.symm) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

/--
lemma `of_commsq` / 引理 `of_commsq`

English:
lemma of_commsq
  statement: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  proof: by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

中文:
引理 of_commsq
  结论: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  证明: by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

Depends on / 依赖: Nonempty, Nonempty.intro, h.symm, infer_instance, p.map
-/
lemma of_commsq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : p.map φ ≫ eqToHom hb = (eqToHom ha) ≫ f) : p.IsHomLift f φ := by
  subst ha hb
  obtain rfl : f = p.map φ := by simpa using h.symm
  infer_instance

/--
lemma `of_commSq` / 引理 `of_commSq`

English:
lemma of_commSq
  statement: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  proof: of_commsq p f φ ha hb h.1

中文:
引理 of_commSq
  结论: {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
  证明: of_commsq p f φ ha hb h.1

Depends on / 依赖: of_commsq
-/
lemma of_commSq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (ha : p.obj a = R) (hb : p.obj b = S)
    (h : CommSq (p.map φ) (eqToHom ha) (eqToHom hb) f) : p.IsHomLift f φ :=
  of_commsq p f φ ha hb h.1

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
  body: by
  apply of_commSq
  -- This line transforms the first goal in suitable form; the last line closes all three goals.
  on_goal 1 => rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)

中文:
实例 comp
  签名: {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
  定义体: by
  apply of_commSq
  -- This line transforms the first goal in suitable form; the last line closes all three goals.
  on_goal 1 => rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)

Depends on / 依赖: of_commSq
-/
instance comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (ψ : b ⟶ c) [p.IsHomLift f φ] [p.IsHomLift g ψ] : p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  apply of_commSq
  -- This line transforms the first goal in suitable form; the last line closes all three goals.
  on_goal 1 => rw [p.map_comp]
  apply CommSq.horiz_comp (commSq p f φ) (commSq p g ψ)

/--
Instance `comp_of_lift_id` / 实例 `comp_of_lift_id`

English:
instance comp_of_lift_id
  signature: (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
  body: comp_id (𝟙 R) ▸ comp p (𝟙 R) (𝟙 R) φ ψ

中文:
实例 comp_of_lift_id
  签名: (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
  定义体: comp_id (𝟙 R) ▸ comp p (𝟙 R) (𝟙 R) φ ψ

Depends on / 依赖: comp_id
-/
instance comp_of_lift_id (R : 𝒮) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [p.IsHomLift (𝟙 R) φ] [p.IsHomLift (𝟙 R) ψ] : p.IsHomLift (𝟙 R) (φ ≫ ψ) :=
  comp_id (𝟙 R) ▸ comp p (𝟙 R) (𝟙 R) φ ψ

/--
Instance `comp_lift_id_right` / 实例 `comp_lift_id_right`

English:
instance comp_lift_id_right
  signature: {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomLift f φ]
  body: by
  simpa using (inferInstance : p.IsHomLift (f ≫ 𝟙 T) (φ ≫ ψ))

中文:
实例 comp_lift_id_right
  签名: {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomLift f φ]
  定义体: by
  simpa using (inferInstance : p.IsHomLift (f ≫ 𝟙 T) (φ ≫ ψ))

Depends on / 依赖: IsHomLift, p.IsHomLift
-/
instance comp_lift_id_right {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (φ : a ⟶ b) [p.IsHomLift f φ]
    (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using (inferInstance : p.IsHomLift (f ≫ 𝟙 T) (φ ≫ ψ))

/--
lemma `comp_lift_id_right'` / 引理 `comp_lift_id_right'`

English:
lemma comp_lift_id_right'
  statement: {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  proof: by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  infer_instance

中文:
引理 comp_lift_id_right'
  结论: {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
  证明: by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  infer_instance

Depends on / 依赖: codomain_eq, domain_eq, infer_instance
-/
lemma comp_lift_id_right' {R S : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (T : 𝒮) (ψ : b ⟶ c) [p.IsHomLift (𝟙 T) ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : S = T := by rw [← codomain_eq p f φ, domain_eq p (𝟙 T) ψ]
  infer_instance

/--
Instance `comp_lift_id_left` / 实例 `comp_lift_id_left`

English:
instance comp_lift_id_left
  signature: {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ]
  body: by
  simpa using (inferInstance : p.IsHomLift (𝟙 S ≫ f) (φ ≫ ψ))

中文:
实例 comp_lift_id_left
  签名: {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ]
  定义体: by
  simpa using (inferInstance : p.IsHomLift (𝟙 S ≫ f) (φ ≫ ψ))

Depends on / 依赖: IsHomLift, p.IsHomLift
-/
instance comp_lift_id_left {a b c : 𝒳} {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ]
    (φ : a ⟶ b) [p.IsHomLift (𝟙 S) φ] : p.IsHomLift f (φ ≫ ψ) := by
  simpa using (inferInstance : p.IsHomLift (𝟙 S ≫ f) (φ ≫ ψ))

/--
lemma `comp_lift_id_left'` / 引理 `comp_lift_id_left'`

English:
lemma comp_lift_id_left'
  statement: {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ]
  proof: by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  infer_instance

中文:
引理 comp_lift_id_left'
  结论: {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ]
  证明: by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  infer_instance

Depends on / 依赖: codomain_eq, domain_eq, infer_instance
-/
lemma comp_lift_id_left' {a b c : 𝒳} (R : 𝒮) (φ : a ⟶ b) [p.IsHomLift (𝟙 R) φ]
    {S T : 𝒮} (f : S ⟶ T) (ψ : b ⟶ c) [p.IsHomLift f ψ] : p.IsHomLift f (φ ≫ ψ) := by
  obtain rfl : R = S := by rw [← codomain_eq p (𝟙 R) φ, domain_eq p f ψ]
  infer_instance

/--
lemma `eqToHom_domain_lift_id` / 引理 `eqToHom_domain_lift_id`

English:
lemma eqToHom_domain_lift_id
  given: {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R)
  proof: by
  subst hR hab; simp

中文:
引理 eqToHom_domain_lift_id
  条件: {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R)
  证明: by
  subst hR hab; simp
-/
lemma eqToHom_domain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {R : 𝒮} (hR : p.obj a = R) :
    p.IsHomLift (𝟙 R) (eqToHom hab) := by
  subst hR hab; simp

/--
lemma `eqToHom_codomain_lift_id` / 引理 `eqToHom_codomain_lift_id`

English:
lemma eqToHom_codomain_lift_id
  given: {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S)
  proof: by
  subst hS hab; simp

中文:
引理 eqToHom_codomain_lift_id
  条件: {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S)
  证明: by
  subst hS hab; simp
-/
lemma eqToHom_codomain_lift_id {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hab : a = b) {S : 𝒮} (hS : p.obj b = S) :
    p.IsHomLift (𝟙 S) (eqToHom hab) := by
  subst hS hab; simp

/--
lemma `id_lift_eqToHom_domain` / 引理 `id_lift_eqToHom_domain`

English:
lemma id_lift_eqToHom_domain
  given: {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R)
  proof: by
  subst hRS ha; simp

中文:
引理 id_lift_eqToHom_domain
  条件: {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R)
  证明: by
  subst hRS ha; simp
-/
lemma id_lift_eqToHom_domain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {a : 𝒳} (ha : p.obj a = R) :
    p.IsHomLift (eqToHom hRS) (𝟙 a) := by
  subst hRS ha; simp

/--
lemma `id_lift_eqToHom_codomain` / 引理 `id_lift_eqToHom_codomain`

English:
lemma id_lift_eqToHom_codomain
  given: {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S)
  proof: by
  subst hRS hb; simp

中文:
引理 id_lift_eqToHom_codomain
  条件: {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S)
  证明: by
  subst hRS hb; simp
-/
lemma id_lift_eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} (hRS : R = S) {b : 𝒳} (hb : p.obj b = S) :
    p.IsHomLift (eqToHom hRS) (𝟙 b) := by
  subst hRS hb; simp


section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]

/--
Instance `comp_id_lift` / 实例 `comp_id_lift`

English:
instance comp_id_lift
  signature: : p.IsHomLift f (𝟙 a ≫ φ)
  body: by
  simp_all

中文:
实例 comp_id_lift
  签名: : p.IsHomLift f (𝟙 a ≫ φ)
  定义体: by
  simp_all
-/
instance comp_id_lift : p.IsHomLift f (𝟙 a ≫ φ) := by
  simp_all

/--
Instance `id_comp_lift` / 实例 `id_comp_lift`

English:
instance id_comp_lift
  signature: : p.IsHomLift f (φ ≫ 𝟙 b)
  body: by
  simp_all

中文:
实例 id_comp_lift
  签名: : p.IsHomLift f (φ ≫ 𝟙 b)
  定义体: by
  simp_all
-/
instance id_comp_lift : p.IsHomLift f (φ ≫ 𝟙 b) := by
  simp_all

/--
Instance `lift_id_comp` / 实例 `lift_id_comp`

English:
instance lift_id_comp
  signature: : p.IsHomLift (𝟙 R ≫ f) φ
  body: by
  simp_all

中文:
实例 lift_id_comp
  签名: : p.IsHomLift (𝟙 R ≫ f) φ
  定义体: by
  simp_all
-/
instance lift_id_comp : p.IsHomLift (𝟙 R ≫ f) φ := by
  simp_all

/--
Instance `lift_comp_id` / 实例 `lift_comp_id`

English:
instance lift_comp_id
  signature: : p.IsHomLift (f ≫ 𝟙 S) φ
  body: by
  simp_all

中文:
实例 lift_comp_id
  签名: : p.IsHomLift (f ≫ 𝟙 S) φ
  定义体: by
  simp_all
-/
instance lift_comp_id : p.IsHomLift (f ≫ 𝟙 S) φ := by
  simp_all

/--
Instance `comp_eqToHom_lift` / 实例 `comp_eqToHom_lift`

English:
instance comp_eqToHom_lift
  signature: {a' : 𝒳} (h : a' = a)
  body: by
  subst h; simp_all

中文:
实例 comp_eqToHom_lift
  签名: {a' : 𝒳} (h : a' = a)
  定义体: by
  subst h; simp_all
-/
instance comp_eqToHom_lift {a' : 𝒳} (h : a' = a) : p.IsHomLift f (eqToHom h ≫ φ) := by
  subst h; simp_all

/--
Instance `eqToHom_comp_lift` / 实例 `eqToHom_comp_lift`

English:
instance eqToHom_comp_lift
  signature: {b' : 𝒳} (h : b = b')
  body: by
  subst h; simp_all

中文:
实例 eqToHom_comp_lift
  签名: {b' : 𝒳} (h : b = b')
  定义体: by
  subst h; simp_all
-/
instance eqToHom_comp_lift {b' : 𝒳} (h : b = b') : p.IsHomLift f (φ ≫ eqToHom h) := by
  subst h; simp_all

/--
Instance `lift_eqToHom_comp` / 实例 `lift_eqToHom_comp`

English:
instance lift_eqToHom_comp
  signature: {R' : 𝒮} (h : R' = R)
  body: by
  subst h; simp_all

中文:
实例 lift_eqToHom_comp
  签名: {R' : 𝒮} (h : R' = R)
  定义体: by
  subst h; simp_all
-/
instance lift_eqToHom_comp {R' : 𝒮} (h : R' = R) : p.IsHomLift (eqToHom h ≫ f) φ := by
  subst h; simp_all

/--
Instance `lift_comp_eqToHom` / 实例 `lift_comp_eqToHom`

English:
instance lift_comp_eqToHom
  signature: {S' : 𝒮} (h : S = S')
  body: by
  subst h; simp_all

中文:
实例 lift_comp_eqToHom
  签名: {S' : 𝒮} (h : S = S')
  定义体: by
  subst h; simp_all
-/
instance lift_comp_eqToHom {S' : 𝒮} (h : S = S') : p.IsHomLift (f ≫ eqToHom h) φ := by
  subst h; simp_all

end

@[simp]
/--
lemma `comp_eqToHom_lift_iff` / 引理 `comp_eqToHom_lift_iff`

English:
lemma comp_eqToHom_lift_iff
  given: {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a)
  proof: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]

中文:
引理 comp_eqToHom_lift_iff
  条件: {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a)
  证明: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
-/
lemma comp_eqToHom_lift_iff {R S : 𝒮} {a' a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : a' = a) :
    p.IsHomLift f (eqToHom h ≫ φ) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/--
lemma `eqToHom_comp_lift_iff` / 引理 `eqToHom_comp_lift_iff`

English:
lemma eqToHom_comp_lift_iff
  given: {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b')
  proof: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]

中文:
引理 eqToHom_comp_lift_iff
  条件: {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b')
  证明: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]

Depends on / 依赖: HasLimit, HasLimit.mk, kernelForkBiproductToSubtype
-/
lemma eqToHom_comp_lift_iff {R S : 𝒮} {a b b' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : b = b') :
    p.IsHomLift f (φ ≫ eqToHom h) ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/--
lemma `lift_eqToHom_comp_iff` / 引理 `lift_eqToHom_comp_iff`

English:
lemma lift_eqToHom_comp_iff
  given: {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R)
  proof: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]

中文:
引理 lift_eqToHom_comp_iff
  条件: {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R)
  证明: by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
-/
lemma lift_eqToHom_comp_iff {R' R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : R' = R) :
    p.IsHomLift (eqToHom h ≫ f) φ ↔ p.IsHomLift f φ where
  mp hφ' := by subst h; simpa using hφ'
  mpr _ := inferInstance

@[simp]
/--
lemma `lift_comp_eqToHom_iff` / 引理 `lift_comp_eqToHom_iff`

English:
lemma lift_comp_eqToHom_iff
  given: {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S')
  proof: fun hφ' => by subst h; simpa using hφ'
  mpr := fun _ => inferInstance

中文:
引理 lift_comp_eqToHom_iff
  条件: {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S')
  证明: fun hφ' => by subst h; simpa using hφ'
  mpr := fun _ => inferInstance
-/
lemma lift_comp_eqToHom_iff {R S S' : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) (h : S = S') :
    p.IsHomLift (f ≫ eqToHom h) φ ↔ p.IsHomLift f φ where
  mp := fun hφ' => by subst h; simpa using hφ'
  mpr := fun _ => inferInstance

section

variable {R S : 𝒮} {a b : 𝒳}

/-- Given a morphism `f : R ⟶ S`, and an isomorphism `φ : a ≅ b` lifting `f`, `isoOfIsoLift f φ` is
the isomorphism `Φ : R ≅ S` with `Φ.hom = f` induced from `φ` -/
@[simps hom]
/--
Definition of `isoOfIsoLift` / `isoOfIsoLift` 的定义

English:
definition isoOfIsoLift
  signature: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  body: f
  inv := eqToHom (codomain_eq p f φ.hom).symm ≫ (p.mapIso φ).inv ≫ eqToHom (domain_eq p f φ.hom)
  hom_inv_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
  inv_hom_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]

@[simp]

中文:
定义 isoOfIsoLift
  签名: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  定义体: f
  inv := eqToHom (codomain_eq p f φ.hom).symm ≫ (p.mapIso φ).inv ≫ eqToHom (domain_eq p f φ.hom)
  hom_inv_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
  inv_hom_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]

@[simp]

Depends on / 依赖: HasColimit, HasColimit.mk, cokernelCoforkBiproductFromSubtype
-/
def isoOfIsoLift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    R ≅ S where
  hom := f
  inv := eqToHom (codomain_eq p f φ.hom).symm ≫ (p.mapIso φ).inv ≫ eqToHom (domain_eq p f φ.hom)
  hom_inv_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]
  inv_hom_id := by subst_hom_lift p f φ.hom; simp [← p.map_comp]

@[simp]
/--
lemma `isoOfIsoLift_inv_hom_id` / 引理 `isoOfIsoLift_inv_hom_id`

English:
lemma isoOfIsoLift_inv_hom_id
  given: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  proof: (isoOfIsoLift p f φ).inv_hom_id

@[simp]

中文:
引理 isoOfIsoLift_inv_hom_id
  条件: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  证明: (isoOfIsoLift p f φ).inv_hom_id

@[simp]

Depends on / 依赖: inv_hom_id, isoOfIsoLift
-/
lemma isoOfIsoLift_inv_hom_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    (isoOfIsoLift p f φ).inv ≫ f = 𝟙 S :=
  (isoOfIsoLift p f φ).inv_hom_id

@[simp]
/--
lemma `isoOfIsoLift_hom_inv_id` / 引理 `isoOfIsoLift_hom_inv_id`

English:
lemma isoOfIsoLift_hom_inv_id
  given: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  proof: (isoOfIsoLift p f φ).hom_inv_id

中文:
引理 isoOfIsoLift_hom_inv_id
  条件: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  证明: (isoOfIsoLift p f φ).hom_inv_id

Depends on / 依赖: hom_inv_id, isoOfIsoLift
-/
lemma isoOfIsoLift_hom_inv_id (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    f ≫ (isoOfIsoLift p f φ).inv = 𝟙 R :=
  (isoOfIsoLift p f φ).hom_inv_id

/--
lemma `isIso_of_lift_isIso` / 引理 `isIso_of_lift_isIso`

English:
lemma isIso_of_lift_isIso
  given: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ]
  statement: IsIso f
  proof: (fac p f φ) ▸ inferInstance

中文:
引理 isIso_of_lift_isIso
  条件: (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [是同构 φ]
  结论: 是同构 f
  证明: (fac p f φ) ▸ inferInstance
-/
lemma isIso_of_lift_isIso (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [IsIso φ] : IsIso f :=
  (fac p f φ) ▸ inferInstance

/--
Instance `inv_lift_inv` / 实例 `inv_lift_inv`

English:
instance inv_lift_inv
  signature: (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom]
  body: by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (commSq p f.hom φ.hom)

中文:
实例 inv_lift_inv
  签名: (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom]
  定义体: by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (commSq p f.hom φ.hom)

Depends on / 依赖: CommSq, CommSq.horiz_inv, commSq, f.hom, horiz_inv, mapIso, of_commSq, p.mapIso
-/
instance inv_lift_inv (f : R ≅ S) (φ : a ≅ b) [p.IsHomLift f.hom φ.hom] :
    p.IsHomLift f.inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (commSq p f.hom φ.hom)

/--
Instance `inv_lift` / 实例 `inv_lift`

English:
instance inv_lift
  signature: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  body: by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (by apply commSq p f φ.hom)

中文:
实例 inv_lift
  签名: (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom]
  定义体: by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (by apply commSq p f φ.hom)

Depends on / 依赖: CommSq, CommSq.horiz_inv, commSq, horiz_inv, mapIso, of_commSq, p.mapIso
-/
instance inv_lift (f : R ⟶ S) (φ : a ≅ b) [p.IsHomLift f φ.hom] :
    p.IsHomLift (isoOfIsoLift p f φ).inv φ.inv := by
  apply of_commSq
  apply CommSq.horiz_inv (f := p.mapIso φ) (by apply commSq p f φ.hom)

/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: (f : R ⟶ S) (φ : a ⟶ b) [IsIso f] [IsIso φ] [p.IsHomLift f φ]
  body: have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp_all
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)

中文:
实例 inv
  签名: (f : R ⟶ S) (φ : a ⟶ b) [是同构 f] [是同构 φ] [p.IsHomLift f φ]
  定义体: have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp_all
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)
-/
protected instance inv (f : R ⟶ S) (φ : a ⟶ b) [IsIso f] [IsIso φ] [p.IsHomLift f φ] :
    p.IsHomLift (inv f) (inv φ) :=
  have : p.IsHomLift (asIso f).hom (asIso φ).hom := by simp_all
  IsHomLift.inv_lift_inv p (asIso f) (asIso φ)

end

/--
Instance `lift_id_inv` / 实例 `lift_id_inv`

English:
instance lift_id_inv
  signature: (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom]
  body: have : p.IsHomLift (asIso (𝟙 S)).hom φ.hom := by simp_all
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv_lift_inv p (asIso (𝟙 S)) φ)

中文:
实例 lift_id_inv
  签名: (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom]
  定义体: have : p.IsHomLift (asIso (𝟙 S)).hom φ.hom := by simp_all
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv_lift_inv p (asIso (𝟙 S)) φ)

Depends on / 依赖: IsHomLift, IsHomLift.inv_lift_inv, IsIso.inv_id, inv_id, inv_lift_inv, p.IsHomLift
-/
instance lift_id_inv (S : 𝒮) {a b : 𝒳} (φ : a ≅ b) [p.IsHomLift (𝟙 S) φ.hom] :
    p.IsHomLift (𝟙 S) φ.inv :=
  have : p.IsHomLift (asIso (𝟙 S)).hom φ.hom := by simp_all
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv_lift_inv p (asIso (𝟙 S)) φ)

/--
Instance `lift_id_inv_isIso` / 实例 `lift_id_inv_isIso`

English:
instance lift_id_inv_isIso
  signature: (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 S) φ]
  body: (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv p _ φ)

中文:
实例 lift_id_inv_isIso
  签名: (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [是同构 φ] [p.IsHomLift (𝟙 S) φ]
  定义体: (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv p _ φ)

Depends on / 依赖: IsHomLift, IsHomLift.inv, IsIso.inv_id, inv_id
-/
instance lift_id_inv_isIso (S : 𝒮) {a b : 𝒳} (φ : a ⟶ b) [IsIso φ] [p.IsHomLift (𝟙 S) φ] :
    p.IsHomLift (𝟙 S) (inv φ) :=
  (IsIso.inv_id (X := S)) ▸ (IsHomLift.inv p _ φ)

end IsHomLift

end CategoryTheory
