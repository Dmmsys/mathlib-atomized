/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The quotient category is linear

If `r : HomRel C` is a congruence on a preadditive category `C` which satisfies certain
compatibilities, we have already defined a preadditive structure on `Quotient r` in
the file `Mathlib/CategoryTheory/Quotient/Preadditive.lean` such that `functor r : C ⥤ Quotient r`
is an additive functor. In this file, assuming moreover that `C` is an `R`-linear category
and that the relation `r` is compatible with the scalar multiplication by any `a : R`, we
show that `Quotient r` is an `R`-linear category and that `functor r : C ⥤ Quotient r`
is an `R`-linear functor.

-/

@[expose] public section

namespace CategoryTheory

namespace Quotient

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]
  (r : HomRel C) [Congruence r]

namespace Linear

/-- The scalar multiplications on morphisms in `Quotient R`. -/
@[instance_reducible]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  body: Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hr _ _ _ h₁₂)

@[simp]

中文:
定义 smul
  签名: (hr : 对任意 (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  定义体: Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hr _ _ _ h₁₂)

@[simp]

Depends on / 依赖: HomRel, HomRel.compClosure_eq_self, Quot.lift, Quot.mk, Quot.sound, compClosure_eq_self
-/
def smul (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (X Y : Quotient r) : SMul R (X ⟶ Y) where
  smul a := Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hr _ _ _ h₁₂)

@[simp]
/--
lemma `smul_eq` / 引理 `smul_eq`

English:
lemma smul_eq
  statement: (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  proof: smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl

中文:
引理 smul_eq
  结论: (hr : 对任意 (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  证明: smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl
-/
lemma smul_eq (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (a : R) {X Y : C} (f : X ⟶ Y) :
    letI := smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl


/-- Auxiliary definition for `Quotient.Linear.module`. -/
@[instance_reducible]
/--
Definition of `module'` / `module'` 的定义

English:
definition module'
  signature: (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  body: letI smul := smul r hr ((functor r).obj X) ((functor r).obj Y)
  { smul_zero := fun a => by
      rw [← (functor r).map_zero X Y]; rw [smul_eq]; rw [smul_zero]
    zero_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [zero_smul]; rw [Functor.map_zero]
    one_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [one_smul]
    mul_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [mul_smul]
    smul_add := fun a f g => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      obtain ⟨g, rfl⟩ := (functor r).map_surjective g
      dsimp [smul]
      rw [← (functor r).map_add]; rw [smul_eq]; rw [← (functor r).map_add]; rw [smul_add]
    add_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [add_smul]; rw [Functor.map_add] }

中文:
定义 module'
  签名: (hr : 对任意 (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  定义体: letI smul := smul r hr ((functor r).obj X) ((functor r).obj Y)
  { smul_zero := fun a => by
      rw [← (functor r).map_zero X Y]; rw [smul_eq]; rw [smul_zero]
    zero_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [zero_smul]; rw [Functor.map_zero]
    one_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [one_smul]
    mul_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [mul_smul]
    smul_add := fun a f g => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      obtain ⟨g, rfl⟩ := (functor r).map_surjective g
      dsimp [smul]
      rw [← (functor r).map_add]; rw [smul_eq]; rw [← (functor r).map_add]; rw [smul_add]
    add_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [add_smul]; rw [Functor.map_add] }

Depends on / 依赖: Functor, Functor.map_zero, functor, map_surjective, map_zero, mul_smul, one_smul, smul_add, smul_eq, smul_zero, zero_smul
-/
def module' (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] (X Y : C) :
    Module R ((functor r).obj X ⟶ (functor r).obj Y) :=
  letI smul := smul r hr ((functor r).obj X) ((functor r).obj Y)
  { smul_zero := fun a => by
      rw [← (functor r).map_zero X Y]; rw [smul_eq]; rw [smul_zero]
    zero_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [zero_smul]; rw [Functor.map_zero]
    one_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [one_smul]
    mul_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [mul_smul]
    smul_add := fun a f g => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      obtain ⟨g, rfl⟩ := (functor r).map_surjective g
      dsimp [smul]
      rw [← (functor r).map_add]; rw [smul_eq]; rw [← (functor r).map_add]; rw [smul_add]
    add_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [add_smul]; rw [Functor.map_add] }

/-- Auxiliary definition for `Quotient.linear`. -/
@[instance_reducible]
/--
Definition of `module` / `module` 的定义

English:
definition module
  signature: (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  body: module' r hr X.as Y.as

中文:
定义 module
  签名: (hr : 对任意 (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  定义体: module' r hr X.as Y.as

Depends on / 依赖: X.as, Y.as, module
-/
def module (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] (X Y : Quotient r) :
    Module R (X ⟶ Y) := module' r hr X.as Y.as

end Linear

variable (R)

set_option backward.isDefEq.respectTransparency false in
/-- Assuming `Quotient r` has already been endowed with a preadditive category structure
such that `functor r : C ⥤ Quotient r` is additive, and that `C` has an `R`-linear category
structure compatible with `r`, this is the induced `R`-linear category structure on
`Quotient r`. -/
@[instance_reducible]
/--
Definition of `linear` / `linear` 的定义

English:
definition linear
  signature: (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  body: by
  letI := Linear.module r hr
  exact
    { smul_comp := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.smul_comp]
      comp_smul := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f a g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.comp_smul] }

中文:
定义 linear
  签名: (hr : 对任意 (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
  定义体: by
  letI := Linear.module r hr
  exact
    { smul_comp := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.smul_comp]
      comp_smul := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f a g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.comp_smul] }

Depends on / 依赖: Functor, Functor.map_comp, Linear, Linear.module, Linear.smul_comp, Linear.smul_eq, comp_smul, functor, map_comp, map_surjective, module, smul_comp, smul_eq
-/
def linear (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] : Linear R (Quotient r) := by
  letI := Linear.module r hr
  exact
    { smul_comp := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.smul_comp]
      comp_smul := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f a g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq]; rw [← Functor.map_comp]; rw [← Functor.map_comp]; rw [Linear.smul_eq]; rw [Linear.comp_smul] }

/--
Instance `linear_functor` / 实例 `linear_functor`

English:
instance linear_functor
  body: linear R r hr; Functor.Linear R (functor r) := by
  let := linear R r hr; exact { }

中文:
实例 linear_functor
  定义体: linear R r hr; Functor.Linear R (functor r) := by
  let := linear R r hr; exact { }

Depends on / 依赖: Functor, Functor.Linear, Linear, functor, linear
-/
instance linear_functor
    (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] :
    letI := linear R r hr; Functor.Linear R (functor r) := by
  let := linear R r hr; exact { }

end Quotient

end CategoryTheory
