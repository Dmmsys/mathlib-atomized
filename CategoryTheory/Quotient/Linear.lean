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
/-
**CategoryTheory.Quotient.Linear.smul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Quotient.Linear`。
形式化陈述：smul (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • 
f₁) (a • f₂)) (X Y : Quotient r) : SMul R (X ⟶ Y) where smul a
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；X Y : Quotient r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scalar multiplications on morphisms in `Quotient R`.
-/
def smul (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (X Y : Quotient r) : SMul R (X ⟶ Y) where
  smul a := Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hr _ _ _ h₁₂)

@[simp]
/-
**CategoryTheory.Quotient.Linear.smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Quotient.Linear`。
形式化陈述：smul_eq (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a
 • f₁) (a • f₂)) (a : R) {X Y : C} (f : X ⟶ Y) : letI
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；a : R；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (a : R) {X Y : C} (f : X ⟶ Y) :
    letI := smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl


/-- Auxiliary definition for `Quotient.Linear.module`. -/
@[instance_reducible]
/-
**CategoryTheory.Quotient.Linear.module'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Quotient.Linear`。
形式化陈述：module' (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a
 • f₁) (a • f₂)) [Preadditive (Quotient r)] [(functor r).Additive] (X Y : C) : M
odule R ((functor r).obj X ⟶ (functor r).obj Y)
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；Quotient r；functor r；X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Quotient.Linear.module`.
-/
def module' (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] (X Y : C) :
    Module R ((functor r).obj X ⟶ (functor r).obj Y) :=
  letI smul := smul r hr ((functor r).obj X) ((functor r).obj Y)
  { smul_zero := fun a => by
      rw [← (functor r).map_zero X Y, smul_eq, smul_zero]
    zero_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [zero_smul, Functor.map_zero]
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
      rw [← (functor r).map_add, smul_eq, ← (functor r).map_add, smul_add]
    add_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [add_smul, Functor.map_add] }

/-- Auxiliary definition for `Quotient.linear`. -/
@[instance_reducible]
/-
**CategoryTheory.Quotient.Linear.module** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Quotient.Linear`。
形式化陈述：module (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a 
• f₁) (a • f₂)) [Preadditive (Quotient r)] [(functor r).Additive] (X Y : Quotien
t r) : Module R (X ⟶ Y)
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；Quotient r；functor r；X Y : Quotient r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Quotient.linear`.
-/
def module (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
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
/-
**CategoryTheory.Quotient.linear** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quoti
ent`。
形式化陈述：linear (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a 
• f₁) (a • f₂)) [Preadditive (Quotient r)] [(functor r).Additive] : Linear R (Qu
otient r)
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；Quotient r；functor r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming `Quotient r` has already been endowed with a preadditive category struc
ture
such that `functor r : C ⥤ Quotient r` is additive, and that `C` has an `R`-line
ar category
structure compatible with `r`, this is the induced `R`-linear category structure
 on
`Quotient r`.
-/
def linear (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] : Linear R (Quotient r) := by
  letI := Linear.module r hr
  exact
    { smul_comp := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq, ← Functor.map_comp, ← Functor.map_comp,
          Linear.smul_eq, Linear.smul_comp]
      comp_smul := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f a g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq, ← Functor.map_comp, ← Functor.map_comp,
          Linear.smul_eq, Linear.comp_smul] }
/-
**CategoryTheory.Quotient.linear_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Quotient`。
形式化陈述：linear_functor (hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂
), r (a • f₁) (a • f₂)) [Preadditive (Quotient r)] [(functor r).Additive] : letI
参数：hr : forall (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • 
f₂)；Quotient r；functor r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linear_functor
    (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] :
    letI := linear R r hr; Functor.Linear R (functor r) := by
  let := linear R r hr; exact { }

end Quotient

end CategoryTheory

