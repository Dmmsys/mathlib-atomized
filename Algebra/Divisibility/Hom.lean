/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Mapping divisibility across multiplication-preserving homomorphisms

## Main definitions

* `map_dvd`

## Tags

divisibility, divides
-/

public section

attribute [local simp] mul_assoc mul_comm mul_left_comm

variable {M N : Type*}

@[gcongr]
/--
theorem `map_dvd` / 定理 `map_dvd`

English:
theorem map_dvd
  statement: [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]

中文:
定理 map_dvd
  结论: [Semigroup M] [Semigroup N] {F : 类型} [FunLike F M N] [MulHomClass F M N]
-/
theorem map_dvd [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]
    (f : F) {a b} : a ∣ b -> f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩

/--
theorem `MulHom.map_dvd` / 定理 `MulHom.map_dvd`

English:
theorem MulHom.map_dvd
  given: [Semigroup M] [Semigroup N] (f : M ->ₙ* N) {a b}
  statement: a ∣ b -> f a ∣ f b
  proof: _root_.map_dvd f

中文:
定理 MulHom.map_dvd
  条件: [Semigroup M] [Semigroup N] (f : M ->ₙ* N) {a b}
  结论: a ∣ b -> f a ∣ f b
  证明: _root_.map_dvd f

Depends on / 依赖: _root_, _root_.map_dvd, map_dvd
-/
theorem MulHom.map_dvd [Semigroup M] [Semigroup N] (f : M ->ₙ* N) {a b} : a ∣ b -> f a ∣ f b :=
  _root_.map_dvd f

/--
theorem `MonoidHom.map_dvd` / 定理 `MonoidHom.map_dvd`

English:
theorem MonoidHom.map_dvd
  given: [Monoid M] [Monoid N] (f : M ->* N) {a b}
  statement: a ∣ b -> f a ∣ f b
  proof: _root_.map_dvd f

中文:
定理 MonoidHom.map_dvd
  条件: [Monoid M] [Monoid N] (f : M ->* N) {a b}
  结论: a ∣ b -> f a ∣ f b
  证明: _root_.map_dvd f

Depends on / 依赖: _root_, _root_.map_dvd, map_dvd
-/
theorem MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M ->* N) {a b} : a ∣ b -> f a ∣ f b :=
  _root_.map_dvd f
