/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.PowerBasis

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `Polynomial.Separable f`: a polynomial `f` is separable iff it is coprime with its derivative.
* `IsSeparable K x`: an element `x` is separable over `K` iff the minimal polynomial of `x`
  over `K` is separable.
* `Algebra.IsSeparable K L`: `L` is separable over `K` iff every element in `L` is separable
  over `K`.

-/

@[expose] public section


universe u v w

open Polynomial Finset

namespace Polynomial

section CommSemiring

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
@[stacks 09H1 "first part"]
/--
Definition of `Separable` / `Separable` 的定义

English:
definition Separable
  signature: (f : R[X])
  body: IsCoprime f (derivative f)

中文:
定义 可分
  签名: (f : R[X])
  定义体: IsCoprime f (derivative f)

Depends on / 依赖: IsCoprime, derivative
-/
def Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)

/--
theorem `separable_def` / 定理 `separable_def`

English:
theorem separable_def
  given: (f : R[X])
  statement: f.Separable ↔ IsCoprime f (derivative f)
  proof: Iff.rfl

中文:
定理 separable_def
  条件: (f : R[X])
  结论: f.可分 ↔ IsCoprime f (derivative f)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem separable_def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl

/--
theorem `separable_def'` / 定理 `separable_def'`

English:
theorem separable_def'
  given: (f : R[X])
  statement: f.Separable ↔ exists a b : R[X], a * f + b * (derivative f) = 1
  proof: Iff.rfl

中文:
定理 separable_def'
  条件: (f : R[X])
  结论: f.可分 ↔ 存在 a b : R[X], a * f + b * (derivative f) = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem separable_def' (f : R[X]) : f.Separable ↔ exists a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl

/--
theorem `not_separable_zero` / 定理 `not_separable_zero`

English:
theorem not_separable_zero
  given: [Nontrivial R]
  statement: ¬Separable (0 : R[X])
  proof: by
  rintro ⟨x, y, h⟩
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h

中文:
定理 not_separable_zero
  条件: [非平凡 R]
  结论: ¬可分 (0 : R[X])
  证明: by
  rintro ⟨x, y, h⟩
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h

Depends on / 依赖: add_zero, derivative_zero, mul_zero, zero_ne_one
-/
theorem not_separable_zero [Nontrivial R] : ¬Separable (0 : R[X]) := by
  rintro ⟨x, y, h⟩
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h

/--
theorem `Separable.ne_zero` / 定理 `Separable.ne_zero`

English:
theorem Separable.ne_zero
  given: [Nontrivial R] {f : R[X]} (h : f.Separable)
  statement: f != 0
  proof: (not_separable_zero <| · ▸ h)

@[simp]

中文:
定理 可分.ne_zero
  条件: [非平凡 R] {f : R[X]} (h : f.可分)
  结论: f != 0
  证明: (not_separable_zero <| · ▸ h)

@[simp]

Depends on / 依赖: not_separable_zero
-/
theorem Separable.ne_zero [Nontrivial R] {f : R[X]} (h : f.Separable) : f != 0 :=
  (not_separable_zero <| · ▸ h)

@[simp]
/--
theorem `separable_one` / 定理 `separable_one`

English:
theorem separable_one
  statement: (1 : R[X]).Separable
  proof: isCoprime_one_left

@[nontriviality]

中文:
定理 separable_one
  结论: (1 : R[X]).可分
  证明: isCoprime_one_left

@[nontriviality]

Depends on / 依赖: isCoprime_one_left
-/
theorem separable_one : (1 : R[X]).Separable :=
  isCoprime_one_left

@[nontriviality]
/--
theorem `separable_of_subsingleton` / 定理 `separable_of_subsingleton`

English:
theorem separable_of_subsingleton
  given: [Subsingleton R] (f : R[X])
  statement: f.Separable
  proof: by
  simp [Separable, IsCoprime, eq_iff_true_of_subsingleton]

中文:
定理 separable_of_subsingleton
  条件: [子单例 R] (f : R[X])
  结论: f.可分
  证明: by
  simp [Separable, IsCoprime, eq_iff_true_of_subsingleton]

Depends on / 依赖: IsCoprime, Separable, eq_iff_true_of_subsingleton
-/
theorem separable_of_subsingleton [Subsingleton R] (f : R[X]) : f.Separable := by
  simp [Separable, IsCoprime, eq_iff_true_of_subsingleton]

/--
theorem `separable_X_add_C` / 定理 `separable_X_add_C`

English:
theorem separable_X_add_C
  given: (a : R)
  statement: (X + C a).Separable
  proof: by
  rw [separable_def]; rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]
  exact isCoprime_one_right

中文:
定理 separable_X_add_C
  条件: (a : R)
  结论: (X + C a).可分
  证明: by
  rw [separable_def]; rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]
  exact isCoprime_one_right

Depends on / 依赖: add_zero, derivative_C, derivative_X, derivative_add, isCoprime_one_right, separable_def
-/
theorem separable_X_add_C (a : R) : (X + C a).Separable := by
  rw [separable_def]; rw [derivative_add]; rw [derivative_X]; rw [derivative_C]; rw [add_zero]
  exact isCoprime_one_right

/--
theorem `separable_X` / 定理 `separable_X`

English:
theorem separable_X
  statement: (X : R[X]).Separable
  proof: by
  rw [separable_def]; rw [derivative_X]
  exact isCoprime_one_right

中文:
定理 separable_X
  结论: (X : R[X]).可分
  证明: by
  rw [separable_def]; rw [derivative_X]
  exact isCoprime_one_right

Depends on / 依赖: derivative_X, isCoprime_one_right, separable_def
-/
theorem separable_X : (X : R[X]).Separable := by
  rw [separable_def]; rw [derivative_X]
  exact isCoprime_one_right

/--
theorem `separable_C` / 定理 `separable_C`

English:
theorem separable_C
  given: (r : R)
  statement: (C r).Separable ↔ IsUnit r
  proof: by
  rw [separable_def]; rw [derivative_C]; rw [isCoprime_zero_right]; rw [isUnit_C]

中文:
定理 separable_C
  条件: (r : R)
  结论: (C r).可分 ↔ 是单位 r
  证明: by
  rw [separable_def]; rw [derivative_C]; rw [isCoprime_zero_right]; rw [isUnit_C]

Depends on / 依赖: derivative_C, isCoprime_zero_right, isUnit_C, separable_def
-/
theorem separable_C (r : R) : (C r).Separable ↔ IsUnit r := by
  rw [separable_def]; rw [derivative_C]; rw [isCoprime_zero_right]; rw [isUnit_C]

/--
theorem `Separable.of_mul_left` / 定理 `Separable.of_mul_left`

English:
theorem Separable.of_mul_left
  given: {f g : R[X]} (h : (f * g).Separable)
  statement: f.Separable
  proof: by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)

中文:
定理 可分.of_mul_left
  条件: {f g : R[X]} (h : (f * g).可分)
  结论: f.可分
  证明: by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)

Depends on / 依赖: IsCoprime, IsCoprime.of_add_mul_left_right, IsCoprime.of_mul_right_left, derivative_mul, h.of_mul_left_left, of_add_mul_left_right, of_mul_left_left, of_mul_right_left
-/
theorem Separable.of_mul_left {f g : R[X]} (h : (f * g).Separable) : f.Separable := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)

/--
theorem `Separable.of_mul_right` / 定理 `Separable.of_mul_right`

English:
theorem Separable.of_mul_right
  given: {f g : R[X]} (h : (f * g).Separable)
  statement: g.Separable
  proof: by
  rw [mul_comm] at h
  exact h.of_mul_left

中文:
定理 可分.of_mul_right
  条件: {f g : R[X]} (h : (f * g).可分)
  结论: g.可分
  证明: by
  rw [mul_comm] at h
  exact h.of_mul_left

Depends on / 依赖: h.of_mul_left, mul_comm, of_mul_left
-/
theorem Separable.of_mul_right {f g : R[X]} (h : (f * g).Separable) : g.Separable := by
  rw [mul_comm] at h
  exact h.of_mul_left

/--
theorem `Separable.of_dvd` / 定理 `Separable.of_dvd`

English:
theorem Separable.of_dvd
  given: {f g : R[X]} (hf : f.Separable) (hfg : g ∣ f)
  statement: g.Separable
  proof: by
  rcases hfg with ⟨f', rfl⟩
  exact Separable.of_mul_left hf

中文:
定理 可分.of_dvd
  条件: {f g : R[X]} (hf : f.可分) (hfg : g ∣ f)
  结论: g.可分
  证明: by
  rcases hfg with ⟨f', rfl⟩
  exact Separable.of_mul_left hf

Depends on / 依赖: Separable, Separable.of_mul_left, of_mul_left
-/
theorem Separable.of_dvd {f g : R[X]} (hf : f.Separable) (hfg : g ∣ f) : g.Separable := by
  rcases hfg with ⟨f', rfl⟩
  exact Separable.of_mul_left hf

/--
theorem `separable_gcd_left` / 定理 `separable_gcd_left`

English:
theorem separable_gcd_left
  statement: {F : Type*} [Field F] [DecidableEq F[X]]
  proof: Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)

中文:
定理 separable_gcd_left
  结论: {F : 类型} [域 F] [DecidableEq F[X]]
  证明: Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_dvd_left, Separable, Separable.of_dvd, gcd_dvd_left, of_dvd
-/
theorem separable_gcd_left {F : Type*} [Field F] [DecidableEq F[X]]
    {f : F[X]} (hf : f.Separable) (g : F[X]) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)

/--
theorem `separable_gcd_right` / 定理 `separable_gcd_right`

English:
theorem separable_gcd_right
  statement: {F : Type*} [Field F] [DecidableEq F[X]]
  proof: Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)

中文:
定理 separable_gcd_right
  结论: {F : 类型} [域 F] [DecidableEq F[X]]
  证明: Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_dvd_right, Separable, Separable.of_dvd, gcd_dvd_right, of_dvd
-/
theorem separable_gcd_right {F : Type*} [Field F] [DecidableEq F[X]]
    {g : F[X]} (f : F[X]) (hg : g.Separable) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)

/--
theorem `Separable.isCoprime` / 定理 `Separable.isCoprime`

English:
theorem Separable.isCoprime
  given: {f g : R[X]} (h : (f * g).Separable)
  statement: IsCoprime f g
  proof: by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)

中文:
定理 可分.isCoprime
  条件: {f g : R[X]} (h : (f * g).可分)
  结论: IsCoprime f g
  证明: by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)

Depends on / 依赖: IsCoprime, IsCoprime.of_add_mul_left_right, IsCoprime.of_mul_right_right, derivative_mul, h.of_mul_left_left, of_add_mul_left_right, of_mul_left_left, of_mul_right_right
-/
theorem Separable.isCoprime {f g : R[X]} (h : (f * g).Separable) : IsCoprime f g := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)

/--
theorem `Separable.of_pow'` / 定理 `Separable.of_pow'`

English:
theorem Separable.of_pow'
  given: {f : R[X]}

中文:
定理 可分.of_pow'
  条件: {f : R[X]}
-/
theorem Separable.of_pow' {f : R[X]} :
    forall {n : Nat} (_h : (f ^ n).Separable), IsUnit f ∨ f.Separable ∧ n = 1 ∨ n = 0
| 0 => fun _h => Or.inr Or.inr rfl
| 1 => fun h => Or.inr Or.inl ⟨pow_one f ▸ h, rfl⟩
  | n + 2 => fun h => by
    rw [pow_succ]; rw [pow_succ] at h
    exact Or.inl (isCoprime_self.1 h.isCoprime.of_mul_left_right)

/--
theorem `Separable.of_pow` / 定理 `Separable.of_pow`

English:
theorem Separable.of_pow
  statement: {f : R[X]} (hf : ¬IsUnit f) {n : Nat} (hn : n != 0)
  proof: (hfs.of_pow'.resolve_left hf).resolve_right hn

中文:
定理 可分.of_pow
  结论: {f : R[X]} (hf : ¬是单位 f) {n : 自然数} (hn : n != 0)
  证明: (hfs.of_pow'.resolve_left hf).resolve_right hn

Depends on / 依赖: hfs.of_pow, of_pow, resolve_left, resolve_right
-/
theorem Separable.of_pow {f : R[X]} (hf : ¬IsUnit f) {n : Nat} (hn : n != 0)
    (hfs : (f ^ n).Separable) : f.Separable ∧ n = 1 :=
  (hfs.of_pow'.resolve_left hf).resolve_right hn

/--
theorem `Separable.map` / 定理 `Separable.map`

English:
theorem Separable.map
  given: {p : R[X]} (h : p.Separable) {f : R ->+* S}
  statement: (p.map f).Separable
  proof: let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_add]; rw [H]; rw [Polynomial.map_one]⟩

中文:
定理 可分.map
  条件: {p : R[X]} (h : p.可分) {f : R ->+* S}
  结论: (p.map f).可分
  证明: let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_add]; rw [H]; rw [Polynomial.map_one]⟩

Depends on / 依赖: Polynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, a.map, b.map, derivative_map, map_add, map_mul, map_one
-/
theorem Separable.map {p : R[X]} (h : p.Separable) {f : R ->+* S} : (p.map f).Separable :=
  let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_mul]; rw [← Polynomial.map_add]; rw [H]; rw [Polynomial.map_one]⟩

/--
theorem `_root_.Associated.separable` / 定理 `_root_.Associated.separable`

English:
theorem _root_.Associated.separable
  statement: {f g : R[X]}
  proof: by
  grind [Separable.of_dvd, Associated.dvd']

中文:
定理 _root_.Associated.separable
  结论: {f g : R[X]}
  证明: by
  grind [Separable.of_dvd, Associated.dvd']

Depends on / 依赖: Associated, Associated.dvd, Separable, Separable.of_dvd, of_dvd
-/
theorem _root_.Associated.separable {f g : R[X]}
    (ha : Associated f g) (h : f.Separable) : g.Separable := by
  grind [Separable.of_dvd, Associated.dvd']

/--
theorem `_root_.Associated.separable_iff` / 定理 `_root_.Associated.separable_iff`

English:
theorem _root_.Associated.separable_iff
  statement: {f g : R[X]}
  proof: ⟨ha.separable, ha.symm.separable⟩

中文:
定理 _root_.Associated.separable_iff
  结论: {f g : R[X]}
  证明: ⟨ha.separable, ha.symm.separable⟩

Depends on / 依赖: ha.separable, ha.symm.separable, separable
-/
theorem _root_.Associated.separable_iff {f g : R[X]}
    (ha : Associated f g) : f.Separable ↔ g.Separable := ⟨ha.separable, ha.symm.separable⟩

/--
theorem `Separable.mul_unit` / 定理 `Separable.mul_unit`

English:
theorem Separable.mul_unit
  given: {f g : R[X]} (hf : f.Separable) (hg : IsUnit g)
  statement: (f * g).Separable
  proof: (associated_mul_unit_right f g hg).separable hf

中文:
定理 可分.mul_unit
  条件: {f g : R[X]} (hf : f.可分) (hg : 是单位 g)
  结论: (f * g).可分
  证明: (associated_mul_unit_right f g hg).separable hf

Depends on / 依赖: associated_mul_unit_right, separable
-/
theorem Separable.mul_unit {f g : R[X]} (hf : f.Separable) (hg : IsUnit g) : (f * g).Separable :=
  (associated_mul_unit_right f g hg).separable hf

/--
theorem `Separable.unit_mul` / 定理 `Separable.unit_mul`

English:
theorem Separable.unit_mul
  given: {f g : R[X]} (hf : IsUnit f) (hg : g.Separable)
  statement: (f * g).Separable
  proof: (associated_unit_mul_right g f hf).separable hg

中文:
定理 可分.unit_mul
  条件: {f g : R[X]} (hf : 是单位 f) (hg : g.可分)
  结论: (f * g).可分
  证明: (associated_unit_mul_right g f hf).separable hg

Depends on / 依赖: associated_unit_mul_right, separable
-/
theorem Separable.unit_mul {f g : R[X]} (hf : IsUnit f) (hg : g.Separable) : (f * g).Separable :=
  (associated_unit_mul_right g f hf).separable hg

/--
theorem `Separable.eval₂_derivative_ne_zero` / 定理 `Separable.eval₂_derivative_ne_zero`

English:
theorem Separable.eval₂_derivative_ne_zero
  statement: [Nontrivial S] (f : R ->+* S) {p : R[X]}
  proof: by
  intro hx'
  obtain ⟨a, b, e⟩ := h
  apply_fun Polynomial.eval₂ f x at e
  simp only [eval₂_add, eval₂_mul, hx, mul_zero, hx', add_zero, eval₂_one, zero_ne_one] at e

中文:
定理 可分.eval₂_derivative_ne_zero
  结论: [非平凡 S] (f : R ->+* S) {p : R[X]}
  证明: by
  intro hx'
  obtain ⟨a, b, e⟩ := h
  apply_fun Polynomial.eval₂ f x at e
  simp only [eval₂_add, eval₂_mul, hx, mul_zero, hx', add_zero, eval₂_one, zero_ne_one] at e

Depends on / 依赖: Polynomial, Polynomial.eval, add_zero, apply_fun, mul_zero, zero_ne_one
-/
theorem Separable.eval₂_derivative_ne_zero [Nontrivial S] (f : R ->+* S) {p : R[X]}
    (h : p.Separable) {x : S} (hx : p.eval₂ f x = 0) :
    (derivative p).eval₂ f x != 0 := by
  intro hx'
  obtain ⟨a, b, e⟩ := h
  apply_fun Polynomial.eval₂ f x at e
  simp only [eval₂_add, eval₂_mul, hx, mul_zero, hx', add_zero, eval₂_one, zero_ne_one] at e

/--
theorem `Separable.aeval_derivative_ne_zero` / 定理 `Separable.aeval_derivative_ne_zero`

English:
theorem Separable.aeval_derivative_ne_zero
  statement: [Nontrivial S] [Algebra R S] {p : R[X]}
  proof: h.eval₂_derivative_ne_zero (algebraMap R S) hx

中文:
定理 可分.aeval_derivative_ne_zero
  结论: [非平凡 S] [代数 R S] {p : R[X]}
  证明: h.eval₂_derivative_ne_zero (algebraMap R S) hx

Depends on / 依赖: algebraMap, h.eval
-/
theorem Separable.aeval_derivative_ne_zero [Nontrivial S] [Algebra R S] {p : R[X]}
    (h : p.Separable) {x : S} (hx : aeval x p = 0) :
    aeval x (derivative p) != 0 :=
  h.eval₂_derivative_ne_zero (algebraMap R S) hx

variable (p q : Nat)

/--
theorem `isUnit_of_self_mul_dvd_separable` / 定理 `isUnit_of_self_mul_dvd_separable`

English:
theorem isUnit_of_self_mul_dvd_separable
  given: {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p)
  proof: by
  obtain ⟨p, rfl⟩ := hq
  apply isCoprime_self.mp
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert! hp using 1
    rw [derivative_mul]; rw [derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)

中文:
定理 isUnit_of_self_mul_dvd_separable
  条件: {p q : R[X]} (hp : p.可分) (hq : q * q ∣ p)
  证明: by
  obtain ⟨p, rfl⟩ := hq
  apply isCoprime_self.mp
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert! hp using 1
    rw [derivative_mul]; rw [derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)

Depends on / 依赖: IsCoprime, IsCoprime.of_mul_left_left, IsCoprime.of_mul_right_left, Separable, convert, derivative, derivative_mul, isCoprime_self, isCoprime_self.mp, mul_add, mul_assoc, of_mul_left_left, of_mul_right_left
-/
theorem isUnit_of_self_mul_dvd_separable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) :
    IsUnit q := by
  obtain ⟨p, rfl⟩ := hq
  apply isCoprime_self.mp
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert! hp using 1
    rw [derivative_mul]; rw [derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)

/--
theorem `emultiplicity_le_one_of_separable` / 定理 `emultiplicity_le_one_of_separable`

English:
theorem emultiplicity_le_one_of_separable
  given: {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p)
  proof: by
  contrapose! hq
  apply isUnit_of_self_mul_dvd_separable hsep
  rw [← sq]
  apply pow_dvd_of_le_emultiplicity
  exact Order.add_one_le_of_lt hq

中文:
定理 emultiplicity_le_one_of_separable
  条件: {p q : R[X]} (hq : ¬是单位 q) (hsep : 可分 p)
  证明: by
  contrapose! hq
  apply isUnit_of_self_mul_dvd_separable hsep
  rw [← sq]
  apply pow_dvd_of_le_emultiplicity
  exact Order.add_one_le_of_lt hq

Depends on / 依赖: Order.add_one_le_of_lt, add_one_le_of_lt, contrapose, isUnit_of_self_mul_dvd_separable, pow_dvd_of_le_emultiplicity
-/
theorem emultiplicity_le_one_of_separable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) :
    emultiplicity q p <= 1 := by
  contrapose! hq
  apply isUnit_of_self_mul_dvd_separable hsep
  rw [← sq]
  apply pow_dvd_of_le_emultiplicity
  exact Order.add_one_le_of_lt hq

/--
theorem `Separable.squarefree` / 定理 `Separable.squarefree`

English:
theorem Separable.squarefree
  given: {p : R[X]} (hsep : Separable p)
  statement: Squarefree p
  proof: by
  rw [squarefree_iff_emultiplicity_le_one p]
  exact fun f => or_iff_not_imp_right.mpr fun hunit => emultiplicity_le_one_of_separable hunit hsep

中文:
定理 可分.squarefree
  条件: {p : R[X]} (hsep : 可分 p)
  结论: Squarefree p
  证明: by
  rw [squarefree_iff_emultiplicity_le_one p]
  exact fun f => or_iff_not_imp_right.mpr fun hunit => emultiplicity_le_one_of_separable hunit hsep

Depends on / 依赖: emultiplicity_le_one_of_separable, or_iff_not_imp_right, or_iff_not_imp_right.mpr, squarefree_iff_emultiplicity_le_one
-/
theorem Separable.squarefree {p : R[X]} (hsep : Separable p) : Squarefree p := by
  rw [squarefree_iff_emultiplicity_le_one p]
  exact fun f => or_iff_not_imp_right.mpr fun hunit => emultiplicity_le_one_of_separable hunit hsep

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/--
theorem `separable_X_sub_C` / 定理 `separable_X_sub_C`

English:
theorem separable_X_sub_C
  given: {x : R}
  statement: Separable (X - C x)
  proof: by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

中文:
定理 separable_X_sub_C
  条件: {x : R}
  结论: 可分 (X - C x)
  证明: by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

Depends on / 依赖: C_neg, separable_X_add_C, sub_eq_add_neg
-/
theorem separable_X_sub_C {x : R} : Separable (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)

/--
theorem `Separable.mul` / 定理 `Separable.mul`

English:
theorem Separable.mul
  given: {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g)
  proof: by
  rw [separable_def]; rw [derivative_mul]
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)

中文:
定理 可分.mul
  条件: {f g : R[X]} (hf : f.可分) (hg : g.可分) (h : IsCoprime f g)
  证明: by
  rw [separable_def]; rw [derivative_mul]
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)

Depends on / 依赖: add_mul_left_right, derivative_mul, h.symm.mul_right, hf.mul_right, mul_add_right_right, mul_left, mul_right, separable_def
-/
theorem Separable.mul {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g) :
    (f * g).Separable := by
  rw [separable_def]; rw [derivative_mul]
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)

/--
theorem `separable_prod'` / 定理 `separable_prod'`

English:
theorem separable_prod'
  given: {ι : Sort _} {f : ι -> R[X]} {s : Finset ι}
  proof: by
  classical
  exact Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)

中文:
定理 separable_prod'
  条件: {ι : 类型层 _} {f : ι -> R[X]} {s : 有限集 ι}
  证明: by
  classical
  exact Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, IsCoprime, IsCoprime.prod_right, Ne.symm, classical, forall_and, forall_mem_insert, induction_on, ne_of_mem_of_not_mem, prod_insert, prod_right, separable_one, simp_rw
-/
theorem separable_prod' {ι : Sort _} {f : ι -> R[X]} {s : Finset ι} :
    (forall x in s, forall y in s, x != y -> IsCoprime (f x) (f y)) ->
      (forall x in s, (f x).Separable) -> (∏ x in s, f x).Separable := by
  classical
  exact Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)

open scoped Function in -- required for scoped `on` notation
/--
theorem `separable_prod` / 定理 `separable_prod`

English:
theorem separable_prod
  statement: {ι : Sort _} [Fintype ι] {f : ι -> R[X]} (h1 : Pairwise (IsCoprime on f))
  proof: separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x

中文:
定理 separable_prod
  结论: {ι : 类型层 _} [有限类型 ι] {f : ι -> R[X]} (h1 : 两两 (IsCoprime on f))
  证明: separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x

Depends on / 依赖: separable_prod
-/
theorem separable_prod {ι : Sort _} [Fintype ι] {f : ι -> R[X]} (h1 : Pairwise (IsCoprime on f))
    (h2 : forall x, (f x).Separable) : (∏ x, f x).Separable :=
  separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x

/--
theorem `Separable.inj_of_prod_X_sub_C` / 定理 `Separable.inj_of_prod_X_sub_C`

English:
theorem Separable.inj_of_prod_X_sub_C
  statement: [Nontrivial R] {ι : Sort _} {f : ι -> R} {s : Finset ι}
  proof: by
  classical
  by_contra hxy
  rw [← insert_erase hx]; rw [prod_insert (notMem_erase _ _)]; rw [←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy)]; rw [prod_insert (notMem_erase _ _)]; rw [←
    mul_assoc]; rw [hfxy]; rw [← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2

中文:
定理 可分.inj_of_prod_X_sub_C
  结论: [非平凡 R] {ι : 类型层 _} {f : ι -> R} {s : 有限集 ι}
  证明: by
  classical
  by_contra hxy
  rw [← insert_erase hx]; rw [prod_insert (notMem_erase _ _)]; rw [←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy)]; rw [prod_insert (notMem_erase _ _)]; rw [←
    mul_assoc]; rw [hfxy]; rw [← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2

Depends on / 依赖: Ne.symm, classical, hfs.of_mul_left.of_pow, insert_erase, mem_erase_of_ne_of_mem, mul_assoc, notMem_erase, not_isUnit_X_sub_C, of_mul_left, of_pow, prod_insert, two_ne_zero
-/
theorem Separable.inj_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} {f : ι -> R} {s : Finset ι}
    (hfs : (∏ i in s, (X - C (f i))).Separable) {x y : ι} (hx : x in s) (hy : y in s)
    (hfxy : f x = f y) : x = y := by
  classical
  by_contra hxy
  rw [← insert_erase hx]; rw [prod_insert (notMem_erase _ _)]; rw [←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy)]; rw [prod_insert (notMem_erase _ _)]; rw [←
    mul_assoc]; rw [hfxy]; rw [← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2

/--
theorem `Separable.injective_of_prod_X_sub_C` / 定理 `Separable.injective_of_prod_X_sub_C`

English:
theorem Separable.injective_of_prod_X_sub_C
  statement: [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι -> R}
  proof: fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy

中文:
定理 可分.injective_of_prod_X_sub_C
  结论: [非平凡 R] {ι : 类型层 _} [有限类型 ι] {f : ι -> R}
  证明: fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy
-/
theorem Separable.injective_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι -> R}
    (hfs : (∏ i, (X - C (f i))).Separable) : Function.Injective f := fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy

/--
theorem `nodup_of_separable_prod` / 定理 `nodup_of_separable_prod`

English:
theorem nodup_of_separable_prod
  statement: [Nontrivial R] {s : Multiset R}
  proof: by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t rfl
  refine not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs ?_)
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)

中文:
定理 nodup_of_separable_prod
  结论: [非平凡 R] {s : Multiset R}
  证明: by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t rfl
  refine not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs ?_)
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)

Depends on / 依赖: Multiset, Multiset.map_cons, Multiset.nodup_iff_ne_cons_cons, Multiset.prod_cons, dvd_mul_right, isUnit_of_self_mul_dvd_separable, map_cons, mul_dvd_mul_left, nodup_iff_ne_cons_cons, not_isUnit_X_sub_C, prod_cons
-/
theorem nodup_of_separable_prod [Nontrivial R] {s : Multiset R}
    (hs : Separable (Multiset.map (fun a => X - C a) s).prod) : s.Nodup := by
  rw [Multiset.nodup_iff_ne_cons_cons]
  rintro a t rfl
  refine not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs ?_)
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)

/--
theorem `separable_X_pow_sub_C_unit` / 定理 `separable_X_pow_sub_C_unit`

English:
theorem separable_X_pow_sub_C_unit
  given: {n : Nat} (u : Rˣ) (hn : IsUnit (n : R))
  proof: by
  nontriviality R
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp at hn
  apply (separable_def' (X ^ n - C (u : R))).2
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  refine ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, ?_⟩
  rw [derivative_sub]; rw [derivative_C]; rw [sub_zero]; rw [derivative_pow X n]; rw [derivative_X]; rw [mul_one]
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_natCast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ',
        Nat.sub_add_cancel (show 1 <= n from hpos), sub_add_cancel]

中文:
定理 separable_X_pow_sub_C_unit
  条件: {n : 自然数} (u : Rˣ) (hn : 是单位 (n : R))
  证明: by
  nontriviality R
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp at hn
  apply (separable_def' (X ^ n - C (u : R))).2
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  refine ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, ?_⟩
  rw [derivative_sub]; rw [derivative_C]; rw [sub_zero]; rw [derivative_pow X n]; rw [derivative_X]; rw [mul_one]
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_natCast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ',
        Nat.sub_add_cancel (show 1 <= n from hpos), sub_add_cancel]

Depends on / 依赖: C.map_mul, C_eq_natC, derivative_C, derivative_X, derivative_pow, derivative_sub, eq_zero_or_pos, exists_left_inv, hn.exists_left_inv, map_mul, mul_one, n.eq_zero_or_pos, nontriviality, separable_def, sub_zero
-/
theorem separable_X_pow_sub_C_unit {n : Nat} (u : Rˣ) (hn : IsUnit (n : R)) :
    Separable (X ^ n - C (u : R)) := by
  nontriviality R
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp at hn
  apply (separable_def' (X ^ n - C (u : R))).2
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  refine ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, ?_⟩
  rw [derivative_sub]; rw [derivative_C]; rw [sub_zero]; rw [derivative_pow X n]; rw [derivative_X]; rw [mul_one]
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_natCast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ',
        Nat.sub_add_cancel (show 1 <= n from hpos), sub_add_cancel]

/--
theorem `separable_C_mul_X_pow_add_C_mul_X_add_C` / 定理 `separable_C_mul_X_pow_add_C_mul_X_add_C`

English:
theorem separable_C_mul_X_pow_add_C_mul_X_add_C
  proof: by
  set f := C a * X ^ n + C b * X + C c
  obtain ⟨e, hb⟩ := hb.exists_left_inv
  refine ⟨-derivative f, f + C e, ?_⟩
  have hderiv : derivative f = C b := by
    simp [hn, f, map_add derivative, derivative_C, derivative_X_pow]
  rw [hderiv]; rw [right_distrib]; rw [← add_assoc]; rw [neg_mul]; rw [mul_comm]; rw [neg_add_cancel]; rw [zero_add]; rw [← map_mul]; rw [hb]; rw [map_one]

中文:
定理 separable_C_mul_X_pow_add_C_mul_X_add_C
  证明: by
  set f := C a * X ^ n + C b * X + C c
  obtain ⟨e, hb⟩ := hb.exists_left_inv
  refine ⟨-derivative f, f + C e, ?_⟩
  have hderiv : derivative f = C b := by
    simp [hn, f, map_add derivative, derivative_C, derivative_X_pow]
  rw [hderiv]; rw [right_distrib]; rw [← add_assoc]; rw [neg_mul]; rw [mul_comm]; rw [neg_add_cancel]; rw [zero_add]; rw [← map_mul]; rw [hb]; rw [map_one]

Depends on / 依赖: add_assoc, derivative, derivative_C, derivative_X_pow, exists_left_inv, hb.exists_left_inv, hderiv, map_add, map_mul, map_one, mul_comm, neg_add_cancel, neg_mul, right_distrib, zero_add
-/
theorem separable_C_mul_X_pow_add_C_mul_X_add_C
    {n : Nat} (a b c : R) (hn : (n : R) = 0) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable := by
  set f := C a * X ^ n + C b * X + C c
  obtain ⟨e, hb⟩ := hb.exists_left_inv
  refine ⟨-derivative f, f + C e, ?_⟩
  have hderiv : derivative f = C b := by
    simp [hn, f, map_add derivative, derivative_C, derivative_X_pow]
  rw [hderiv]; rw [right_distrib]; rw [← add_assoc]; rw [neg_mul]; rw [mul_comm]; rw [neg_add_cancel]; rw [zero_add]; rw [← map_mul]; rw [hb]; rw [map_one]

/--
theorem `separable_C_mul_X_pow_add_C_mul_X_add_C'` / 定理 `separable_C_mul_X_pow_add_C_mul_X_add_C'`

English:
theorem separable_C_mul_X_pow_add_C_mul_X_add_C'
  proof: separable_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff R p n).2 hn) hb

中文:
定理 separable_C_mul_X_pow_add_C_mul_X_add_C'
  证明: separable_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff R p n).2 hn) hb

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, separable_C_mul_X_pow_add_C_mul_X_add_C
-/
theorem separable_C_mul_X_pow_add_C_mul_X_add_C'
    (p n : Nat) (a b c : R) [CharP R p] (hn : p ∣ n) (hb : IsUnit b) :
    (C a * X ^ n + C b * X + C c).Separable :=
  separable_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff R p n).2 hn) hb

/--
theorem `rootMultiplicity_le_one_of_separable` / 定理 `rootMultiplicity_le_one_of_separable`

English:
theorem rootMultiplicity_le_one_of_separable
  statement: [Nontrivial R] {p : R[X]} (hsep : Separable p)
  proof: by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]; rw [← Nat.cast_le (α := Nat∞)]; rw [Nat.cast_one]; rw [← (finiteMultiplicity_X_sub_C x hp).emultiplicity_eq_multiplicity]
  apply emultiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep

中文:
定理 rootMultiplicity_le_one_of_separable
  结论: [非平凡 R] {p : R[X]} (hsep : 可分 p)
  证明: by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]; rw [← Nat.cast_le (α := Nat∞)]; rw [Nat.cast_one]; rw [← (finiteMultiplicity_X_sub_C x hp).emultiplicity_eq_multiplicity]
  apply emultiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep

Depends on / 依赖: Nat.cast_le, Nat.cast_one, cast_le, cast_one, classical, emultiplicity_eq_multiplicity, emultiplicity_le_one_of_separable, finiteMultiplicity_X_sub_C, if_neg, not_isUnit_X_sub_C, rootMultiplicity_eq_multiplicity
-/
theorem rootMultiplicity_le_one_of_separable [Nontrivial R] {p : R[X]} (hsep : Separable p)
    (x : R) : rootMultiplicity x p <= 1 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [rootMultiplicity_eq_multiplicity]; rw [if_neg hp]; rw [← Nat.cast_le (α := Nat∞)]; rw [Nat.cast_one]; rw [← (finiteMultiplicity_X_sub_C x hp).emultiplicity_eq_multiplicity]
  apply emultiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep

end CommRing

section IsDomain

variable {R : Type u} [CommRing R] [IsDomain R]

/--
theorem `count_roots_le_one` / 定理 `count_roots_le_one`

English:
theorem count_roots_le_one
  given: [DecidableEq R] {p : R[X]} (hsep : Separable p) (x : R)
  proof: by
  rw [count_roots p]
  exact rootMultiplicity_le_one_of_separable hsep x

中文:
定理 count_roots_le_one
  条件: [DecidableEq R] {p : R[X]} (hsep : 可分 p) (x : R)
  证明: by
  rw [count_roots p]
  exact rootMultiplicity_le_one_of_separable hsep x

Depends on / 依赖: count_roots, rootMultiplicity_le_one_of_separable
-/
theorem count_roots_le_one [DecidableEq R] {p : R[X]} (hsep : Separable p) (x : R) :
    p.roots.count x <= 1 := by
  rw [count_roots p]
  exact rootMultiplicity_le_one_of_separable hsep x

/--
theorem `nodup_roots` / 定理 `nodup_roots`

English:
theorem nodup_roots
  given: {p : R[X]} (hsep : Separable p)
  statement: p.roots.Nodup
  proof: by
  classical
  exact Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

中文:
定理 nodup_roots
  条件: {p : R[X]} (hsep : 可分 p)
  结论: p.roots.Nodup
  证明: by
  classical
  exact Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

Depends on / 依赖: Multiset, Multiset.nodup_iff_count_le_one.mpr, classical, count_roots_le_one, nodup_iff_count_le_one
-/
theorem nodup_roots {p : R[X]} (hsep : Separable p) : p.roots.Nodup := by
  classical
  exact Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)

end IsDomain

section Field

variable {F : Type u} [Field F] {K : Type v} [Field K]

/--
theorem `separable_iff_derivative_ne_zero` / 定理 `separable_iff_derivative_ne_zero`

English:
theorem separable_iff_derivative_ne_zero
  given: {f : F[X]} (hf : Irreducible f)
  proof: ⟨fun h1 h2 => hf.not_isUnit isCoprime_zero_right.1 h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        rwa [Units.mul_right_dvd]
not_lt_of_ge (natDegree_le_of_dvd this h)
natDegree_derivative_lt mt derivative_of_natDegree_zero h⟩

中文:
定理 separable_iff_derivative_ne_zero
  条件: {f : F[X]} (hf : 不可约 f)
  证明: ⟨fun h1 h2 => hf.not_isUnit isCoprime_zero_right.1 h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        rwa [Units.mul_right_dvd]
not_lt_of_ge (natDegree_le_of_dvd this h)
natDegree_derivative_lt mt derivative_of_natDegree_zero h⟩

Depends on / 依赖: And.right, EuclideanDomain, EuclideanDomain.isCoprime_of_dvd, Units.mul_right_dvd, _hg2, conv_lhs, derivative, derivative_of_natDegree_zero, hf.isUnit_or_isUnit, hf.not_isUnit, isCoprime_of_dvd, isCoprime_zero_right, isUnit_or_isUnit, mul_right_dvd, natDegree_derivative_lt, natDegree_le_of_dvd, not_isUnit, not_lt_of_ge, resolve_left
-/
theorem separable_iff_derivative_ne_zero {f : F[X]} (hf : Irreducible f) :
    f.Separable ↔ derivative f != 0 :=
⟨fun h1 h2 => hf.not_isUnit isCoprime_zero_right.1 h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        rwa [Units.mul_right_dvd]
not_lt_of_ge (natDegree_le_of_dvd this h)
natDegree_derivative_lt mt derivative_of_natDegree_zero h⟩

attribute [local instance] Ideal.Quotient.field in
/--
theorem `separable_map` / 定理 `separable_map`

English:
theorem separable_map
  given: {S} [CommRing S] [Nontrivial S] (f : F ->+* S) {p : F[X]}
  proof: by
  refine ⟨fun H => ?_, fun H => H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_def, derivative_map, isCoprime_map] at this

中文:
定理 separable_map
  条件: {S} [交换环 S] [非平凡 S] (f : F ->+* S) {p : F[X]}
  证明: by
  refine ⟨fun H => ?_, fun H => H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_def, derivative_map, isCoprime_map] at this

Depends on / 依赖: H.map, Ideal.Quotient.mk, Ideal.exists_maximal, Quotient, Separable, Separable.map, derivative_map, exists_maximal, isCoprime_map, map_map, separable_def
-/
theorem separable_map {S} [CommRing S] [Nontrivial S] (f : F ->+* S) {p : F[X]} :
    (p.map f).Separable ↔ p.Separable := by
  refine ⟨fun H => ?_, fun H => H.map⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  have := Separable.map H (f := Ideal.Quotient.mk m)
  rwa [map_map, separable_def, derivative_map, isCoprime_map] at this

/--
theorem `separable_prod_X_sub_C_iff'` / 定理 `separable_prod_X_sub_C_iff'`

English:
theorem separable_prod_X_sub_C_iff'
  given: {ι : Sort _} {f : ι -> F} {s : Finset ι}
  proof: ⟨fun hfs _ hx _ hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x in s } (fun x => f x)
            (fun x y hxy => Subtype.ext <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩

中文:
定理 separable_prod_X_sub_C_iff'
  条件: {ι : 类型层 _} {f : ι -> F} {s : 有限集 ι}
  证明: ⟨fun hfs _ hx _ hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x in s } (fun x => f x)
            (fun x y hxy => Subtype.ext <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩

Depends on / 依赖: Subtype, Subtype.ext, hfs.inj_of_prod_X_sub_C, inj_of_prod_X_sub_C, pairwise_coprime_X_sub_C, prod_attach, separable_X_sub_C, separable_prod
-/
theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι -> F} {s : Finset ι} :
    (∏ i in s, (X - C (f i))).Separable ↔ forall x in s, forall y in s, f x = f y -> x = y :=
  ⟨fun hfs _ hx _ hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x in s } (fun x => f x)
            (fun x y hxy => Subtype.ext <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩

/--
theorem `separable_prod_X_sub_C_iff` / 定理 `separable_prod_X_sub_C_iff`

English:
theorem separable_prod_X_sub_C_iff
  given: {ι : Sort _} [Fintype ι] {f : ι -> F}
  proof: separable_prod_X_sub_C_iff'.trans by simp_rw [mem_univ, true_imp_iff, Function.Injective]

中文:
定理 separable_prod_X_sub_C_iff
  条件: {ι : 类型层 _} [有限类型 ι] {f : ι -> F}
  证明: separable_prod_X_sub_C_iff'.trans by simp_rw [mem_univ, true_imp_iff, Function.Injective]

Depends on / 依赖: Function, Function.Injective, Injective, mem_univ, separable_prod_X_sub_C_iff, simp_rw, true_imp_iff
-/
theorem separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι -> F} :
    (∏ i, (X - C (f i))).Separable ↔ Function.Injective f :=
separable_prod_X_sub_C_iff'.trans by simp_rw [mem_univ, true_imp_iff, Function.Injective]

section CharP

variable (p : Nat) [HF : CharP F p]

/--
theorem `separable_or` / 定理 `separable_or`

English:
theorem separable_or
  given: {f : F[X]} (hf : Irreducible f)
  proof: by
  classical
  exact if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    · have := CharP.charP_to_charZero F
      have := derivative_eq_zero.1 H
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      contradiction
    have := isLocalHom_expand F hp
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          Irreducible.of_map (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
else Or.inl (separable_iff_derivative_ne_zero hf).2 H

中文:
定理 separable_or
  条件: {f : F[X]} (hf : 不可约 f)
  证明: by
  classical
  exact if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    · have := CharP.charP_to_charZero F
      have := derivative_eq_zero.1 H
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      contradiction
    have := isLocalHom_expand F hp
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          Irreducible.of_map (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
else Or.inl (separable_iff_derivative_ne_zero hf).2 H

Depends on / 依赖: CharP.charP_to_charZero, Classical, Classical.not_not, Irreducible, Irreducible.of_map, Or.inl, Or.inr, charP_to_charZero, classical, contract, degree_pos_of_irreducible, derivative, derivative_eq_zero, eq_zero_or_pos, expand_contract, hp.ne, isLocalHom_expand, natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mpr, not_not
-/
theorem separable_or {f : F[X]} (hf : Irreducible f) :
    f.Separable ∨ ¬f.Separable ∧ exists g : F[X], Irreducible g ∧ expand F p g = f := by
  classical
  exact if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    · have := CharP.charP_to_charZero F
      have := derivative_eq_zero.1 H
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      contradiction
    have := isLocalHom_expand F hp
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          Irreducible.of_map (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
else Or.inl (separable_iff_derivative_ne_zero hf).2 H

/--
theorem `exists_separable_of_irreducible` / 定理 `exists_separable_of_irreducible`

English:
theorem exists_separable_of_irreducible
  given: {f : F[X]} (hf : Irreducible f) (hp : p != 0)
  proof: by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ N ih
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  · refine ⟨0, f, h, ?_⟩
    rw [pow_zero]; rw [expand_one]
  · rcases N with - | N
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      rw [hn]; rw [separable_C]; rw [isUnit_iff_ne_zero]; rw [Classical.not_not] at h1
      have hf0 : f != 0 := hf.ne_zero
      rw [h1]; rw [C_0] at hn
      exact absurd hn hf0
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    have hg2 : g.natDegree != 0 := by
      intro this
      rw [this]; rw [zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree]; rw [← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    refine ⟨n + 1, g, hg4, ?_⟩
    rw [← hgf]; rw [expand_expand]; rw [pow_succ']

中文:
定理 存在_separable_of_irreducible
  条件: {f : F[X]} (hf : 不可约 f) (hp : p != 0)
  证明: by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ N ih
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  · refine ⟨0, f, h, ?_⟩
    rw [pow_zero]; rw [expand_one]
  · rcases N with - | N
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      rw [hn]; rw [separable_C]; rw [isUnit_iff_ne_zero]; rw [Classical.not_not] at h1
      have hf0 : f != 0 := hf.ne_zero
      rw [h1]; rw [C_0] at hn
      exact absurd hn hf0
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    have hg2 : g.natDegree != 0 := by
      intro this
      rw [this]; rw [zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree]; rw [← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    refine ⟨n + 1, g, hg4, ?_⟩
    rw [← hgf]; rw [expand_expand]; rw [pow_succ']

Depends on / 依赖: CharP.char_is_prime_or_zero, Classical, Classical.not_not, Nat.strong_induction_on, char_is_prime_or_zero, degree_le_zero_iff, expand_one, f.natDegree, generalizing, hf.ne_zero, isUnit_iff_ne_zero, natDegree, natDegree_eq_zero_iff_degree_le_zero, ne_zero, not_not, p.Prime, pow_zero, replace, resolve_right, separable_C
-/
theorem exists_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : p != 0) :
    exists (n : Nat) (g : F[X]), g.Separable ∧ expand F (p ^ n) g = f := by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ N ih
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  · refine ⟨0, f, h, ?_⟩
    rw [pow_zero]; rw [expand_one]
  · rcases N with - | N
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      rw [hn]; rw [separable_C]; rw [isUnit_iff_ne_zero]; rw [Classical.not_not] at h1
      have hf0 : f != 0 := hf.ne_zero
      rw [h1]; rw [C_0] at hn
      exact absurd hn hf0
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    have hg2 : g.natDegree != 0 := by
      intro this
      rw [this]; rw [zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree]; rw [← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    refine ⟨n + 1, g, hg4, ?_⟩
    rw [← hgf]; rw [expand_expand]; rw [pow_succ']

/--
theorem `isUnit_or_eq_zero_of_separable_expand` / 定理 `isUnit_or_eq_zero_of_separable_expand`

English:
theorem isUnit_or_eq_zero_of_separable_expand
  statement: {f : F[X]} (n : Nat) (hp : 0 < p)
  proof: by
  rw [or_iff_not_imp_right]
  rintro hn : n != 0
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand]; rw [Nat.cast_pow]; rw [CharP.cast_eq_zero]; rw [zero_pow hn]; rw [zero_mul]; rw [mul_zero]
  rw [separable_def]; rw [hf2]; rw [isCoprime_zero_right]; rw [isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [eq_comm]; rw [expand_eq_C (pow_pos hp _)] at hrf
  rwa [hrf, isUnit_C]

中文:
定理 isUnit_or_eq_zero_of_separable_expand
  结论: {f : F[X]} (n : 自然数) (hp : 0 < p)
  证明: by
  rw [or_iff_not_imp_right]
  rintro hn : n != 0
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand]; rw [Nat.cast_pow]; rw [CharP.cast_eq_zero]; rw [zero_pow hn]; rw [zero_mul]; rw [mul_zero]
  rw [separable_def]; rw [hf2]; rw [isCoprime_zero_right]; rw [isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [eq_comm]; rw [expand_eq_C (pow_pos hp _)] at hrf
  rwa [hrf, isUnit_C]

Depends on / 依赖: CharP.cast_eq_zero, Nat.cast_pow, cast_eq_zero, cast_pow, derivative, derivative_expand, eq_comm, expand, expand_eq_C, isCoprime_zero_right, isUnit_C, isUnit_iff, mul_zero, or_iff_not_imp_right, pow_pos, separable_def, zero_mul, zero_pow
-/
theorem isUnit_or_eq_zero_of_separable_expand {f : F[X]} (n : Nat) (hp : 0 < p)
    (hf : (expand F (p ^ n) f).Separable) : IsUnit f ∨ n = 0 := by
  rw [or_iff_not_imp_right]
  rintro hn : n != 0
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand]; rw [Nat.cast_pow]; rw [CharP.cast_eq_zero]; rw [zero_pow hn]; rw [zero_mul]; rw [mul_zero]
  rw [separable_def]; rw [hf2]; rw [isCoprime_zero_right]; rw [isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [eq_comm]; rw [expand_eq_C (pow_pos hp _)] at hrf
  rwa [hrf, isUnit_C]

/--
theorem `unique_separable_of_irreducible` / 定理 `unique_separable_of_irreducible`

English:
theorem unique_separable_of_irreducible
  statement: {f : F[X]} (hf : Irreducible f) (hp : 0 < p) (n₁ : Nat)
  proof: by
  revert g₁ g₂
  wlog hn : n₁ <= n₂
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_ge hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
  intro g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  rw [le_iff_exists_add] at hn
  rcases hn with ⟨k, rfl⟩
  rw [← hgf₁]; rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos hp n₁)] at hgf₂
  subst hgf₂
  subst hgf₁
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  · rw [isUnit_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    simp_rw [expand_C] at hf
    exact absurd (isUnit_C.2 hr) hf.1
  · rw [add_zero, pow_zero, expand_one]
    constructor <;> rfl

中文:
定理 unique_separable_of_irreducible
  结论: {f : F[X]} (hf : 不可约 f) (hp : 0 < p) (n₁ : 自然数)
  证明: by
  revert g₁ g₂
  wlog hn : n₁ <= n₂
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_ge hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
  intro g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  rw [le_iff_exists_add] at hn
  rcases hn with ⟨k, rfl⟩
  rw [← hgf₁]; rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos hp n₁)] at hgf₂
  subst hgf₂
  subst hgf₁
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  · rw [isUnit_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    simp_rw [expand_C] at hf
    exact absurd (isUnit_C.2 hr) hf.1
  · rw [add_zero, pow_zero, expand_one]
    constructor <;> rfl

Depends on / 依赖: absurd, eq_comm, expand_C, expand_inj, expand_mul, isUnit_iff, isUnit_or_eq_zero_of_separable_expand, le_iff_exists_add, le_of_not_ge, pow_add, pow_pos, revert, simp_rw
-/
theorem unique_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : 0 < p) (n₁ : Nat)
    (g₁ : F[X]) (hg₁ : g₁.Separable) (hgf₁ : expand F (p ^ n₁) g₁ = f) (n₂ : Nat) (g₂ : F[X])
    (hg₂ : g₂.Separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ := by
  revert g₁ g₂
  wlog hn : n₁ <= n₂
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_ge hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
  intro g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  rw [le_iff_exists_add] at hn
  rcases hn with ⟨k, rfl⟩
  rw [← hgf₁]; rw [pow_add]; rw [expand_mul]; rw [expand_inj (pow_pos hp n₁)] at hgf₂
  subst hgf₂
  subst hgf₁
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  · rw [isUnit_iff] at h
    rcases h with ⟨r, hr, rfl⟩
    simp_rw [expand_C] at hf
    exact absurd (isUnit_C.2 hr) hf.1
  · rw [add_zero, pow_zero, expand_one]
    constructor <;> rfl

end CharP

/--
theorem `separable_X_pow_sub_C` / 定理 `separable_X_pow_sub_C`

English:
theorem separable_X_pow_sub_C
  given: {n : Nat} (a : F) (hn : (n : F) != 0) (ha : a != 0)
  proof: separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)

中文:
定理 separable_X_pow_sub_C
  条件: {n : 自然数} (a : F) (hn : (n : F) != 0) (ha : a != 0)
  证明: separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)

Depends on / 依赖: IsUnit, IsUnit.mk0, Units.mk0, separable_X_pow_sub_C_unit
-/
theorem separable_X_pow_sub_C {n : Nat} (a : F) (hn : (n : F) != 0) (ha : a != 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)

/--
theorem `separable_X_pow_sub_C'` / 定理 `separable_X_pow_sub_C'`

English:
theorem separable_X_pow_sub_C'
  given: (p n : Nat) (a : F) [CharP F p] (hn : ¬p ∣ n) (ha : a != 0)
  proof: separable_X_pow_sub_C a (by rwa [← CharP.cast_eq_zero_iff F p n] at hn) ha

中文:
定理 separable_X_pow_sub_C'
  条件: (p n : 自然数) (a : F) [特征p F p] (hn : ¬p ∣ n) (ha : a != 0)
  证明: separable_X_pow_sub_C a (by rwa [← CharP.cast_eq_zero_iff F p n] at hn) ha

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, separable_X_pow_sub_C
-/
theorem separable_X_pow_sub_C' (p n : Nat) (a : F) [CharP F p] (hn : ¬p ∣ n) (ha : a != 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C a (by rwa [← CharP.cast_eq_zero_iff F p n] at hn) ha

/--
theorem `X_pow_sub_C_separable_iff` / 定理 `X_pow_sub_C_separable_iff`

English:
theorem X_pow_sub_C_separable_iff
  given: {n : Nat} {x : F} (hn : 0 < n) (hx : x != 0)
  proof: by
  refine ⟨fun h hn' => ?_, fun h => separable_X_pow_sub_C x h hx⟩
exact not_isUnit_of_natDegree_pos (X ^ n - C x) (by simp [hn]) by
    simpa [separable_def, derivative_X_pow, hn', isCoprime_zero_right] using h

中文:
定理 X_pow_sub_C_separable_iff
  条件: {n : 自然数} {x : F} (hn : 0 < n) (hx : x != 0)
  证明: by
  refine ⟨fun h hn' => ?_, fun h => separable_X_pow_sub_C x h hx⟩
exact not_isUnit_of_natDegree_pos (X ^ n - C x) (by simp [hn]) by
    simpa [separable_def, derivative_X_pow, hn', isCoprime_zero_right] using h

Depends on / 依赖: derivative_X_pow, isCoprime_zero_right, not_isUnit_of_natDegree_pos, separable_X_pow_sub_C, separable_def
-/
theorem X_pow_sub_C_separable_iff {n : Nat} {x : F} (hn : 0 < n) (hx : x != 0) :
    (X ^ n - C x : F[X]).Separable ↔ (n : F) != 0 := by
  refine ⟨fun h hn' => ?_, fun h => separable_X_pow_sub_C x h hx⟩
exact not_isUnit_of_natDegree_pos (X ^ n - C x) (by simp [hn]) by
    simpa [separable_def, derivative_X_pow, hn', isCoprime_zero_right] using h

-- this can possibly be strengthened to making `separable_X_pow_sub_C_unit` a
-- bi-implication, but it is nontrivial!
/--
theorem `X_pow_sub_one_separable_iff` / 定理 `X_pow_sub_one_separable_iff`

English:
theorem X_pow_sub_one_separable_iff
  given: {n : Nat}
  statement: (X ^ n - 1 : F[X]).Separable ↔ (n : F) != 0
  proof: by
  rcases (Nat.eq_zero_or_pos n) with (hz | hpos)
  · simp_all [not_separable_zero]
  · exact X_pow_sub_C_separable_iff hpos one_ne_zero

中文:
定理 X_pow_sub_one_separable_iff
  条件: {n : 自然数}
  结论: (X ^ n - 1 : F[X]).可分 ↔ (n : F) != 0
  证明: by
  rcases (Nat.eq_zero_or_pos n) with (hz | hpos)
  · simp_all [not_separable_zero]
  · exact X_pow_sub_C_separable_iff hpos one_ne_zero

Depends on / 依赖: Nat.eq_zero_or_pos, X_pow_sub_C_separable_iff, eq_zero_or_pos, not_separable_zero, one_ne_zero
-/
theorem X_pow_sub_one_separable_iff {n : Nat} : (X ^ n - 1 : F[X]).Separable ↔ (n : F) != 0 := by
  rcases (Nat.eq_zero_or_pos n) with (hz | hpos)
  · simp_all [not_separable_zero]
  · exact X_pow_sub_C_separable_iff hpos one_ne_zero

section Splits

/--
theorem `card_rootSet_eq_natDegree` / 定理 `card_rootSet_eq_natDegree`

English:
theorem card_rootSet_eq_natDegree
  statement: [Algebra F K] {p : F[X]} (hsep : p.Separable)
  proof: by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map)]; rw [← hsplit.natDegree_eq_card_roots]; rw [natDegree_map]

中文:
定理 card_rootSet_eq_natDegree
  结论: [代数 F K] {p : F[X]} (hsep : p.可分)
  证明: by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map)]; rw [← hsplit.natDegree_eq_card_roots]; rw [natDegree_map]

Depends on / 依赖: Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, Multiset, Multiset.toFinset_card_of_nodup, card_coe, classical, coe_sort_coe, hsep.map, hsplit, hsplit.natDegree_eq_card_roots, natDegree_eq_card_roots, natDegree_map, nodup_roots, rootSet_def, simp_rw, toFinset_card_of_nodup
-/
theorem card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable)
    (hsplit : Splits (p.map (algebraMap F K))) : Fintype.card (p.rootSet K) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep.map)]; rw [← hsplit.natDegree_eq_card_roots]; rw [natDegree_map]

/--
theorem `nodup_roots_iff_of_splits` / 定理 `nodup_roots_iff_of_splits`

English:
theorem nodup_roots_iff_of_splits
  given: {f : F[X]} (hf : f != 0) (h : f.Splits)
  proof: by
  classical
  refine ⟨(fun hnsep => ?_).mtr, nodup_roots⟩
  rw [Separable]; rw [← gcd_isUnit_iff]; rw [isUnit_iff_degree_eq_zero] at hnsep
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (Splits.of_dvd h hf (gcd_dvd_left f _)) hnsep
  simp_rw [Multiset.nodup_iff_count_le_one, not_forall, not_le]
  exact ⟨x, ((one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx).trans_eq f.count_roots.symm⟩

中文:
定理 nodup_roots_iff_of_splits
  条件: {f : F[X]} (hf : f != 0) (h : f.Splits)
  证明: by
  classical
  refine ⟨(fun hnsep => ?_).mtr, nodup_roots⟩
  rw [Separable]; rw [← gcd_isUnit_iff]; rw [isUnit_iff_degree_eq_zero] at hnsep
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (Splits.of_dvd h hf (gcd_dvd_left f _)) hnsep
  simp_rw [Multiset.nodup_iff_count_le_one, not_forall, not_le]
  exact ⟨x, ((one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx).trans_eq f.count_roots.symm⟩

Depends on / 依赖: Multiset, Multiset.nodup_iff_count_le_one, Separable, Splits, Splits.exists_eval_eq_zero, Splits.of_dvd, classical, count_roots, exists_eval_eq_zero, f.count_roots.symm, gcd_dvd_left, gcd_isUnit_iff, isUnit_iff_degree_eq_zero, nodup_iff_count_le_one, nodup_roots, not_forall, not_le, of_dvd, one_lt_rootMultiplicity_iff_isRoot_gcd, simp_rw
-/
theorem nodup_roots_iff_of_splits {f : F[X]} (hf : f != 0) (h : f.Splits) :
    f.roots.Nodup ↔ f.Separable := by
  classical
  refine ⟨(fun hnsep => ?_).mtr, nodup_roots⟩
  rw [Separable]; rw [← gcd_isUnit_iff]; rw [isUnit_iff_degree_eq_zero] at hnsep
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (Splits.of_dvd h hf (gcd_dvd_left f _)) hnsep
  simp_rw [Multiset.nodup_iff_count_le_one, not_forall, not_le]
  exact ⟨x, ((one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx).trans_eq f.count_roots.symm⟩

/-- If a non-zero polynomial over `F` splits in `K`, then it has no repeated roots on `K`
if and only if it is separable. -/
@[stacks 09H3 "Here we only require `f` splits instead of `K` is algebraically closed."]
/--
theorem `nodup_aroots_iff_of_splits` / 定理 `nodup_aroots_iff_of_splits`

English:
theorem nodup_aroots_iff_of_splits
  statement: [Algebra F K] {f : F[X]} (hf : f != 0)
  proof: by
  rw [nodup_roots_iff_of_splits (map_ne_zero hf) h]; rw [separable_map]

中文:
定理 nodup_aroots_iff_of_splits
  结论: [代数 F K] {f : F[X]} (hf : f != 0)
  证明: by
  rw [nodup_roots_iff_of_splits (map_ne_zero hf) h]; rw [separable_map]

Depends on / 依赖: map_ne_zero, nodup_roots_iff_of_splits, separable_map
-/
theorem nodup_aroots_iff_of_splits [Algebra F K] {f : F[X]} (hf : f != 0)
    (h : (f.map (algebraMap F K)).Splits) : (f.aroots K).Nodup ↔ f.Separable := by
  rw [nodup_roots_iff_of_splits (map_ne_zero hf) h]; rw [separable_map]

/--
theorem `card_rootSet_eq_natDegree_iff_of_splits` / 定理 `card_rootSet_eq_natDegree_iff_of_splits`

English:
theorem card_rootSet_eq_natDegree_iff_of_splits
  statement: [Algebra F K] {f : F[X]} (hf : f != 0)
  proof: by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe,
    ← natDegree_map (algebraMap F K), h.natDegree_eq_card_roots,
    Multiset.toFinset_card_eq_card_iff_nodup, nodup_aroots_iff_of_splits hf h]

中文:
定理 card_rootSet_eq_natDegree_iff_of_splits
  结论: [代数 F K] {f : F[X]} (hf : f != 0)
  证明: by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe,
    ← natDegree_map (algebraMap F K), h.natDegree_eq_card_roots,
    Multiset.toFinset_card_eq_card_iff_nodup, nodup_aroots_iff_of_splits hf h]

Depends on / 依赖: Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, Multiset, Multiset.toFinset_card_eq_card_iff_nodup, algebraMap, card_coe, classical, coe_sort_coe, h.natDegree_eq_card_roots, natDegree_eq_card_roots, natDegree_map, nodup_aroots_iff_of_splits, rootSet_def, simp_rw, toFinset_card_eq_card_iff_nodup
-/
theorem card_rootSet_eq_natDegree_iff_of_splits [Algebra F K] {f : F[X]} (hf : f != 0)
    (h : (f.map (algebraMap F K)).Splits) :
    Fintype.card (f.rootSet K) = f.natDegree ↔ f.Separable := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe,
    ← natDegree_map (algebraMap F K), h.natDegree_eq_card_roots,
    Multiset.toFinset_card_eq_card_iff_nodup, nodup_aroots_iff_of_splits hf h]

variable {i : F ->+* K}

/--
theorem `eq_X_sub_C_of_separable_of_root_eq` / 定理 `eq_X_sub_C_of_separable_of_root_eq`

English:
theorem eq_X_sub_C_of_separable_of_root_eq
  statement: {x : F} {h : F[X]} (h_sep : h.Separable)
  proof: by
  have h_ne_zero : h != 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  suffices (map i h).roots = {i x} from
    map_injective i i.injective (by simpa using h_splits.eq_X_sub_C_of_single_root this)
  apply Finset.mk.inj
  · change _ = {i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · apply Finset.mem_mk.mpr
      · rw [mem_roots (show h.map i != 0 from map_ne_zero h_ne_zero)]
        rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [eval₂_hom]; rw [h_root]
        exact map_zero i
      · exact nodup_roots (Separable.map h_sep)
    · exact h_roots

中文:
定理 eq_X_sub_C_of_separable_of_root_eq
  结论: {x : F} {h : F[X]} (h_sep : h.可分)
  证明: by
  have h_ne_zero : h != 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  suffices (map i h).roots = {i x} from
    map_injective i i.injective (by simpa using h_splits.eq_X_sub_C_of_single_root this)
  apply Finset.mk.inj
  · change _ = {i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · apply Finset.mem_mk.mpr
      · rw [mem_roots (show h.map i != 0 from map_ne_zero h_ne_zero)]
        rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [eval₂_hom]; rw [h_root]
        exact map_zero i
      · exact nodup_roots (Separable.map h_sep)
    · exact h_roots

Depends on / 依赖: Finset, Finset.eq_singleton_iff_unique_mem, Finset.mem_mk.mpr, Finset.mk.inj, IsRoot, IsRoot.def, Separable, Separable.ma, eq_X_sub_C_of_single_root, eq_singleton_iff_unique_mem, h.map, h_ne_zero, h_root, h_sep, h_splits, h_splits.eq_X_sub_C_of_single_root, i.injective, injective, map_injective, map_ne_zero
-/
theorem eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]} (h_sep : h.Separable)
    (h_root : h.eval x = 0) (h_splits : Splits (h.map i))
    (h_roots : forall y in (h.map i).roots, y = i x) : h = C (leadingCoeff h) * (X - C x) := by
  have h_ne_zero : h != 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  suffices (map i h).roots = {i x} from
    map_injective i i.injective (by simpa using h_splits.eq_X_sub_C_of_single_root this)
  apply Finset.mk.inj
  · change _ = {i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · apply Finset.mem_mk.mpr
      · rw [mem_roots (show h.map i != 0 from map_ne_zero h_ne_zero)]
        rw [IsRoot.def]; rw [← eval₂_eq_eval_map]; rw [eval₂_hom]; rw [h_root]
        exact map_zero i
      · exact nodup_roots (Separable.map h_sep)
    · exact h_roots

/--
theorem `exists_finset_of_splits` / 定理 `exists_finset_of_splits`

English:
theorem exists_finset_of_splits
  statement: (i : F ->+* K) {f : F[X]} (sep : Separable f)
  proof: by
  classical
  obtain ⟨s, h⟩ := splits_iff_exists_multiset.1 sp
  use s.toFinset
  rw [h]; rw [Finset.prod_eq_multiset_prod]; rw [← Multiset.toFinset_eq]; rw [leadingCoeff_map]
  apply nodup_of_separable_prod
  apply Separable.of_mul_right
  rw [← h]
  exact sep.map

中文:
定理 存在_finset_of_splits
  结论: (i : F ->+* K) {f : F[X]} (sep : 可分 f)
  证明: by
  classical
  obtain ⟨s, h⟩ := splits_iff_exists_multiset.1 sp
  use s.toFinset
  rw [h]; rw [Finset.prod_eq_multiset_prod]; rw [← Multiset.toFinset_eq]; rw [leadingCoeff_map]
  apply nodup_of_separable_prod
  apply Separable.of_mul_right
  rw [← h]
  exact sep.map

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Multiset, Multiset.toFinset_eq, Separable, Separable.of_mul_right, classical, leadingCoeff_map, nodup_of_separable_prod, of_mul_right, prod_eq_multiset_prod, s.toFinset, sep.map, splits_iff_exists_multiset, toFinset, toFinset_eq
-/
theorem exists_finset_of_splits (i : F ->+* K) {f : F[X]} (sep : Separable f)
    (sp : Splits (f.map i)) :
    exists s : Finset K, f.map i = C (i f.leadingCoeff) * s.prod fun a : K => X - C a := by
  classical
  obtain ⟨s, h⟩ := splits_iff_exists_multiset.1 sp
  use s.toFinset
  rw [h]; rw [Finset.prod_eq_multiset_prod]; rw [← Multiset.toFinset_eq]; rw [leadingCoeff_map]
  apply nodup_of_separable_prod
  apply Separable.of_mul_right
  rw [← h]
  exact sep.map

end Splits

/--
theorem `_root_.Irreducible.separable` / 定理 `_root_.Irreducible.separable`

English:
theorem _root_.Irreducible.separable
  given: [CharZero F] {f : F[X]} (hf : Irreducible f)
  proof: by
  rw [separable_iff_derivative_ne_zero hf]; rw [Ne]; rw [← degree_eq_bot]; rw [degree_derivative]
  · rintro ⟨⟩
  exact hf.natDegree_pos.ne'

中文:
定理 _root_.不可约.separable
  条件: [特征零 F] {f : F[X]} (hf : 不可约 f)
  证明: by
  rw [separable_iff_derivative_ne_zero hf]; rw [Ne]; rw [← degree_eq_bot]; rw [degree_derivative]
  · rintro ⟨⟩
  exact hf.natDegree_pos.ne'

Depends on / 依赖: degree_derivative, degree_eq_bot, hf.natDegree_pos.ne, natDegree_pos, separable_iff_derivative_ne_zero
-/
theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable := by
  rw [separable_iff_derivative_ne_zero hf]; rw [Ne]; rw [← degree_eq_bot]; rw [degree_derivative]
  · rintro ⟨⟩
  exact hf.natDegree_pos.ne'

end Field

end Polynomial

open Polynomial

section CommRing

variable (F L K : Type*) [CommRing F] [Ring K] [Algebra F K]

-- TODO: refactor to allow transcendental extensions?
-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions
-- Note that right now a Galois extension (class `IsGalois`) is defined to be an extension which
-- is separable and normal, so if the definition of separable changes here at some point
-- to allow non-algebraic extensions, then the definition of `IsGalois` must also be changed.

variable {K} in
/--
An element `x` of an algebra `K` over a commutative ring `F` is said to be *separable*, if its
minimal polynomial over `K` is separable. Note that the minimal polynomial of any element not
integral over `F` is defined to be `0`, which is not a separable polynomial.
-/
@[stacks 09H1 "second part"]
/--
Definition of `IsSeparable` / `IsSeparable` 的定义

English:
definition IsSeparable
  signature: (x : K)
  body: Polynomial.Separable (minpoly F x)

中文:
定义 是可分
  签名: (x : K)
  定义体: Polynomial.Separable (minpoly F x)

Depends on / 依赖: Polynomial, Polynomial.Separable, Separable, minpoly
-/
def IsSeparable (x : K) : Prop := Polynomial.Separable (minpoly F x)

/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable. This implies that `K/F` is an algebraic
extension, because the minimal polynomial of a non-integral element is `0`, which is not
separable.

We define this for general (commutative) rings and only assume `F` and `K` are fields if this
is needed for a proof. -/
@[mk_iff isSeparable_def, stacks 09H1 "third part"]
/--
Definition of `Algebra.IsSeparable` / `Algebra.IsSeparable` 的定义

English:
class Algebra.IsSeparable
  parameters: : Prop where
  axioms and operations (1):
    - isSeparable' : forall x : K, IsSeparable F x

中文:
类 代数.是可分
  参数: : 命题 where
  公理与运算 (1 个):
    - isSeparable' : 对任意 x : K, 是可分 F x
-/
protected class Algebra.IsSeparable : Prop where
  isSeparable' : forall x : K, IsSeparable F x

variable {K}

/--
theorem `Algebra.IsSeparable.isSeparable` / 定理 `Algebra.IsSeparable.isSeparable`

English:
theorem Algebra.IsSeparable.isSeparable
  given: [Algebra.IsSeparable F K]
  statement: forall x : K, IsSeparable F x
  proof: Algebra.IsSeparable.isSeparable'

中文:
定理 代数.是可分.isSeparable
  条件: [代数.是可分 F K]
  结论: 对任意 x : K, 是可分 F x
  证明: Algebra.IsSeparable.isSeparable'

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable
-/
theorem Algebra.IsSeparable.isSeparable [Algebra.IsSeparable F K] : forall x : K, IsSeparable F x :=
  Algebra.IsSeparable.isSeparable'

variable {F} in
/--
theorem `IsSeparable.isIntegral` / 定理 `IsSeparable.isIntegral`

English:
theorem IsSeparable.isIntegral
  given: {x : K} (h : IsSeparable F x)
  statement: IsIntegral F x
  proof: by
  cases subsingleton_or_nontrivial F
  · have := Module.subsingleton F K
    exact ⟨1, monic_one, Subsingleton.elim _ _⟩
  · exact of_not_not (h.ne_zero <| minpoly.eq_zero ·)

中文:
定理 是可分.is整数egral
  条件: {x : K} (h : 是可分 F x)
  结论: 是整 F x
  证明: by
  cases subsingleton_or_nontrivial F
  · have := Module.subsingleton F K
    exact ⟨1, monic_one, Subsingleton.elim _ _⟩
  · exact of_not_not (h.ne_zero <| minpoly.eq_zero ·)

Depends on / 依赖: Module, Module.subsingleton, Subsingleton, Subsingleton.elim, eq_zero, h.ne_zero, minpoly, minpoly.eq_zero, monic_one, ne_zero, of_not_not, subsingleton, subsingleton_or_nontrivial
-/
theorem IsSeparable.isIntegral {x : K} (h : IsSeparable F x) : IsIntegral F x := by
  cases subsingleton_or_nontrivial F
  · have := Module.subsingleton F K
    exact ⟨1, monic_one, Subsingleton.elim _ _⟩
  · exact of_not_not (h.ne_zero <| minpoly.eq_zero ·)

/--
theorem `Algebra.IsSeparable.isIntegral` / 定理 `Algebra.IsSeparable.isIntegral`

English:
theorem Algebra.IsSeparable.isIntegral
  given: [Algebra.IsSeparable F K]
  statement: forall x : K, IsIntegral F x
  proof: fun x => _root_.IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F x)

中文:
定理 代数.是可分.is整数egral
  条件: [代数.是可分 F K]
  结论: 对任意 x : K, 是整 F x
  证明: fun x => _root_.IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F x)

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, _root_, _root_.IsSeparable.isIntegral, isIntegral, isSeparable
-/
theorem Algebra.IsSeparable.isIntegral [Algebra.IsSeparable F K] : forall x : K, IsIntegral F x :=
  fun x => _root_.IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F x)

variable (K) in
/--
Instance `Algebra.IsSeparable.isAlgebraic` / 实例 `Algebra.IsSeparable.isAlgebraic`

English:
instance Algebra.IsSeparable.isAlgebraic
  signature: [Nontrivial F] [Algebra.IsSeparable F K]
  body: ⟨fun x => (Algebra.IsSeparable.isIntegral F x).isAlgebraic⟩

中文:
实例 代数.是可分.isAlgebraic
  签名: [非平凡 F] [代数.是可分 F K]
  定义体: ⟨fun x => (Algebra.IsSeparable.isIntegral F x).isAlgebraic⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, IsSeparable, isAlgebraic, isIntegral
-/
instance Algebra.IsSeparable.isAlgebraic [Nontrivial F] [Algebra.IsSeparable F K] :
    Algebra.IsAlgebraic F K :=
  ⟨fun x => (Algebra.IsSeparable.isIntegral F x).isAlgebraic⟩

variable {F}

/--
theorem `Algebra.isSeparable_iff` / 定理 `Algebra.isSeparable_iff`

English:
theorem Algebra.isSeparable_iff
  proof: ⟨fun _ x => ⟨Algebra.IsSeparable.isIntegral F x, Algebra.IsSeparable.isSeparable F x⟩,
    fun h => ⟨fun x => (h x).2⟩⟩

中文:
定理 代数.isSeparable_iff
  证明: ⟨fun _ x => ⟨Algebra.IsSeparable.isIntegral F x, Algebra.IsSeparable.isSeparable F x⟩,
    fun h => ⟨fun x => (h x).2⟩⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, Algebra.IsSeparable.isSeparable, IsSeparable, isIntegral, isSeparable
-/
theorem Algebra.isSeparable_iff :
    Algebra.IsSeparable F K ↔ forall x : K, IsIntegral F x ∧ IsSeparable F x :=
  ⟨fun _ x => ⟨Algebra.IsSeparable.isIntegral F x, Algebra.IsSeparable.isSeparable F x⟩,
    fun h => ⟨fun x => (h x).2⟩⟩

variable {L}

/--
lemma `isSeparable_map_iff` / 引理 `isSeparable_map_iff`

English:
lemma isSeparable_map_iff
  statement: [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L)
  proof: by
  simp_rw [IsSeparable, minpoly.algHom_eq _ hf]

中文:
引理 isSeparable_map_iff
  结论: [环 L] [代数 F L] {x : K} (f : K ->ₐ[F] L)
  证明: by
  simp_rw [IsSeparable, minpoly.algHom_eq _ hf]

Depends on / 依赖: IsSeparable, algHom_eq, minpoly, minpoly.algHom_eq, simp_rw
-/
lemma isSeparable_map_iff [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L)
    (hf : Function.Injective f) : IsSeparable F (f x) ↔ IsSeparable F x := by
  simp_rw [IsSeparable, minpoly.algHom_eq _ hf]

/--
lemma `IsSeparable.map` / 引理 `IsSeparable.map`

English:
lemma IsSeparable.map
  statement: [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L) (hf : Function.Injective f)
  proof: (isSeparable_map_iff f hf).mpr H

中文:
引理 是可分.map
  结论: [环 L] [代数 F L] {x : K} (f : K ->ₐ[F] L) (hf : 函数.单射 f)
  证明: (isSeparable_map_iff f hf).mpr H

Depends on / 依赖: isSeparable_map_iff
-/
lemma IsSeparable.map [Ring L] [Algebra F L] {x : K} (f : K ->ₐ[F] L) (hf : Function.Injective f)
    (H : IsSeparable F x) : IsSeparable F (f x) :=
  (isSeparable_map_iff f hf).mpr H

/--
lemma `Subalgebra.isSeparable_iff` / 引理 `Subalgebra.isSeparable_iff`

English:
lemma Subalgebra.isSeparable_iff
  given: [Ring L] [Algebra F L] {S : Subalgebra F L}
  proof: by
  simp_rw [Algebra.isSeparable_def, Subtype.forall,
    ← isSeparable_map_iff S.val Subtype.val_injective, coe_val]

中文:
引理 子代数.isSeparable_iff
  条件: [环 L] [代数 F L] {S : 子代数 F L}
  证明: by
  simp_rw [Algebra.isSeparable_def, Subtype.forall,
    ← isSeparable_map_iff S.val Subtype.val_injective, coe_val]

Depends on / 依赖: Algebra, Algebra.isSeparable_def, S.val, Subtype, Subtype.forall, Subtype.val_injective, coe_val, isSeparable_def, isSeparable_map_iff, simp_rw, val_injective
-/
lemma Subalgebra.isSeparable_iff [Ring L] [Algebra F L] {S : Subalgebra F L} :
    Algebra.IsSeparable F S ↔ forall x in S, IsSeparable F x := by
  simp_rw [Algebra.isSeparable_def, Subtype.forall,
    ← isSeparable_map_iff S.val Subtype.val_injective, coe_val]

variable (L) {E : Type*}

section AlgEquiv

variable [Ring E] [Algebra F E] (e : K ≃ₐ[F] E)
include e

/--
theorem `AlgEquiv.isSeparable_iff` / 定理 `AlgEquiv.isSeparable_iff`

English:
theorem AlgEquiv.isSeparable_iff
  given: {x : K}
  statement: IsSeparable F (e x) ↔ IsSeparable F x
  proof: by
  simp only [IsSeparable, minpoly.algEquiv_eq e x]

中文:
定理 代数等价.isSeparable_iff
  条件: {x : K}
  结论: 是可分 F (e x) ↔ 是可分 F x
  证明: by
  simp only [IsSeparable, minpoly.algEquiv_eq e x]

Depends on / 依赖: IsSeparable, algEquiv_eq, minpoly, minpoly.algEquiv_eq
-/
theorem AlgEquiv.isSeparable_iff {x : K} : IsSeparable F (e x) ↔ IsSeparable F x := by
  simp only [IsSeparable, minpoly.algEquiv_eq e x]

/--
theorem `AlgEquiv.Algebra.isSeparable` / 定理 `AlgEquiv.Algebra.isSeparable`

English:
theorem AlgEquiv.Algebra.isSeparable
  given: [Algebra.IsSeparable F K]
  statement: Algebra.IsSeparable F E
  proof: ⟨fun _ => e.symm.isSeparable_iff.mp (Algebra.IsSeparable.isSeparable _ _)⟩

中文:
定理 代数等价.代数.isSeparable
  条件: [代数.是可分 F K]
  结论: 代数.是可分 F E
  证明: ⟨fun _ => e.symm.isSeparable_iff.mp (Algebra.IsSeparable.isSeparable _ _)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, e.symm.isSeparable_iff.mp, isSeparable, isSeparable_iff
-/
theorem AlgEquiv.Algebra.isSeparable [Algebra.IsSeparable F K] : Algebra.IsSeparable F E :=
  ⟨fun _ => e.symm.isSeparable_iff.mp (Algebra.IsSeparable.isSeparable _ _)⟩

/--
theorem `AlgEquiv.Algebra.isSeparable_iff` / 定理 `AlgEquiv.Algebra.isSeparable_iff`

English:
theorem AlgEquiv.Algebra.isSeparable_iff
  statement: Algebra.IsSeparable F K ↔ Algebra.IsSeparable F E
  proof: ⟨fun _ => AlgEquiv.Algebra.isSeparable e, fun _ => AlgEquiv.Algebra.isSeparable e.symm⟩

中文:
定理 代数等价.代数.isSeparable_iff
  结论: 代数.是可分 F K ↔ 代数.是可分 F E
  证明: ⟨fun _ => AlgEquiv.Algebra.isSeparable e, fun _ => AlgEquiv.Algebra.isSeparable e.symm⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.Algebra.isSeparable, Algebra, e.symm, isSeparable
-/
theorem AlgEquiv.Algebra.isSeparable_iff : Algebra.IsSeparable F K ↔ Algebra.IsSeparable F E :=
  ⟨fun _ => AlgEquiv.Algebra.isSeparable e, fun _ => AlgEquiv.Algebra.isSeparable e.symm⟩

end AlgEquiv

section IsScalarTower

variable [Field L] [Ring E] [Algebra F L]
    [Algebra F E] [Algebra L E] [IsScalarTower F L E]

/-- If `E / L / F` is a scalar tower and `x : E` is separable over `F`, then it's also separable
over `L`. -/
@[stacks 09H2 "first part"]
/--
theorem `IsSeparable.tower_top` / 定理 `IsSeparable.tower_top`

English:
theorem IsSeparable.tower_top
  proof: .of_dvd (.map h) (minpoly.dvd_map_of_isScalarTower ..)

中文:
定理 是可分.tower_top
  证明: .of_dvd (.map h) (minpoly.dvd_map_of_isScalarTower ..)

Depends on / 依赖: dvd_map_of_isScalarTower, minpoly, minpoly.dvd_map_of_isScalarTower, of_dvd
-/
theorem IsSeparable.tower_top
    {x : E} (h : IsSeparable F x) : IsSeparable L x :=
  .of_dvd (.map h) (minpoly.dvd_map_of_isScalarTower ..)

variable (F E) in
/-- If `E / K / F` is an extension tower, `E` is separable over `F`, then it's also separable
over `K`. -/
@[stacks 09H2 "second part"]
/--
theorem `Algebra.isSeparable_tower_top_of_isSeparable` / 定理 `Algebra.isSeparable_tower_top_of_isSeparable`

English:
theorem Algebra.isSeparable_tower_top_of_isSeparable
  given: [Algebra.IsSeparable F E]
  proof: ⟨fun x => IsSeparable.tower_top _ (Algebra.IsSeparable.isSeparable F x)⟩

中文:
定理 代数.isSeparable_tower_top_of_isSeparable
  条件: [代数.是可分 F E]
  证明: ⟨fun x => IsSeparable.tower_top _ (Algebra.IsSeparable.isSeparable F x)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, IsSeparable.tower_top, isSeparable, tower_top
-/
theorem Algebra.isSeparable_tower_top_of_isSeparable [Algebra.IsSeparable F E] :
    Algebra.IsSeparable L E :=
  ⟨fun x => IsSeparable.tower_top _ (Algebra.IsSeparable.isSeparable F x)⟩

end IsScalarTower

end CommRing

section Field

variable (F : Type*) [Field F] {K E E' : Type*}

section IsIntegral

variable [Ring K] [Algebra F K]

variable {F} in
/--
theorem `isSeparable_algebraMap` / 定理 `isSeparable_algebraMap`

English:
theorem isSeparable_algebraMap
  given: (x : F)
  statement: IsSeparable F (algebraMap F K x)
  proof: Polynomial.Separable.of_dvd (Polynomial.separable_X_sub_C (x := x))
    (minpoly.dvd F (algebraMap F K x) (by simp))

中文:
定理 isSeparable_algebraMap
  条件: (x : F)
  结论: 是可分 F (algebraMap F K x)
  证明: Polynomial.Separable.of_dvd (Polynomial.separable_X_sub_C (x := x))
    (minpoly.dvd F (algebraMap F K x) (by simp))

Depends on / 依赖: Polynomial, Polynomial.Separable.of_dvd, Polynomial.separable_X_sub_C, Separable, algebraMap, minpoly, minpoly.dvd, of_dvd, separable_X_sub_C
-/
theorem isSeparable_algebraMap (x : F) : IsSeparable F (algebraMap F K x) :=
  Polynomial.Separable.of_dvd (Polynomial.separable_X_sub_C (x := x))
    (minpoly.dvd F (algebraMap F K x) (by simp))

/--
Instance `Algebra.isSeparable_self` / 实例 `Algebra.isSeparable_self`

English:
instance Algebra.isSeparable_self
  signature: : Algebra.IsSeparable F F
  body: ⟨isSeparable_algebraMap⟩

中文:
实例 代数.isSeparable_self
  签名: : 代数.是可分 F F
  定义体: ⟨isSeparable_algebraMap⟩

Depends on / 依赖: isSeparable_algebraMap
-/
instance Algebra.isSeparable_self : Algebra.IsSeparable F F :=
  ⟨isSeparable_algebraMap⟩

variable [IsDomain K] [Algebra.IsIntegral F K] [CharZero F]

/--
theorem `IsSeparable.of_integral` / 定理 `IsSeparable.of_integral`

English:
theorem IsSeparable.of_integral
  given: (x : K)
  statement: IsSeparable F x
  proof: (minpoly.irreducible <| Algebra.IsIntegral.isIntegral x).separable

中文:
定理 是可分.of_integral
  条件: (x : K)
  结论: 是可分 F x
  证明: (minpoly.irreducible <| Algebra.IsIntegral.isIntegral x).separable

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, irreducible, isIntegral, minpoly, minpoly.irreducible, separable
-/
theorem IsSeparable.of_integral (x : K) : IsSeparable F x :=
  (minpoly.irreducible <| Algebra.IsIntegral.isIntegral x).separable

-- See note [lower instance priority]
variable (K) in
/-- An integral field extension in characteristic 0 is separable. -/
protected instance (priority := 100) Algebra.IsSeparable.of_integral : Algebra.IsSeparable F K :=
  ⟨_root_.IsSeparable.of_integral _⟩

end IsIntegral

section IsScalarTower

variable [Field K] [Ring E] [Algebra F K] [Algebra F E] [Algebra K E]
  [Nontrivial E] [IsScalarTower F K E]

variable {F} in
/--
theorem `IsSeparable.tower_bot` / 定理 `IsSeparable.tower_bot`

English:
theorem IsSeparable.tower_bot
  given: {x : K} (h : IsSeparable F (algebraMap K E x))
  statement: IsSeparable F x
  proof: have ⟨_q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    (Eq.mp (congrArg Separable hq) h).of_mul_left

中文:
定理 是可分.tower_bot
  条件: {x : K} (h : 是可分 F (algebraMap K E x))
  结论: 是可分 F x
  证明: have ⟨_q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    (Eq.mp (congrArg Separable hq) h).of_mul_left

Depends on / 依赖: Eq.mp, Separable, aeval_algebraMap_eq_zero_iff, algebraMap, minpoly, minpoly.aeval, minpoly.dvd, of_mul_left
-/
theorem IsSeparable.tower_bot {x : K} (h : IsSeparable F (algebraMap K E x)) : IsSeparable F x :=
    have ⟨_q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    (Eq.mp (congrArg Separable hq) h).of_mul_left

variable (K E) in
/--
theorem `Algebra.isSeparable_tower_bot_of_isSeparable` / 定理 `Algebra.isSeparable_tower_bot_of_isSeparable`

English:
theorem Algebra.isSeparable_tower_bot_of_isSeparable
  given: [h : Algebra.IsSeparable F E]
  proof: ⟨fun _ => IsSeparable.tower_bot (h.isSeparable _ _)⟩

中文:
定理 代数.isSeparable_tower_bot_of_isSeparable
  条件: [h : 代数.是可分 F E]
  证明: ⟨fun _ => IsSeparable.tower_bot (h.isSeparable _ _)⟩

Depends on / 依赖: IsSeparable, IsSeparable.tower_bot, h.isSeparable, isSeparable, tower_bot
-/
theorem Algebra.isSeparable_tower_bot_of_isSeparable [h : Algebra.IsSeparable F E] :
    Algebra.IsSeparable F K :=
  ⟨fun _ => IsSeparable.tower_bot (h.isSeparable _ _)⟩

end IsScalarTower

section

variable [Field E] [Field E'] [Algebra F E] [Algebra F E']
    (f : E ->ₐ[F] E')
include f

variable {F} in
/--
theorem `IsSeparable.of_algHom` / 定理 `IsSeparable.of_algHom`

English:
theorem IsSeparable.of_algHom
  given: {x : E} (h : IsSeparable F (f x))
  statement: IsSeparable F x
  proof: by
  let _ : Algebra E E' := RingHom.toAlgebra f.toRingHom
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact h.tower_bot

中文:
定理 是可分.of_algHom
  条件: {x : E} (h : 是可分 F (f x))
  结论: 是可分 F x
  证明: by
  let _ : Algebra E E' := RingHom.toAlgebra f.toRingHom
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact h.tower_bot

Depends on / 依赖: Algebra, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.toAlgebra, commutes, f.commutes, f.toRingHom, h.tower_bot, of_algebraMap_eq, toAlgebra, toRingHom, tower_bot
-/
theorem IsSeparable.of_algHom {x : E} (h : IsSeparable F (f x)) : IsSeparable F x := by
  let _ : Algebra E E' := RingHom.toAlgebra f.toRingHom
  have : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  exact h.tower_bot


variable (E') in
/--
theorem `Algebra.IsSeparable.of_algHom` / 定理 `Algebra.IsSeparable.of_algHom`

English:
theorem Algebra.IsSeparable.of_algHom
  given: [Algebra.IsSeparable F E']
  statement: Algebra.IsSeparable F E
  proof: ⟨fun x => (Algebra.IsSeparable.isSeparable F (f x)).of_algHom⟩

中文:
定理 代数.是可分.of_algHom
  条件: [代数.是可分 F E']
  结论: 代数.是可分 F E
  证明: ⟨fun x => (Algebra.IsSeparable.isSeparable F (f x)).of_algHom⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable, of_algHom
-/
theorem Algebra.IsSeparable.of_algHom [Algebra.IsSeparable F E'] : Algebra.IsSeparable F E :=
  ⟨fun x => (Algebra.IsSeparable.isSeparable F (f x)).of_algHom⟩

end

namespace IntermediateField

variable [Field K] [Algebra F K] (M : IntermediateField F K)

/--
Instance `isSeparable_tower_bot` / 实例 `isSeparable_tower_bot`

English:
instance isSeparable_tower_bot
  signature: [Algebra.IsSeparable F K]
  body: Algebra.isSeparable_tower_bot_of_isSeparable F M K

中文:
实例 isSeparable_tower_bot
  签名: [代数.是可分 F K]
  定义体: Algebra.isSeparable_tower_bot_of_isSeparable F M K

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, isSeparable_tower_bot_of_isSeparable
-/
instance isSeparable_tower_bot [Algebra.IsSeparable F K] : Algebra.IsSeparable F M :=
  Algebra.isSeparable_tower_bot_of_isSeparable F M K

/--
Instance `isSeparable_tower_top` / 实例 `isSeparable_tower_top`

English:
instance isSeparable_tower_top
  signature: [Algebra.IsSeparable F K]
  body: Algebra.isSeparable_tower_top_of_isSeparable F M K

中文:
实例 isSeparable_tower_top
  签名: [代数.是可分 F K]
  定义体: Algebra.isSeparable_tower_top_of_isSeparable F M K

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_top_of_isSeparable, isSeparable_tower_top_of_isSeparable
-/
instance isSeparable_tower_top [Algebra.IsSeparable F K] : Algebra.IsSeparable M K :=
  Algebra.isSeparable_tower_top_of_isSeparable F M K

end IntermediateField

end Field

section AlgEquiv

open RingHom RingEquiv

variable {A₁ B₁ A₂ B₂ : Type*} [Field A₁] [Ring B₁] [Field A₂] [Ring B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
include he

/--
lemma `IsSeparable.of_equiv_equiv` / 引理 `IsSeparable.of_equiv_equiv`

English:
lemma IsSeparable.of_equiv_equiv
  given: {x : B₁} (h : IsSeparable A₁ x)
  statement: IsSeparable A₂ (e₂ x)
  proof: letI := e₁.toRingHom.toAlgebra
  letI : Algebra A₂ B₁ :=
    { (algebraMap A₁ B₁).comp e₁.symm.toRingHom with
        algebraMap := (algebraMap A₁ B₁).comp e₁.symm.toRingHom
        smul := fun a b => ((algebraMap A₁ B₁).comp e₁.symm.toRingHom a) * b
        commutes' := fun r x => (Algebra.commutes) (e₁.symm.toRingHom r) x
        smul_def' := fun _ _ => rfl }
haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq fun x =>
(algebraMap A₁ B₁).congr_arg id ((e₁.symm_apply_apply x).symm)
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using! DFunLike.congr_fun he.symm (e₁.symm x) }
(AlgEquiv.isSeparable_iff e).mpr IsSeparable.tower_top A₂ h

中文:
引理 是可分.of_equiv_equiv
  条件: {x : B₁} (h : 是可分 A₁ x)
  结论: 是可分 A₂ (e₂ x)
  证明: letI := e₁.toRingHom.toAlgebra
  letI : Algebra A₂ B₁ :=
    { (algebraMap A₁ B₁).comp e₁.symm.toRingHom with
        algebraMap := (algebraMap A₁ B₁).comp e₁.symm.toRingHom
        smul := fun a b => ((algebraMap A₁ B₁).comp e₁.symm.toRingHom a) * b
        commutes' := fun r x => (Algebra.commutes) (e₁.symm.toRingHom r) x
        smul_def' := fun _ _ => rfl }
haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq fun x =>
(algebraMap A₁ B₁).congr_arg id ((e₁.symm_apply_apply x).symm)
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using! DFunLike.congr_fun he.symm (e₁.symm x) }
(AlgEquiv.isSeparable_iff e).mpr IsSeparable.tower_top A₂ h

Depends on / 依赖: Algebra, Algebra.commutes, IsScalarTower, IsScalarTower.of_algebraMap_eq, algebraMap, commutes, congr_arg, of_algebraMap_eq, smul_def, symm.toRingHom, symm_apply_apply, toAlgebra, toRingHom, toRingHom.toAlgebra
-/
lemma IsSeparable.of_equiv_equiv {x : B₁} (h : IsSeparable A₁ x) : IsSeparable A₂ (e₂ x) :=
  letI := e₁.toRingHom.toAlgebra
  letI : Algebra A₂ B₁ :=
    { (algebraMap A₁ B₁).comp e₁.symm.toRingHom with
        algebraMap := (algebraMap A₁ B₁).comp e₁.symm.toRingHom
        smul := fun a b => ((algebraMap A₁ B₁).comp e₁.symm.toRingHom a) * b
        commutes' := fun r x => (Algebra.commutes) (e₁.symm.toRingHom r) x
        smul_def' := fun _ _ => rfl }
haveI : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq fun x =>
(algebraMap A₁ B₁).congr_arg id ((e₁.symm_apply_apply x).symm)
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun x => by
        simpa [RingHom.algebraMap_toAlgebra] using! DFunLike.congr_fun he.symm (e₁.symm x) }
(AlgEquiv.isSeparable_iff e).mpr IsSeparable.tower_top A₂ h

/--
lemma `Algebra.IsSeparable.of_equiv_equiv` / 引理 `Algebra.IsSeparable.of_equiv_equiv`

English:
lemma Algebra.IsSeparable.of_equiv_equiv
  given: [Algebra.IsSeparable A₁ B₁]
  statement: Algebra.IsSeparable A₂ B₂
  proof: ⟨fun x => (e₂.apply_symm_apply x) ▸ _root_.IsSeparable.of_equiv_equiv e₁ e₂ he
    (Algebra.IsSeparable.isSeparable _ _)⟩

中文:
引理 代数.是可分.of_equiv_equiv
  条件: [代数.是可分 A₁ B₁]
  结论: 代数.是可分 A₂ B₂
  证明: ⟨fun x => (e₂.apply_symm_apply x) ▸ _root_.IsSeparable.of_equiv_equiv e₁ e₂ he
    (Algebra.IsSeparable.isSeparable _ _)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, _root_, _root_.IsSeparable.of_equiv_equiv, apply_symm_apply, isSeparable, of_equiv_equiv
-/
lemma Algebra.IsSeparable.of_equiv_equiv [Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂ :=
  ⟨fun x => (e₂.apply_symm_apply x) ▸ _root_.IsSeparable.of_equiv_equiv e₁ e₂ he
    (Algebra.IsSeparable.isSeparable _ _)⟩

/--
lemma `Algebra.IsSeparable.iff_of_equiv_equiv` / 引理 `Algebra.IsSeparable.iff_of_equiv_equiv`

English:
lemma Algebra.IsSeparable.iff_of_equiv_equiv
  proof: ⟨fun _ => Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he,
    fun _ => Algebra.IsSeparable.of_equiv_equiv e₁.symm e₂.symm (by
      ext x
      simpa [RingEquiv.eq_symm_apply] using (RingHom.ext_iff.mp he (e₁.symm x)).symm)⟩

中文:
引理 代数.是可分.iff_of_equiv_equiv
  证明: ⟨fun _ => Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he,
    fun _ => Algebra.IsSeparable.of_equiv_equiv e₁.symm e₂.symm (by
      ext x
      simpa [RingEquiv.eq_symm_apply] using (RingHom.ext_iff.mp he (e₁.symm x)).symm)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.of_equiv_equiv, IsSeparable, RingEquiv, RingEquiv.eq_symm_apply, RingHom, RingHom.ext_iff.mp, eq_symm_apply, ext_iff, of_equiv_equiv
-/
lemma Algebra.IsSeparable.iff_of_equiv_equiv :
    Algebra.IsSeparable A₁ B₁ ↔ Algebra.IsSeparable A₂ B₂ :=
  ⟨fun _ => Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he,
    fun _ => Algebra.IsSeparable.of_equiv_equiv e₁.symm e₂.symm (by
      ext x
      simpa [RingEquiv.eq_symm_apply] using (RingHom.ext_iff.mp he (e₁.symm x)).symm)⟩

end AlgEquiv

section CardAlgHom

variable {R S T : Type*} [CommRing S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K S] [Algebra K L]

/--
theorem `AlgHom.natCard_of_powerBasis` / 定理 `AlgHom.natCard_of_powerBasis`

English:
theorem AlgHom.natCard_of_powerBasis
  statement: (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
  proof: by
  classical
  rw [Nat.card_congr pb.liftEquiv']; rw [Nat.subtype_card _ (fun x => Multiset.mem_toFinset)]; rw [← pb.natDegree_minpoly]; rw [← natDegree_map (algebraMap K L)]; rw [h_splits.natDegree_eq_card_roots]; rw [Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)

中文:
定理 代数态射.natCard_of_powerBasis
  结论: (pb : PowerBasis K S) (h_sep : 是可分 K pb.gen)
  证明: by
  classical
  rw [Nat.card_congr pb.liftEquiv']; rw [Nat.subtype_card _ (fun x => Multiset.mem_toFinset)]; rw [← pb.natDegree_minpoly]; rw [← natDegree_map (algebraMap K L)]; rw [h_splits.natDegree_eq_card_roots]; rw [Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)

Depends on / 依赖: Multiset, Multiset.mem_toFinset, Multiset.toFinset_card_of_nodup, Nat.card_congr, Nat.subtype_card, algebraMap, card_congr, classical, h_sep, h_splits, h_splits.natDegree_eq_card_roots, liftEquiv, mem_toFinset, natDegree_eq_card_roots, natDegree_map, natDegree_minpoly, nodup_roots, pb.liftEquiv, pb.natDegree_minpoly, separable_map
-/
theorem AlgHom.natCard_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
    (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) :
    Nat.card (S ->ₐ[K] L) = pb.dim := by
  classical
  rw [Nat.card_congr pb.liftEquiv']; rw [Nat.subtype_card _ (fun x => Multiset.mem_toFinset)]; rw [← pb.natDegree_minpoly]; rw [← natDegree_map (algebraMap K L)]; rw [h_splits.natDegree_eq_card_roots]; rw [Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)

/--
theorem `AlgHom.card_of_powerBasis` / 定理 `AlgHom.card_of_powerBasis`

English:
theorem AlgHom.card_of_powerBasis
  statement: (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
  proof: by
  rw [Fintype.card_eq_nat_card]; rw [AlgHom.natCard_of_powerBasis pb h_sep h_splits]

中文:
定理 代数态射.card_of_powerBasis
  结论: (pb : PowerBasis K S) (h_sep : 是可分 K pb.gen)
  证明: by
  rw [Fintype.card_eq_nat_card]; rw [AlgHom.natCard_of_powerBasis pb h_sep h_splits]

Depends on / 依赖: AlgHom, AlgHom.natCard_of_powerBasis, Fintype, Fintype.card_eq_nat_card, card_eq_nat_card, h_sep, h_splits, natCard_of_powerBasis
-/
theorem AlgHom.card_of_powerBasis (pb : PowerBasis K S) (h_sep : IsSeparable K pb.gen)
    (h_splits : ((minpoly K pb.gen).map (algebraMap K L)).Splits) :
    @Fintype.card (S ->ₐ[K] L) (PowerBasis.AlgHom.fintype pb) = pb.dim := by
  rw [Fintype.card_eq_nat_card]; rw [AlgHom.natCard_of_powerBasis pb h_sep h_splits]

end CardAlgHom
