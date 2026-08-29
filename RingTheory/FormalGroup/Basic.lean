/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Formal group laws over commutative ring

Let `R` be a commutative ring, a one dimensional formal group law is a formal power series
`F(X,Y) ∈ R⟦X,Y⟧` such that
  * `F(X,Y) = X + Y + higher order terms`.
  * `F(F(X,Y),Z) = F(X,F(Y,Z))`.

Under this definition, we can prove that `F(X,0) = X` and `F(0,X) = X`. Moreover, there is a
unique power series `i(X)` such that `F(X, i(X)) = 0`, which is considered to be the inverse
of the formal group law `F(X,Y)`.

## Main definitions/lemmas

* `FormalGroup R`: definition of one dimensional formal group law over commutative ring `R`.

* Properties: `F(X,0) = X` and `F(0,X) = X`.

* Additive formal group laws `𝔾ₐ` and multiplicative formal group laws `𝔾ₘ`.

* `F.Point σ` taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent. We have the following typeclass:
- `AddMonoid (F.Point σ)`
when `F` is a commutative formal group law
- `AddCommMonoid (F.Point σ)`

## References
* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {σ τ : Type*}

noncomputable section

open MvPowerSeries Finsupp

name_power_vars X₀, X₁ over R

name_power_vars Y₀, Y₁, Y₂ over R

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`. -/
@[ext]
/--
Definition of `FormalGroup` / `FormalGroup` 的定义

English:
structure FormalGroup
  parameters: where
  axioms and operations (5):
    - toPowerSeries : MvPowerSeries (Fin 2) R
    - zero_constantCoeff : toPowerSeries.constantCoeff = 0
    - lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
    - lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
    - assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂] = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)

中文:
结构 FormalGroup
  参数: where
  公理与运算 (5 个):
    - toPowerSeries : MvPowerSeries (Fin 2) R
    - zero_constantCoeff : toPowerSeries.constantCoeff = 0
    - lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
    - lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
    - assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂] = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)
-/
structure FormalGroup where
  /-- The underlying power series $F(X, Y)$ in two variables. -/
  toPowerSeries : MvPowerSeries (Fin 2) R
  /-- The constant coefficient of the formal group law is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  /-- Associativity condition: $F(F(X, Y), Z) = F(X, F(Y, Z))$. -/
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)

/--
Instance `FormalGroup.coeToPowerSeries` / 实例 `FormalGroup.coeToPowerSeries`

English:
instance FormalGroup.coeToPowerSeries
  signature: : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R)
  body: ⟨toPowerSeries⟩

中文:
实例 FormalGroup.coeToPowerSeries
  签名: : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R)
  定义体: ⟨toPowerSeries⟩

Depends on / 依赖: toPowerSeries
-/
instance FormalGroup.coeToPowerSeries : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R) :=
  ⟨toPowerSeries⟩

/--
Definition of `FormalGroup.IsComm` / `FormalGroup.IsComm` 的定义

English:
class FormalGroup.IsComm
  parameters: (F : FormalGroup R)
  axioms and operations (1):
    - comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]

中文:
类 FormalGroup.IsComm
  参数: (F : FormalGroup R)
  公理与运算 (1 个):
    - comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]
-/
class FormalGroup.IsComm (F : FormalGroup R) : Prop where
  comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]

/--
lemma `FormalGroup.assoc'` / 引理 `FormalGroup.assoc'`

English:
lemma FormalGroup.assoc'
  statement: (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
  proof: by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.t

中文:
引理 FormalGroup.assoc'
  结论: (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
  证明: by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.t

Depends on / 依赖: F.toPowerSeries.subst, F.zero_constantCoeff, Fin.zero_eta, HasSubst, HasSubst.cons_subst_zero_left, HasSubst.cons_subst_zero_right, Nat.reduceAdd, Nat.succ_eq_add_one, cons_subst_zero_left, cons_subst_zero_right, fin_cases, hasSubst_of_constantCoeff_nilpotent, reduceAdd, subst_comp_subst_apply, succ_eq_add_one, toPowerSeries, zero_constantCoeff, zero_eta
-/
lemma FormalGroup.assoc' (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasSubst f₂) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![f₀, f₁], f₂] =
      F.toPowerSeries.subst ![f₀, F.toPowerSeries.subst ![f₁, f₂]] := by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.toPowerSeries.subst ![F.toPowerSeries.subst ![Y₀, Y₁], Y₂]).subst ![f₀, f₁, f₂] := by
      rw [subst_comp_subst_apply aux₁ this]
      congr! 2 with s
      fin_cases s
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst_X this]
      · simp [subst_X this]
    _ = _ := by
      rw [F.assoc]; rw [subst_comp_subst_apply aux₂ this]
      congr! 2 with s
      fin_cases s
      · simp [subst_X this]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst]

/--
lemma `FormalGroup.comm'` / 引理 `FormalGroup.comm'`

English:
lemma FormalGroup.comm'
  statement: (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
  proof: by
  nth_rw 1 [IsComm.comm]
  rw [subst_comp_subst_apply HasSubst.X_X <| hasSubst_of_constantCoeff_nilpotent (by simp [hf]; rw [hg])]
  congr! 2 with s
  fin_cases s <;> simp [subst]

中文:
引理 FormalGroup.comm'
  结论: (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
  证明: by
  nth_rw 1 [IsComm.comm]
  rw [subst_comp_subst_apply HasSubst.X_X <| hasSubst_of_constantCoeff_nilpotent (by simp [hf]; rw [hg])]
  congr! 2 with s
  fin_cases s <;> simp [subst]

Depends on / 依赖: HasSubst, HasSubst.X_X, IsComm, IsComm.comm, fin_cases, hasSubst_of_constantCoeff_nilpotent, nth_rw, subst_comp_subst_apply
-/
lemma FormalGroup.comm' (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) :
    F.toPowerSeries.subst ![f, g] = F.toPowerSeries.subst ![g, f] := by
  nth_rw 1 [IsComm.comm]
  rw [subst_comp_subst_apply HasSubst.X_X <| hasSubst_of_constantCoeff_nilpotent (by simp [hf]; rw [hg])]
  congr! 2 with s
  fin_cases s <;> simp [subst]

namespace FormalGroup

variable {σ : Type*} (F : FormalGroup R)

set_option linter.unusedVariables false in
/-- `F.Point σ` represents the mathematical space of points of a formal group $F$
taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent.

TODO: Mathematically, a 1-dimensional formal group law $F$ over a ring $R$ defines a group
structure on the elements of a complete local $R$-algebra (specifically, its maximal ideal)
via the substitution operation $x +_F y = F(x, y)$. -/
@[nolint unusedArguments]
/--
Definition of `Point` / `Point` 的定义

English:
definition Point
  signature: (F : FormalGroup R) (σ : Type*)
  body: {f : MvPowerSeries σ R // PowerSeries.HasSubst f}

中文:
定义 Point
  签名: (F : FormalGroup R) (σ : 类型)
  定义体: {f : MvPowerSeries σ R // PowerSeries.HasSubst f}

Depends on / 依赖: HasSubst, MvPowerSeries, PowerSeries, PowerSeries.HasSubst
-/
def Point (F : FormalGroup R) (σ : Type*) := {f : MvPowerSeries σ R // PowerSeries.HasSubst f}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (F.Point σ)
  body: ⟨F.toPowerSeries.subst ![x.val, y.val],
    IsNilpotent_subst (by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop])
      (F.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]

中文:
实例 :
  签名: Add (F.Point σ)
  定义体: ⟨F.toPowerSeries.subst ![x.val, y.val],
    IsNilpotent_subst (by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop])
      (F.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]

Depends on / 依赖: F.toPowerSeries.subst, toPowerSeries, x.val, y.val
-/
instance : Add (F.Point σ) where
  add x y := ⟨F.toPowerSeries.subst ![x.val, y.val],
    IsNilpotent_subst (by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop])
      (F.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: {x y : F.Point σ}
  statement: (x + y).val = F.toPowerSeries.subst ![x.val, y.val]
  proof: by
  rfl

中文:
引理 add_apply
  条件: {x y : F.Point σ}
  结论: (x + y).val = F.toPowerSeries.subst ![x.val, y.val]
  证明: by
  rfl
-/
lemma add_apply {x y : F.Point σ} : (x + y).val = F.toPowerSeries.subst ![x.val, y.val] := by
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (F.Point σ)
  body: ⟨0, PowerSeries.HasSubst.zero⟩

@[simp]

中文:
实例 :
  签名: Zero (F.Point σ)
  定义体: ⟨0, PowerSeries.HasSubst.zero⟩

@[simp]

Depends on / 依赖: HasSubst, PowerSeries, PowerSeries.HasSubst.zero
-/
instance : Zero (F.Point σ) where
  zero := ⟨0, PowerSeries.HasSubst.zero⟩

@[simp]
/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  statement: (0 : F.Point σ).val = (0 : MvPowerSeries σ R)
  proof: rfl

中文:
引理 zero_apply
  结论: (0 : F.Point σ).val = (0 : MvPowerSeries σ R)
  证明: rfl
-/
lemma zero_apply : (0 : F.Point σ).val = (0 : MvPowerSeries σ R) := rfl

/-- Additive formal group law `𝔾ₐ(X,Y) = X + Y`. -/
@[simps]
/--
Definition of `𝔾ₐ` / `𝔾ₐ` 的定义

English:
definition 𝔾ₐ
  signature: : FormalGroup R where
  body: X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ +

中文:
定义 𝔾ₐ
  签名: : FormalGroup R where
  定义体: X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ +
-/
def 𝔾ₐ : FormalGroup R where
  toPowerSeries := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_X aux₁, subst_add aux₂, subst_X aux₂]
    simp [subst_add .X_X, subst_X .X_X, add_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝔾ₐ (R := R)).IsComm
  body: by simp [subst_add .X_X, subst_X .X_X, add_comm]

中文:
实例 :
  签名: (𝔾ₐ (R := R)).IsComm
  定义体: by simp [subst_add .X_X, subst_X .X_X, add_comm]

Depends on / 依赖: IsComm
-/
instance : (𝔾ₐ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_X .X_X, add_comm]

/-- Multiplicative formal group law `𝔾ₘ(X,Y) = X + Y + XY`. -/
@[simps]
/--
Definition of `𝔾ₘ` / `𝔾ₘ` 的定义

English:
definition 𝔾ₘ
  signature: : FormalGroup R where
  body: X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  assoc :=

中文:
定义 𝔾ₘ
  签名: : FormalGroup R where
  定义体: X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  assoc :=
-/
def 𝔾ₘ : FormalGroup R where
  toPowerSeries := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : Nat) != 0)]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_mul aux₁, subst_X aux₁, subst_add aux₂, subst_mul aux₂,
      subst_X aux₂]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add .X_X, Fin.isValue, subst_X .X_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, subst_mul .X_X]
    ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝔾ₘ (R := R)).IsComm
  body: by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

中文:
实例 :
  签名: (𝔾ₘ (R := R)).IsComm
  定义体: by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

Depends on / 依赖: IsComm
-/
instance : (𝔾ₘ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

/-- Given an algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => 

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => 

Depends on / 依赖: MvPowerSeries
-/
def map (f : R ->+* S) : FormalGroup S where
  toPowerSeries := (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst .X_X, this, ← map_subst
      (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff), F.assoc,
      ← map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff)]

end FormalGroup

section

namespace FormalGroup

variable (F : FormalGroup R)

/--
Definition of `Xzero` / `Xzero` 的定义

English:
abbreviation Xzero
  signature: : PowerSeries R
  body: subst ![PowerSeries.X, 0] F.toPowerSeries

中文:
缩写 Xzero
  签名: : PowerSeries R
  定义体: subst ![PowerSeries.X, 0] F.toPowerSeries

Depends on / 依赖: F.toPowerSeries, PowerSeries, PowerSeries.X, toPowerSeries
-/
abbrev Xzero : PowerSeries R := subst ![PowerSeries.X, 0] F.toPowerSeries

/--
lemma `constantCoeff_Xzero` / 引理 `constantCoeff_Xzero`

English:
lemma constantCoeff_Xzero
  statement: F.Xzero.constantCoeff = 0
  proof: by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]

中文:
引理 constantCoeff_Xzero
  结论: F.Xzero.constantCoeff = 0
  证明: by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]

Depends on / 依赖: F.zero_constantCoeff, HasSubst, HasSubst.X_zero, MvPowerSeries, MvPowerSeries.constantCoeff_subst_eq_zero, PowerSeries, PowerSeries.X, PowerSeries.constantCoeff, X_zero, constantCoeff, constantCoeff_subst_eq_zero, zero_constantCoeff
-/
lemma constantCoeff_Xzero : F.Xzero.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]
/--
lemma `coeff_one_Xzero` / 引理 `coeff_one_Xzero`

English:
lemma coeff_one_Xzero
  statement: F.Xzero.coeff 1 = 1
  proof: by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

中文:
引理 coeff_one_Xzero
  结论: F.Xzero.coeff 1 = 1
  证明: by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

Depends on / 依赖: F.lin_coeff_X, HasSubst, HasSubst.X_zero, PowerSeries, PowerSeries.coeff, PowerSeries.coeff_X_pow, X_zero, coeff_X_pow, coeff_subst, finsum_eq_single, lin_coeff_X, single
-/
lemma coeff_one_Xzero : F.Xzero.coeff 1 = 1 := by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Xzero_subst_Xzero` / 引理 `Xzero_subst_Xzero`

English:
lemma Xzero_subst_Xzero
  statement: F.Xzero.subst F.Xzero = F.Xzero
  proof: by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSe

中文:
引理 Xzero_subst_Xzero
  结论: F.Xzero.subst F.Xzero = F.Xzero
  证明: by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSe

Depends on / 依赖: F.toPowerSeries, F.toPowerSeries.subst, F.zero_constantCoeff, HasSubst, HasSubst.X_zero, PowerSeries, PowerSeries.HasSubst, PowerSeries.HasSubst.of_constantCoeff_zero, PowerSeries.X, PowerSeries.constantCoeff, PowerSeries.subst, PowerSeries.subst_def, X_zero, constantCoeff, constantCoeff_subst_eq_zero, fin_cases, of_constantCoeff_zero, subst_comp_subst_apply, subst_def, this.const
-/
lemma Xzero_subst_Xzero : F.Xzero.subst F.Xzero = F.Xzero := by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSeries.X]; rw [constantCoeff_subst_eq_zero HasSubst.X_zero
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
      · exact HasSubst.X_zero
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 -> PowerSeries R) := by
        ext x : 1; fin_cases x <;> rfl
      simp [F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]

/--
lemma `Xzero_eq_X` / 引理 `Xzero_eq_X`

English:
lemma Xzero_eq_X
  statement: F.Xzero = PowerSeries.X
  proof: by
  have : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_s

中文:
引理 Xzero_eq_X
  结论: F.Xzero = PowerSeries.X
  证明: by
  have : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_s

Depends on / 依赖: F.Xzero, F.Xzero.coeff, F.Xzero.subst, F.Xzero.substInv.subst, F.Xzero.subst_substInv_left, F.constantCoeff_Xzero, HasSubst, Invertible, PowerSeries, PowerSeries.HasSubst, PowerSeries.HasSubst.of_constantCoeff_zero, PowerSeries.subst_X, PowerSeries.subst_comp_subst_apply, PowerSeries.subst_substInv_left, Xzero_subst_Xzero, coeff_one_Xzero, constantCoeff_Xzero, invertibleOne, of_constantCoeff_zero, substInv
-/
lemma Xzero_eq_X : F.Xzero = PowerSeries.X := by
  have : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀]; rw [PowerSeries.subst_substInv_left _
        F.constantCoeff_Xzero]; rw [PowerSeries.subst_X aux₀]; rw [Xzero]
    _ = _ := by
      rw [Xzero_subst_Xzero]; rw [F.Xzero.subst_substInv_left F.constantCoeff_Xzero]

/--
Definition of `zeroX` / `zeroX` 的定义

English:
abbreviation zeroX
  signature: : PowerSeries R
  body: subst ![0, PowerSeries.X] F.toPowerSeries

中文:
缩写 zeroX
  签名: : PowerSeries R
  定义体: subst ![0, PowerSeries.X] F.toPowerSeries

Depends on / 依赖: F.toPowerSeries, PowerSeries, PowerSeries.X, toPowerSeries
-/
abbrev zeroX : PowerSeries R := subst ![0, PowerSeries.X] F.toPowerSeries

/--
lemma `constantCoeff_zeroX` / 引理 `constantCoeff_zeroX`

English:
lemma constantCoeff_zeroX
  statement: F.zeroX.constantCoeff = 0
  proof: by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]

中文:
引理 constantCoeff_zeroX
  结论: F.zeroX.constantCoeff = 0
  证明: by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]

Depends on / 依赖: F.zero_constantCoeff, HasSubst, HasSubst.zero_X, MvPowerSeries, MvPowerSeries.constantCoeff_subst_eq_zero, PowerSeries, PowerSeries.X, PowerSeries.constantCoeff, constantCoeff, constantCoeff_subst_eq_zero, zero_X, zero_constantCoeff
-/
lemma constantCoeff_zeroX : F.zeroX.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]
/--
lemma `coeff_one_zeroX` / 引理 `coeff_one_zeroX`

English:
lemma coeff_one_zeroX
  statement: F.zeroX.coeff 1 = 1
  proof: by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

中文:
引理 coeff_one_zeroX
  结论: F.zeroX.coeff 1 = 1
  证明: by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

Depends on / 依赖: F.lin_coeff_Y, HasSubst, HasSubst.zero_X, PowerSeries, PowerSeries.coeff, PowerSeries.coeff_X_pow, coeff_X_pow, coeff_subst, finsum_eq_single, lin_coeff_Y, single, zero_X
-/
lemma coeff_one_zeroX : F.zeroX.coeff 1 = 1 := by
  rw [PowerSeries.coeff]; rw [coeff_subst]; rw [finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `zeroX_subst_zeroX` / 引理 `zeroX_subst_zeroX`

English:
lemma zeroX_subst_zeroX
  statement: F.zeroX.subst F.zeroX = F.zeroX
  proof: by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSe

中文:
引理 zeroX_subst_zeroX
  结论: F.zeroX.subst F.zeroX = F.zeroX
  证明: by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSe

Depends on / 依赖: F.toPowerSeries, F.toPowerSeries.subst, F.zero_constantCoeff, HasSubst, HasSubst.zero_X, PowerSeri, PowerSeries, PowerSeries.HasSubst, PowerSeries.HasSubst.of_constantCoeff_zero, PowerSeries.X, PowerSeries.constantCoeff, PowerSeries.subst, PowerSeries.subst_def, constantCoeff, constantCoeff_subst_eq_zero, fin_cases, of_constantCoeff_zero, subst_comp_subst_apply, subst_def, this.const
-/
lemma zeroX_subst_zeroX : F.zeroX.subst F.zeroX = F.zeroX := by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff]; rw [PowerSeries.X]; rw [constantCoeff_subst_eq_zero HasSubst.zero_X
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
      · exact HasSubst.zero_X
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 -> PowerSeries R) := by ext x : 1; fin_cases x <;> rfl
      simp [← F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]

/--
lemma `zeroX_eq_X` / 引理 `zeroX_eq_X`

English:
lemma zeroX_eq_X
  statement: F.zeroX = PowerSeries.X
  proof: by
  have : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_s

中文:
引理 zeroX_eq_X
  结论: F.zeroX = PowerSeries.X
  证明: by
  have : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_s

Depends on / 依赖: F.constantCoeff_zeroX, F.zeroX, F.zeroX.coeff, F.zeroX.subst, F.zeroX.substInv.subst, F.zeroX.subst_substInv_left, HasSubst, Invertible, PowerSeries, PowerSeries.HasSubst, PowerSeries.HasSubst.of_constantCoeff_zero, PowerSeries.subst_X, PowerSeries.subst_comp_subst_apply, PowerSeries.subst_substInv_left, coeff_one_zeroX, constantCoeff_zeroX, invertibleOne, of_constantCoeff_zero, substInv, subst_X
-/
lemma zeroX_eq_X : F.zeroX = PowerSeries.X := by
  have : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀]; rw [PowerSeries.subst_substInv_left _
        F.constantCoeff_zeroX]; rw [PowerSeries.subst_X aux₀]; rw [zeroX]
    _ = _ := by
      rw [zeroX_subst_zeroX]; rw [F.zeroX.subst_substInv_left F.constantCoeff_zeroX]

/--
theorem `add_zero` / 定理 `add_zero`

English:
theorem add_zero
  given: {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f)
  proof: by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X

中文:
定理 add_zero
  条件: {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f)
  证明: by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X

Depends on / 依赖: F.toPowerSeries.subst, HasSubst, HasSubst.X_zero, PowerSeries, PowerSeries.X, PowerSeries.subst, PowerSeries.subst_X, X_zero, Xzero_eq_X, fin_cases, hf.const, subst_X, subst_comp_subst_apply, toPowerSeries
-/
theorem add_zero {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![f, 0] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X_zero
    _ = _ := by
      simp [Xzero_eq_X, PowerSeries.subst_X hf]

/--
theorem `zero_add` / 定理 `zero_add`

English:
theorem zero_add
  given: {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f)
  proof: by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst

中文:
定理 zero_add
  条件: {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f)
  证明: by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst

Depends on / 依赖: F.toPowerSeries.subst, HasSubst, HasSubst.zero_X, PowerSeries, PowerSeries.X, PowerSeries.subst, PowerSeries.subst_X, fin_cases, hf.const, subst_X, subst_comp_subst_apply, toPowerSeries, zeroX_eq_X, zero_X
-/
theorem zero_add {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![0, f] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst]; rw [subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst.zero_X
    _ = _ := by
      simp [zeroX_eq_X, PowerSeries.subst_X hf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (F.Point σ)
  body: Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)
  nsmul := nsmulRec
add_assoc x y z := Subtype.ext F.assoc' x.prop y.prop z.prop

中文:
实例 :
  签名: AddMonoid (F.Point σ)
  定义体: Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)
  nsmul := nsmulRec
add_assoc x y z := Subtype.ext F.assoc' x.prop y.prop z.prop

Depends on / 依赖: Subtype, Subtype.ext, x.prop, zero_add
-/
instance : AddMonoid (F.Point σ) where
  zero_add x := Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)
  nsmul := nsmulRec
add_assoc x y z := Subtype.ext F.assoc' x.prop y.prop z.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsComm]
  signature: : AddCommMonoid (F.Point σ) where
  body: Subtype.ext F.comm' x.prop y.prop

中文:
实例 [F.IsComm]
  签名: : AddCommMonoid (F.Point σ) where
  定义体: Subtype.ext F.comm' x.prop y.prop

Depends on / 依赖: F.comm, Subtype, Subtype.ext, x.prop, y.prop
-/
instance [F.IsComm] : AddCommMonoid (F.Point σ) where
add_comm x y := Subtype.ext F.comm' x.prop y.prop

end FormalGroup

end
