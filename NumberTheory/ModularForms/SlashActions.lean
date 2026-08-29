/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.AdaptationNote

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a group on an a
additive monoid, parametrized by some index type. This is modeled on the slash action of
`GL (Fin 2) ℝ` on the space of modular forms.

## Notation

Scoped in the `ModularForm` namespace, this file defines

* `f ∣[k] A`: the `k`th slash action by `A` on `f`
-/

@[expose] public section


open Complex UpperHalfPlane ModularGroup

open scoped MatrixGroups

/--
Definition of `SlashAction` / `SlashAction` 的定义

English:
class SlashAction
  parameters: (β G α : Type*) [Monoid G] [AddMonoid α]
  axioms and operations (5):
    - map : β -> G -> α -> α
    - zero_slash : forall (k : β) (g : G), map k g 0 = 0
    - slash_one : forall (k : β) (a : α), map k 1 a = a
    - slash_mul : forall (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
    - add_slash : forall (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

中文:
类 SlashAction
  参数: (β G α : 类型) [Monoid G] [AddMonoid α]
  公理与运算 (5 个):
    - map : β -> G -> α -> α
    - zero_slash : 对任意 (k : β) (g : G), map k g 0 = 0
    - slash_one : 对任意 (k : β) (a : α), map k 1 a = a
    - slash_mul : 对任意 (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
    - add_slash : 对任意 (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b
-/
class SlashAction (β G α : Type*) [Monoid G] [AddMonoid α] where
  map : β -> G -> α -> α
  zero_slash : forall (k : β) (g : G), map k g 0 = 0
  slash_one : forall (k : β) (a : α), map k 1 a = a
  slash_mul : forall (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  add_slash : forall (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

open scoped ModularForm

@[simp]
/--
theorem `SlashAction.neg_slash` / 定理 `SlashAction.neg_slash`

English:
theorem SlashAction.neg_slash
  statement: {β G α : Type*} [Monoid G] [AddGroup α]
  proof: eq_neg_of_add_eq_zero_left by
    rw [← add_slash]; rw [neg_add_cancel]; rw [zero_slash]

中文:
定理 SlashAction.neg_slash
  结论: {β G α : 类型} [Monoid G] [AddGroup α]
  证明: eq_neg_of_add_eq_zero_left by
    rw [← add_slash]; rw [neg_add_cancel]; rw [zero_slash]

Depends on / 依赖: add_slash, eq_neg_of_add_eq_zero_left, neg_add_cancel, zero_slash
-/
theorem SlashAction.neg_slash {β G α : Type*} [Monoid G] [AddGroup α]
    [SlashAction β G α] (k : β) (g : G) (a : α) : (-a) ∣[k] g = -a ∣[k] g :=
eq_neg_of_add_eq_zero_left by
    rw [← add_slash]; rw [neg_add_cancel]; rw [zero_slash]

attribute [simp] SlashAction.zero_slash SlashAction.slash_one SlashAction.add_slash

/--
lemma `SlashAction.sum_slash` / 引理 `SlashAction.sum_slash`

English:
lemma SlashAction.sum_slash
  statement: {β G α ι : Type*} [Monoid G] [AddCommGroup α]
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH => simp [hi, IH]

中文:
引理 SlashAction.sum_slash
  结论: {β G α ι : 类型} [Monoid G] [AddCommGroup α]
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH => simp [hi, IH]
-/
@[simp] lemma SlashAction.sum_slash {β G α ι : Type*} [Monoid G] [AddCommGroup α]
    [SlashAction β G α] (k : β) (g : G) {a : ι -> α} {s : Finset ι} :
    (∑ i in s, a i) ∣[k] g = ∑ i in s, a i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH => simp [hi, IH]

/-- `SlashAction` induced by a monoid homomorphism. -/
@[instance_reducible]
/--
Definition of `monoidHomSlashAction` / `monoidHomSlashAction` 的定义

English:
definition monoidHomSlashAction
  signature: {β G H α : Type*} [Monoid G] [AddMonoid α] [Monoid H]
  body: SlashAction.map k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

@[simp]

中文:
定义 monoidHomSlashAction
  签名: {β G H α : 类型} [Monoid G] [AddMonoid α] [Monoid H]
  定义体: SlashAction.map k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

@[simp]

Depends on / 依赖: SlashAction, SlashAction.map
-/
def monoidHomSlashAction {β G H α : Type*} [Monoid G] [AddMonoid α] [Monoid H]
    [SlashAction β G α] (h : H ->* G) : SlashAction β H α where
  map k g := SlashAction.map k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

@[simp]
/--
lemma `SlashAction.slash_eq_zero_iff` / 引理 `SlashAction.slash_eq_zero_iff`

English:
lemma SlashAction.slash_eq_zero_iff
  statement: {β G α : Type*} [Group G] [AddGroup α] [SlashAction β G α]
  proof: by
  refine ⟨fun h => ?_, by simp +contextual⟩
  apply_fun (· ∣[k] g⁻¹) at h
  simpa [← SlashAction.slash_mul] using h

中文:
引理 SlashAction.slash_eq_zero_iff
  结论: {β G α : 类型} [Group G] [AddGroup α] [SlashAction β G α]
  证明: by
  refine ⟨fun h => ?_, by simp +contextual⟩
  apply_fun (· ∣[k] g⁻¹) at h
  simpa [← SlashAction.slash_mul] using h

Depends on / 依赖: SlashAction, SlashAction.slash_mul, apply_fun, contextual, slash_mul
-/
lemma SlashAction.slash_eq_zero_iff {β G α : Type*} [Group G] [AddGroup α] [SlashAction β G α]
    (k : β) (g : G) (a : α) : a ∣[k] g = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, by simp +contextual⟩
  apply_fun (· ∣[k] g⁻¹) at h
  simpa [← SlashAction.slash_mul] using h

namespace ModularForm

noncomputable section

variable {k : Int} (f : ℍ -> Complex)

section privateSlash

set_option backward.privateInPublic true in
/--
Definition of `privateSlash` / `privateSlash` 的定义

English:
definition privateSlash
  signature: (k : Int) (γ : GL (Fin 2) Real) (f : ℍ -> Complex) (x : ℍ)
  body: σ γ (f (γ • x)) * |γ.det.val| ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)

中文:
定义 privateSlash
  签名: (k : 整数) (γ : GL (Fin 2) 实数) (f : ℍ -> Complex) (x : ℍ)
  定义体: σ γ (f (γ • x)) * |γ.det.val| ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)
-/
private def privateSlash (k : Int) (γ : GL (Fin 2) Real) (f : ℍ -> Complex) (x : ℍ) : Complex :=
  σ γ (f (γ • x)) * |γ.det.val| ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)

-- Why is `noncomputable` flag needed here, when we're in a noncomputable section already?
-- temporary notation until the instance is built
local notation:100 f " ∣[" k "] " γ:100 => ModularForm.privateSlash k γ f

set_option backward.privateInPublic true in
/--
theorem `slash_mul` / 定理 `slash_mul`

English:
theorem slash_mul
  given: (k : Int) (A B : GL (Fin 2) Real) (f : ℍ -> Complex)
  proof: by
  ext1 τ
  calc σ (A * B) (f ((A * B) • τ)) * |(A * B).det.val| ^ (k - 1) * denom (A * B) τ ^ (-k)
  _ = σ B (σ A (f (A • B • τ))) * (|A.det.val| ^ (k - 1) * |B.det.val| ^ (k - 1)) *
      (((σ B) (denom A ↑(B • τ) ^ (-k))) * denom B τ ^ (-k)) := by
    rw [σ_mul_comm]; rw [σ_mul]; rw [denom_cocy

中文:
定理 slash_mul
  条件: (k : 整数) (A B : GL (Fin 2) 实数) (f : ℍ -> Complex)
  证明: by
  ext1 τ
  calc σ (A * B) (f ((A * B) • τ)) * |(A * B).det.val| ^ (k - 1) * denom (A * B) τ ^ (-k)
  _ = σ B (σ A (f (A • B • τ))) * (|A.det.val| ^ (k - 1) * |B.det.val| ^ (k - 1)) *
      (((σ B) (denom A ↑(B • τ) ^ (-k))) * denom B τ ^ (-k)) := by
    rw [σ_mul_comm]; rw [σ_mul]; rw [denom_cocy
-/
private theorem slash_mul (k : Int) (A B : GL (Fin 2) Real) (f : ℍ -> Complex) :
    f ∣[k] (A * B) = (f ∣[k] A) ∣[k] B := by
  ext1 τ
  calc σ (A * B) (f ((A * B) • τ)) * |(A * B).det.val| ^ (k - 1) * denom (A * B) τ ^ (-k)
  _ = σ B (σ A (f (A • B • τ))) * (|A.det.val| ^ (k - 1) * |B.det.val| ^ (k - 1)) *
      (((σ B) (denom A ↑(B • τ) ^ (-k))) * denom B τ ^ (-k)) := by
    rw [σ_mul_comm]; rw [σ_mul]; rw [denom_cocycle_σ]; rw [mul_zpow]; rw [mul_smul]; rw [map_mul]; rw [Units.val_mul]; rw [abs_mul]; rw [ofReal_mul]; rw [mul_zpow]; rw [map_zpow₀]
  _ = σ B (σ A (f (A • B • τ)) * |A.det.val| ^ (k - 1) * (denom A ↑(B • τ) ^ (-k)))
        * |B.det.val| ^ (k - 1) * denom B τ ^ (-k) := by
     rw [map_mul]; rw [map_zpow₀]; rw [map_mul]; rw [map_zpow₀]; rw [σ_ofReal]
     ring
  _ = ((f ∣[k] A) ∣[k] B) τ := rfl

set_option backward.privateInPublic true in
/--
theorem `add_slash` / 定理 `add_slash`

English:
theorem add_slash
  given: (k : Int) (A : GL (Fin 2) Real) (f g : ℍ -> Complex)
  proof: by
  ext1 τ
  simp [privateSlash, add_mul]

中文:
定理 add_slash
  条件: (k : 整数) (A : GL (Fin 2) 实数) (f g : ℍ -> Complex)
  证明: by
  ext1 τ
  simp [privateSlash, add_mul]
-/
private theorem add_slash (k : Int) (A : GL (Fin 2) Real) (f g : ℍ -> Complex) :
    (f + g) ∣[k] A = f ∣[k] A + g ∣[k] A := by
  ext1 τ
  simp [privateSlash, add_mul]

set_option backward.privateInPublic true in
/--
theorem `slash_one` / 定理 `slash_one`

English:
theorem slash_one
  given: (k : Int) (f : ℍ -> Complex)
  statement: f ∣[k] 1 = f
  proof: funext by simp [privateSlash, σ, denom]

中文:
定理 slash_one
  条件: (k : 整数) (f : ℍ -> Complex)
  结论: f ∣[k] 1 = f
  证明: funext by simp [privateSlash, σ, denom]
-/
private theorem slash_one (k : Int) (f : ℍ -> Complex) : f ∣[k] 1 = f :=
funext by simp [privateSlash, σ, denom]

set_option backward.privateInPublic true in
/--
theorem `zero_slash` / 定理 `zero_slash`

English:
theorem zero_slash
  given: (k : Int) (A : GL (Fin 2) Real)
  statement: (0 : ℍ -> Complex) ∣[k] A = 0
  proof: funext fun _ => by simp [privateSlash]

中文:
定理 zero_slash
  条件: (k : 整数) (A : GL (Fin 2) 实数)
  结论: (0 : ℍ -> Complex) ∣[k] A = 0
  证明: funext fun _ => by simp [privateSlash]
-/
private theorem zero_slash (k : Int) (A : GL (Fin 2) Real) : (0 : ℍ -> Complex) ∣[k] A = 0 :=
  funext fun _ => by simp [privateSlash]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SlashAction Int (GL (Fin 2) Real) (ℍ -> Complex)
  body: privateSlash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := add_slash

中文:
实例 :
  签名: SlashAction 整数 (GL (Fin 2) 实数) (ℍ -> Complex)
  定义体: privateSlash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := add_slash

Depends on / 依赖: privateSlash
-/
instance : SlashAction Int (GL (Fin 2) Real) (ℍ -> Complex) where
  map := privateSlash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := add_slash

end privateSlash

/--
theorem `slash_def` / 定理 `slash_def`

English:
theorem slash_def
  given: (g : GL (Fin 2) Real)
  proof: rfl

中文:
定理 slash_def
  条件: (g : GL (Fin 2) 实数)
  证明: rfl
-/
theorem slash_def (g : GL (Fin 2) Real) :
    f ∣[k] g = fun τ => σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl

/--
theorem `slash_apply` / 定理 `slash_apply`

English:
theorem slash_apply
  given: (g : GL (Fin 2) Real) (τ : ℍ)
  proof: rfl

中文:
定理 slash_apply
  条件: (g : GL (Fin 2) 实数) (τ : ℍ)
  证明: rfl
-/
theorem slash_apply (g : GL (Fin 2) Real) (τ : ℍ) :
    (f ∣[k] g) τ = σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl

/--
theorem `smul_slash` / 定理 `smul_slash`

English:
theorem smul_slash
  given: (k : Int) (A : GL (Fin 2) Real) (f : ℍ -> Complex) (c : Complex)
  proof: by
  ext τ : 1
  simp only [slash_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

中文:
定理 smul_slash
  条件: (k : 整数) (A : GL (Fin 2) 实数) (f : ℍ -> Complex) (c : Complex)
  证明: by
  ext τ : 1
  simp only [slash_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

Depends on / 依赖: Pi.smul_apply, map_mul, mul_assoc, slash_apply, smul_apply, smul_eq_mul
-/
theorem smul_slash (k : Int) (A : GL (Fin 2) Real) (f : ℍ -> Complex) (c : Complex) :
    (c • f) ∣[k] A = σ A c • f ∣[k] A := by
  ext τ : 1
  simp only [slash_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/--
Instance `SLAction` / 实例 `SLAction`

English:
instance SLAction
  signature: : SlashAction Int SL(2, Int) (ℍ -> Complex)
  body: monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL Real)

中文:
实例 SLAction
  签名: : SlashAction 整数 SL(2, 整数) (ℍ -> Complex)
  定义体: monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL Real)

Depends on / 依赖: Matrix, Matrix.SpecialLinearGroup.mapGL, SpecialLinearGroup, monoidHomSlashAction
-/
instance SLAction : SlashAction Int SL(2, Int) (ℍ -> Complex) :=
  monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL Real)

/--
theorem `SL_slash` / 定理 `SL_slash`

English:
theorem SL_slash
  given: (γ : SL(2, Int))
  statement: f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) Real)
  proof: rfl

中文:
定理 SL_slash
  条件: (γ : SL(2, 整数))
  结论: f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) 实数)
  证明: rfl
-/
theorem SL_slash (γ : SL(2, Int)) : f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) Real) :=
  rfl

/--
theorem `SL_slash_def` / 定理 `SL_slash_def`

English:
theorem SL_slash_def
  given: (γ : SL(2, Int))
  proof: by
  simp [SL_slash, slash_def, σ]

中文:
定理 SL_slash_def
  条件: (γ : SL(2, 整数))
  证明: by
  simp [SL_slash, slash_def, σ]

Depends on / 依赖: SL_slash, slash_def
-/
theorem SL_slash_def (γ : SL(2, Int)) :
    f ∣[k] γ = fun τ => f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]

/--
theorem `SL_slash_apply` / 定理 `SL_slash_apply`

English:
theorem SL_slash_apply
  given: (γ : SL(2, Int)) (τ : ℍ)
  proof: by
  simp [SL_slash, slash_def, σ]

@[simp]

中文:
定理 SL_slash_apply
  条件: (γ : SL(2, 整数)) (τ : ℍ)
  证明: by
  simp [SL_slash, slash_def, σ]

@[simp]

Depends on / 依赖: SL_slash, slash_def
-/
theorem SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) :
    (f ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]

@[simp]
/--
theorem `SL_smul_slash` / 定理 `SL_smul_slash`

English:
theorem SL_smul_slash
  statement: {α : Type*} [SMul α Complex] [IsScalarTower α Complex Complex]
  proof: by
  ext τ : 1
  simp [SL_slash_apply, Pi.smul_apply, smul_mul_assoc]

中文:
定理 SL_smul_slash
  结论: {α : 类型} [SMul α Complex] [IsScalarTower α Complex Complex]
  证明: by
  ext τ : 1
  simp [SL_slash_apply, Pi.smul_apply, smul_mul_assoc]

Depends on / 依赖: Pi.smul_apply, SL_slash_apply, smul_apply, smul_mul_assoc
-/
theorem SL_smul_slash {α : Type*} [SMul α Complex] [IsScalarTower α Complex Complex]
    (k : Int) (A : SL(2, Int)) (f : ℍ -> Complex) (c : α) :
    (c • f) ∣[k] A = c • f ∣[k] A := by
  ext τ : 1
  simp [SL_slash_apply, Pi.smul_apply, smul_mul_assoc]

/--
theorem `is_invariant_const` / 定理 `is_invariant_const`

English:
theorem is_invariant_const
  given: (A : SL(2, Int)) (x : Complex)
  proof: by
  funext
  simp [SL_slash, slash_def, σ, zero_lt_one]

中文:
定理 is_invariant_const
  条件: (A : SL(2, 整数)) (x : Complex)
  证明: by
  funext
  simp [SL_slash, slash_def, σ, zero_lt_one]

Depends on / 依赖: SL_slash, slash_def, zero_lt_one
-/
theorem is_invariant_const (A : SL(2, Int)) (x : Complex) :
    Function.const ℍ x ∣[(0 : Int)] A = Function.const ℍ x := by
  funext
  simp [SL_slash, slash_def, σ, zero_lt_one]

/--
theorem `is_invariant_one` / 定理 `is_invariant_one`

English:
theorem is_invariant_one
  given: (A : SL(2, Int))
  statement: (1 : ℍ -> Complex) ∣[(0 : Int)] A = (1 : ℍ -> Complex)
  proof: is_invariant_const _ _

中文:
定理 is_invariant_one
  条件: (A : SL(2, 整数))
  结论: (1 : ℍ -> Complex) ∣[(0 : 整数)] A = (1 : ℍ -> Complex)
  证明: is_invariant_const _ _

Depends on / 依赖: is_invariant_const
-/
theorem is_invariant_one (A : SL(2, Int)) : (1 : ℍ -> Complex) ∣[(0 : Int)] A = (1 : ℍ -> Complex) :=
  is_invariant_const _ _

/-- Variant of `is_invariant_one` with the left-hand side in simp normal form. -/
@[simp]
/--
theorem `is_invariant_one'` / 定理 `is_invariant_one'`

English:
theorem is_invariant_one'
  given: (A : SL(2, Int))
  statement: (1 : ℍ -> Complex) ∣[(0 : Int)] (A : GL (Fin 2) Real) = 1
  proof: by
  simpa using! is_invariant_one A

中文:
定理 is_invariant_one'
  条件: (A : SL(2, 整数))
  结论: (1 : ℍ -> Complex) ∣[(0 : 整数)] (A : GL (Fin 2) 实数) = 1
  证明: by
  simpa using! is_invariant_one A

Depends on / 依赖: is_invariant_one
-/
theorem is_invariant_one' (A : SL(2, Int)) : (1 : ℍ -> Complex) ∣[(0 : Int)] (A : GL (Fin 2) Real) = 1 := by
  simpa using! is_invariant_one A

/--
theorem `slash_action_eq'_iff` / 定理 `slash_action_eq'_iff`

English:
theorem slash_action_eq'_iff
  given: (k : Int) (f : ℍ -> Complex) (γ : SL(2, Int)) (z : ℍ)
  proof: by
  simp only [SL_slash_apply]
  convert! inv_mul_eq_iff_eq_mul₀ (G₀ := Complex) _ using 2
  · simp only [mul_comm (f _), denom, zpow_neg]
    rfl
  · exact zpow_ne_zero k (denom_ne_zero γ z)

中文:
定理 slash_action_eq'_iff
  条件: (k : 整数) (f : ℍ -> Complex) (γ : SL(2, 整数)) (z : ℍ)
  证明: by
  simp only [SL_slash_apply]
  convert! inv_mul_eq_iff_eq_mul₀ (G₀ := Complex) _ using 2
  · simp only [mul_comm (f _), denom, zpow_neg]
    rfl
  · exact zpow_ne_zero k (denom_ne_zero γ z)

Depends on / 依赖: SL_slash_apply, convert, denom_ne_zero, mul_comm, zpow_ne_zero, zpow_neg
-/
theorem slash_action_eq'_iff (k : Int) (f : ℍ -> Complex) (γ : SL(2, Int)) (z : ℍ) :
    (f ∣[k] γ) z = f z ↔ f (γ • z) = ((γ 1 0 : Complex) * z + (γ 1 1 : Complex)) ^ k * f z := by
  simp only [SL_slash_apply]
  convert! inv_mul_eq_iff_eq_mul₀ (G₀ := Complex) _ using 2
  · simp only [mul_comm (f _), denom, zpow_neg]
    rfl
  · exact zpow_ne_zero k (denom_ne_zero γ z)

/--
theorem `mul_slash` / 定理 `mul_slash`

English:
theorem mul_slash
  given: (k1 k2 : Int) (A : GL (Fin 2) Real) (f g : ℍ -> Complex)
  proof: by
  ext1 x
  simp only [slash_apply, Pi.mul_apply, Pi.smul_apply, real_smul, map_mul, neg_add,
    zpow_add₀ (denom_ne_zero _ x)]
  set d := (↑|A.det.val| : Complex)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
have : d != 0 := ofReal_ne_zero.mpr abs_ne_zero.mpr NeZero.ne _

中文:
定理 mul_slash
  条件: (k1 k2 : 整数) (A : GL (Fin 2) 实数) (f g : ℍ -> Complex)
  证明: by
  ext1 x
  simp only [slash_apply, Pi.mul_apply, Pi.smul_apply, real_smul, map_mul, neg_add,
    zpow_add₀ (denom_ne_zero _ x)]
  set d := (↑|A.det.val| : Complex)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
have : d != 0 := ofReal_ne_zero.mpr abs_ne_zero.mpr NeZero.ne _

Depends on / 依赖: A.det.val, NeZero, NeZero.ne, Pi.mul_apply, Pi.smul_apply, abs_ne_zero, abs_ne_zero.mpr, denom_ne_zero, map_mul, mul_apply, neg_add, ofReal_ne_zero, ofReal_ne_zero.mpr, real_smul, ring_nf, slash_apply, smul_apply
-/
theorem mul_slash (k1 k2 : Int) (A : GL (Fin 2) Real) (f g : ℍ -> Complex) :
    (f * g) ∣[k1 + k2] A = |(A.det : Real)| • (f ∣[k1] A * g ∣[k2] A) := by
  ext1 x
  simp only [slash_apply, Pi.mul_apply, Pi.smul_apply, real_smul, map_mul, neg_add,
    zpow_add₀ (denom_ne_zero _ x)]
  set d := (↑|A.det.val| : Complex)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
have : d != 0 := ofReal_ne_zero.mpr abs_ne_zero.mpr NeZero.ne _
    rw [← zpow_one_add₀ this]; rw [← zpow_add₀ this]
    ring_nf
  rw [h1]
  ring

/--
theorem `mul_slash_SL2` / 定理 `mul_slash_SL2`

English:
theorem mul_slash_SL2
  given: (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex)
  proof: by
  simp [SL_slash, mul_slash]

中文:
定理 mul_slash_SL2
  条件: (k1 k2 : 整数) (A : SL(2, 整数)) (f g : ℍ -> Complex)
  证明: by
  simp [SL_slash, mul_slash]

Depends on / 依赖: SL_slash, mul_slash
-/
theorem mul_slash_SL2 (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A := by
  simp [SL_slash, mul_slash]

/--
theorem `div_slash_SL2` / 定理 `div_slash_SL2`

English:
theorem div_slash_SL2
  given: (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex)
  proof: by
  ext τ
  simp [SL_slash_apply, zpow_sub₀ (denom_ne_zero A τ)]
  grind

中文:
定理 div_slash_SL2
  条件: (k1 k2 : 整数) (A : SL(2, 整数)) (f g : ℍ -> Complex)
  证明: by
  ext τ
  simp [SL_slash_apply, zpow_sub₀ (denom_ne_zero A τ)]
  grind

Depends on / 依赖: SL_slash_apply, denom_ne_zero
-/
theorem div_slash_SL2 (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex) :
    (f / g) ∣[k1 - k2] A = f ∣[k1] A / g ∣[k2] A := by
  ext τ
  simp [SL_slash_apply, zpow_sub₀ (denom_ne_zero A τ)]
  grind

open Finset

/--
lemma `prod_slash_sum_weights` / 引理 `prod_slash_sum_weights`

English:
lemma prod_slash_sum_weights
  statement: {ι : Type*} {k : ι -> Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Complex}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty, Matrix.GeneralLinearGroup.val_det_apply, card_empty,
      CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one]
    ext _
    simp [slash_apply]
  | insert i t hi IH =>
    rcas

中文:
引理 prod_slash_sum_weights
  结论: {ι : 类型} {k : ι -> 整数} {g : GL (Fin 2) 实数} {f : ι -> ℍ -> Complex}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty, Matrix.GeneralLinearGroup.val_det_apply, card_empty,
      CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one]
    ext _
    simp [slash_apply]
  | insert i t hi IH =>
    rcas

Depends on / 依赖: CharP.cast_eq_zero, Finset, Finset.induction_on, GeneralLinearGroup, Int.reduceNeg, Matrix, Matrix.GeneralLinearGroup.val_det_apply, Nat.cast_succ, add_sub_cancel_right, card_empty, card_insert_of_notMem, cast_eq_zero, cast_succ, classical, eq_empty_or_nonempty, induction_on, insert, mul_slash, mul_smul_comm, prod_empty
-/
lemma prod_slash_sum_weights {ι : Type*} {k : ι -> Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Complex}
    {s : Finset ι} :
    (∏ i in s, f i) ∣[∑ i in s, k i] g = |g.det.val| ^ (#s - 1 : Int) • (∏ i in s, f i ∣[k i] g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty, Matrix.GeneralLinearGroup.val_det_apply, card_empty,
      CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one]
    ext _
    simp [slash_apply]
  | insert i t hi IH =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simp
    simp only [prod_insert hi, card_insert_of_notMem hi, Nat.cast_succ, add_sub_cancel_right,
    show ∑ i in insert i t, k i = (k i) + ∑ i in t, k i by grind, mul_slash, IH, mul_smul_comm,
      ← mul_smul]
    congr 1
    nth_rw 2 [show (#t : Int) = 1 + (#t - 1) by grind]
    rw [zpow_add']; rw [zpow_one]
    left
    exact abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)

/--
lemma `prod_slash` / 引理 `prod_slash`

English:
lemma prod_slash
  statement: {ι : Type*} {k : Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Complex}
  proof: by
  have : k * (#s) = ∑ i in s, k := by
    rw [Finset.sum_const]; rw [nsmul_eq_mul']
  rw [this]
  exact prod_slash_sum_weights

@[deprecated prod_slash (since := "2026-01-22")]

中文:
引理 prod_slash
  结论: {ι : 类型} {k : 整数} {g : GL (Fin 2) 实数} {f : ι -> ℍ -> Complex}
  证明: by
  have : k * (#s) = ∑ i in s, k := by
    rw [Finset.sum_const]; rw [nsmul_eq_mul']
  rw [this]
  exact prod_slash_sum_weights

@[deprecated prod_slash (since := "2026-01-22")]

Depends on / 依赖: Finset, Finset.sum_const, nsmul_eq_mul, prod_slash_sum_weights, sum_const
-/
lemma prod_slash {ι : Type*} {k : Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Complex}
    {s : Finset ι} :
    (∏ i in s, f i) ∣[k * #s] g = |g.det.val| ^ (#s - 1 : Int) • (∏ i in s, f i ∣[k] g) := by
  have : k * (#s) = ∑ i in s, k := by
    rw [Finset.sum_const]; rw [nsmul_eq_mul']
  rw [this]
  exact prod_slash_sum_weights

@[deprecated prod_slash (since := "2026-01-22")]
/--
lemma `prod_fintype_slash` / 引理 `prod_fintype_slash`

English:
lemma prod_fintype_slash
  statement: {ι : Type*} [Fintype ι] [Nonempty ι] {k : Int} {g : GL (Fin 2) Real}
  proof: by
  have : 0 < Fintype.card ι := Fintype.card_pos
  simpa [← zpow_natCast, this] using ModularForm.prod_slash (s := (.univ : Finset ι))

中文:
引理 prod_fintype_slash
  结论: {ι : 类型} [Fintype ι] [Nonempty ι] {k : 整数} {g : GL (Fin 2) 实数}
  证明: by
  have : 0 < Fintype.card ι := Fintype.card_pos
  simpa [← zpow_natCast, this] using ModularForm.prod_slash (s := (.univ : Finset ι))

Depends on / 依赖: Finset, Fintype, Fintype.card, Fintype.card_pos, ModularForm, ModularForm.prod_slash, card_pos, prod_slash, zpow_natCast
-/
lemma prod_fintype_slash {ι : Type*} [Fintype ι] [Nonempty ι] {k : Int} {g : GL (Fin 2) Real}
    {f : ι -> ℍ -> Complex} : (∏ i, f i) ∣[k * Fintype.card ι] g =
      |g.det.val| ^ (Fintype.card ι - 1) • (∏ i, f i ∣[k] g) := by
  have : 0 < Fintype.card ι := Fintype.card_pos
  simpa [← zpow_natCast, this] using ModularForm.prod_slash (s := (.univ : Finset ι))

end

end ModularForm
