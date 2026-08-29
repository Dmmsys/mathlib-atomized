/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.IdealOperations
public import Mathlib.Order.Hom.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Solvable Lie algebras

Like groups, Lie algebras admit a natural concept of solvability. We define this here via the
derived series and prove some related results. We also define the radical of a Lie algebra and
prove that it is solvable when the Lie algebra is Noetherian.

## Main definitions

  * `LieAlgebra.derivedSeriesOfIdeal`
  * `LieAlgebra.derivedSeries`
  * `LieAlgebra.IsSolvable`
  * `LieAlgebra.isSolvableAdd`
  * `LieAlgebra.radical`
  * `LieAlgebra.radicalIsSolvable`
  * `LieAlgebra.derivedLengthOfIdeal`
  * `LieAlgebra.derivedLength`
  * `LieAlgebra.derivedAbelianOfIdeal`

## Tags

lie algebra, derived series, derived length, solvable, radical
-/

@[expose] public section


universe u v w w₁ w₂

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (I J : LieIdeal R L) {f : L' ->ₗ⁅R⁆ L}

namespace LieAlgebra

/--
Definition of `derivedSeriesOfIdeal` / `derivedSeriesOfIdeal` 的定义

English:
definition derivedSeriesOfIdeal
  signature: (k : Nat)
  body: (fun I => ⁅I, I⁆)^[k]

@[simp]

中文:
定义 derivedSeriesOfIdeal
  签名: (k : 自然数)
  定义体: (fun I => ⁅I, I⁆)^[k]

@[simp]
-/
def derivedSeriesOfIdeal (k : Nat) : LieIdeal R L -> LieIdeal R L :=
  (fun I => ⁅I, I⁆)^[k]

@[simp]
/--
theorem `derivedSeriesOfIdeal_zero` / 定理 `derivedSeriesOfIdeal_zero`

English:
theorem derivedSeriesOfIdeal_zero
  statement: derivedSeriesOfIdeal R L 0 I = I
  proof: rfl

@[simp]

中文:
定理 derivedSeriesOfIdeal_zero
  结论: derivedSeriesOfIdeal R L 0 I = I
  证明: rfl

@[simp]
-/
theorem derivedSeriesOfIdeal_zero : derivedSeriesOfIdeal R L 0 I = I :=
  rfl

@[simp]
/--
theorem `derivedSeriesOfIdeal_succ` / 定理 `derivedSeriesOfIdeal_succ`

English:
theorem derivedSeriesOfIdeal_succ
  given: (k : Nat)
  proof: Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

中文:
定理 derivedSeriesOfIdeal_succ
  条件: (k : 自然数)
  证明: Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply
-/
theorem derivedSeriesOfIdeal_succ (k : Nat) :
    derivedSeriesOfIdeal R L (k + 1) I =
      ⁅derivedSeriesOfIdeal R L k I, derivedSeriesOfIdeal R L k I⁆ :=
  Function.iterate_succ_apply' (fun I => ⁅I, I⁆) k I

/--
Definition of `derivedSeries` / `derivedSeries` 的定义

English:
abbreviation derivedSeries
  signature: (k : Nat)
  body: derivedSeriesOfIdeal R L k ⊤

中文:
缩写 derivedSeries
  签名: (k : 自然数)
  定义体: derivedSeriesOfIdeal R L k ⊤

Depends on / 依赖: derivedSeriesOfIdeal
-/
abbrev derivedSeries (k : Nat) : LieIdeal R L :=
  derivedSeriesOfIdeal R L k ⊤

/--
theorem `derivedSeries_def` / 定理 `derivedSeries_def`

English:
theorem derivedSeries_def
  given: (k : Nat)
  statement: derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤
  proof: rfl

中文:
定理 derivedSeries_def
  条件: (k : 自然数)
  结论: derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤
  证明: rfl
-/
theorem derivedSeries_def (k : Nat) : derivedSeries R L k = derivedSeriesOfIdeal R L k ⊤ :=
  rfl

/--
lemma `coe_derivedSeries_one_eq` / 引理 `coe_derivedSeries_one_eq`

English:
lemma coe_derivedSeries_one_eq
  proof: by
  ext z
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span']
  aesop

中文:
引理 coe_derivedSeries_one_eq
  证明: by
  ext z
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span']
  aesop

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, lieIdeal_oper_eq_linear_span, toLieSubalgebra_toSubmodule
-/
lemma coe_derivedSeries_one_eq :
    derivedSeries R L 1 = Submodule.span R {⁅x, y⁆ | (x : L) (y : L)} := by
  ext z
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span']
  aesop

variable {R L}

local notation "D" => derivedSeriesOfIdeal R L

/--
theorem `derivedSeriesOfIdeal_add` / 定理 `derivedSeriesOfIdeal_add`

English:
theorem derivedSeriesOfIdeal_add
  given: (k l : Nat)
  statement: D (k + l) I = D k (D l I)
  proof: by
  induction k with
  | zero => rw [Nat.zero_add, derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, ih]

@[gcongr, mono]

中文:
定理 derivedSeriesOfIdeal_add
  条件: (k l : 自然数)
  结论: D (k + l) I = D k (D l I)
  证明: by
  induction k with
  | zero => rw [Nat.zero_add, derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, ih]

@[gcongr, mono]

Depends on / 依赖: Nat.succ_add, Nat.zero_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, succ_add, zero_add
-/
theorem derivedSeriesOfIdeal_add (k l : Nat) : D (k + l) I = D k (D l I) := by
  induction k with
  | zero => rw [Nat.zero_add, derivedSeriesOfIdeal_zero]
  | succ k ih => rw [Nat.succ_add k l, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ, ih]

@[gcongr, mono]
/--
theorem `derivedSeriesOfIdeal_le` / 定理 `derivedSeriesOfIdeal_le`

English:
theorem derivedSeriesOfIdeal_le
  given: {I J : LieIdeal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k)
  proof: by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l <= k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, derivedSeriesOfIdeal_succ, derivedSeriesOfId

中文:
定理 derivedSeriesOfIdeal_le
  条件: {I J : LieIdeal R L} {k l : 自然数} (h₁ : I <= J) (h₂ : l <= k)
  证明: by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l <= k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, derivedSeriesOfIdeal_succ, derivedSeriesOfId

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_le_left, LieSubmodule.mono_lie, Nat.lt_succ_iff, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, generalizing, k.succ, le_iff_eq_or_lt, le_refl, le_trans, le_zero_iff, lie_le_left, lt_succ_iff, mono_lie
-/
theorem derivedSeriesOfIdeal_le {I J : LieIdeal R L} {k l : Nat} (h₁ : I <= J) (h₂ : l <= k) :
    D k I <= D l J := by
  induction k generalizing l with
  | zero => rw [le_zero_iff] at h₂; rw [h₂, derivedSeriesOfIdeal_zero]; exact h₁
  | succ k ih =>
    have h : l = k.succ ∨ l <= k := by rwa [le_iff_eq_or_lt, Nat.lt_succ_iff] at h₂
    rcases h with h | h
    · rw [h, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ]
      exact LieSubmodule.mono_lie (ih (le_refl k)) (ih (le_refl k))
    · rw [derivedSeriesOfIdeal_succ]; exact le_trans (LieSubmodule.lie_le_left _ _) (ih h)

/--
theorem `derivedSeriesOfIdeal_succ_le` / 定理 `derivedSeriesOfIdeal_succ_le`

English:
theorem derivedSeriesOfIdeal_succ_le
  given: (k : Nat)
  statement: D (k + 1) I <= D k I
  proof: derivedSeriesOfIdeal_le le_rfl k.le_succ

中文:
定理 derivedSeriesOfIdeal_succ_le
  条件: (k : 自然数)
  结论: D (k + 1) I <= D k I
  证明: derivedSeriesOfIdeal_le le_rfl k.le_succ

Depends on / 依赖: derivedSeriesOfIdeal_le, k.le_succ, le_rfl, le_succ
-/
theorem derivedSeriesOfIdeal_succ_le (k : Nat) : D (k + 1) I <= D k I :=
  derivedSeriesOfIdeal_le le_rfl k.le_succ

/--
theorem `derivedSeriesOfIdeal_le_self` / 定理 `derivedSeriesOfIdeal_le_self`

English:
theorem derivedSeriesOfIdeal_le_self
  given: (k : Nat)
  statement: D k I <= I
  proof: derivedSeriesOfIdeal_le le_rfl zero_le

中文:
定理 derivedSeriesOfIdeal_le_self
  条件: (k : 自然数)
  结论: D k I <= I
  证明: derivedSeriesOfIdeal_le le_rfl zero_le

Depends on / 依赖: derivedSeriesOfIdeal_le, le_rfl, zero_le
-/
theorem derivedSeriesOfIdeal_le_self (k : Nat) : D k I <= I :=
  derivedSeriesOfIdeal_le le_rfl zero_le

/--
theorem `derivedSeriesOfIdeal_mono` / 定理 `derivedSeriesOfIdeal_mono`

English:
theorem derivedSeriesOfIdeal_mono
  given: {I J : LieIdeal R L} (h : I <= J) (k : Nat)
  statement: D k I <= D k J
  proof: derivedSeriesOfIdeal_le h le_rfl

中文:
定理 derivedSeriesOfIdeal_mono
  条件: {I J : LieIdeal R L} (h : I <= J) (k : 自然数)
  结论: D k I <= D k J
  证明: derivedSeriesOfIdeal_le h le_rfl

Depends on / 依赖: derivedSeriesOfIdeal_le, le_rfl
-/
theorem derivedSeriesOfIdeal_mono {I J : LieIdeal R L} (h : I <= J) (k : Nat) : D k I <= D k J :=
  derivedSeriesOfIdeal_le h le_rfl

/--
theorem `derivedSeriesOfIdeal_antitone` / 定理 `derivedSeriesOfIdeal_antitone`

English:
theorem derivedSeriesOfIdeal_antitone
  given: {k l : Nat} (h : l <= k)
  statement: D k I <= D l I
  proof: derivedSeriesOfIdeal_le le_rfl h

中文:
定理 derivedSeriesOfIdeal_antitone
  条件: {k l : 自然数} (h : l <= k)
  结论: D k I <= D l I
  证明: derivedSeriesOfIdeal_le le_rfl h

Depends on / 依赖: derivedSeriesOfIdeal_le, le_rfl
-/
theorem derivedSeriesOfIdeal_antitone {k l : Nat} (h : l <= k) : D k I <= D l I :=
  derivedSeriesOfIdeal_le le_rfl h

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `derivedSeriesOfIdeal_add_le_add` / 定理 `derivedSeriesOfIdeal_add_le_add`

English:
theorem derivedSeriesOfIdeal_add_le_add
  given: (J : LieIdeal R L) (k l : Nat)
  proof: by
  let D₁ : LieIdeal R L ->o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : forall I J : LieIdeal R L, D₁ (I ⊔ J) <= D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [←

中文:
定理 derivedSeriesOfIdeal_add_le_add
  条件: (J : LieIdeal R L) (k l : 自然数)
  证明: by
  let D₁ : LieIdeal R L ->o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : forall I J : LieIdeal R L, D₁ (I ⊔ J) <= D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [←

Depends on / 依赖: LieIdeal, LieSubmodule, LieSubmodule.lie_le_left, LieSubmodule.lie_le_right, LieSubmodule.mono_lie, iterate_sup_le_sup_iff, le_sup_of_le_right, lie_le_left, lie_le_right, mono_lie, monotone
-/
theorem derivedSeriesOfIdeal_add_le_add (J : LieIdeal R L) (k l : Nat) :
    D (k + l) (I + J) <= D k I + D l J := by
  let D₁ : LieIdeal R L ->o LieIdeal R L :=
    { toFun := fun I => ⁅I, I⁆
      monotone' := fun I J h => LieSubmodule.mono_lie h h }
  have h₁ : forall I J : LieIdeal R L, D₁ (I ⊔ J) <= D₁ I ⊔ J := by
    simp [D₁, LieSubmodule.lie_le_right, LieSubmodule.lie_le_left, le_sup_of_le_right]
  rw [← D₁.iterate_sup_le_sup_iff] at h₁
  exact h₁ k l I J

/--
theorem `derivedSeries_of_bot_eq_bot` / 定理 `derivedSeries_of_bot_eq_bot`

English:
theorem derivedSeries_of_bot_eq_bot
  given: (k : Nat)
  statement: derivedSeriesOfIdeal R L k ⊥ = ⊥
  proof: by
  rw [eq_bot_iff]; exact derivedSeriesOfIdeal_le_self ⊥ k

中文:
定理 derivedSeries_of_bot_eq_bot
  条件: (k : 自然数)
  结论: derivedSeriesOfIdeal R L k ⊥ = ⊥
  证明: by
  rw [eq_bot_iff]; exact derivedSeriesOfIdeal_le_self ⊥ k

Depends on / 依赖: derivedSeriesOfIdeal_le_self, eq_bot_iff
-/
theorem derivedSeries_of_bot_eq_bot (k : Nat) : derivedSeriesOfIdeal R L k ⊥ = ⊥ := by
  rw [eq_bot_iff]; exact derivedSeriesOfIdeal_le_self ⊥ k

/--
theorem `abelian_iff_derived_one_eq_bot` / 定理 `abelian_iff_derived_one_eq_bot`

English:
theorem abelian_iff_derived_one_eq_bot
  statement: IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥
  proof: by
  rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

中文:
定理 abelian_iff_derived_one_eq_bot
  结论: IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥
  证明: by
  rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_abelian_iff_lie_self_eq_bot, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, lie_abelian_iff_lie_self_eq_bot
-/
theorem abelian_iff_derived_one_eq_bot : IsLieAbelian I ↔ derivedSeriesOfIdeal R L 1 I = ⊥ := by
  rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_zero]; rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot]

/--
theorem `abelian_iff_derived_succ_eq_bot` / 定理 `abelian_iff_derived_succ_eq_bot`

English:
theorem abelian_iff_derived_succ_eq_bot
  given: (I : LieIdeal R L) (k : Nat)
  proof: by
  rw [add_comm]; rw [derivedSeriesOfIdeal_add I 1 k]; rw [abelian_iff_derived_one_eq_bot]

中文:
定理 abelian_iff_derived_succ_eq_bot
  条件: (I : LieIdeal R L) (k : 自然数)
  证明: by
  rw [add_comm]; rw [derivedSeriesOfIdeal_add I 1 k]; rw [abelian_iff_derived_one_eq_bot]

Depends on / 依赖: abelian_iff_derived_one_eq_bot, add_comm, derivedSeriesOfIdeal_add
-/
theorem abelian_iff_derived_succ_eq_bot (I : LieIdeal R L) (k : Nat) :
    IsLieAbelian (derivedSeriesOfIdeal R L k I) ↔ derivedSeriesOfIdeal R L (k + 1) I = ⊥ := by
  rw [add_comm]; rw [derivedSeriesOfIdeal_add I 1 k]; rw [abelian_iff_derived_one_eq_bot]

open TensorProduct in
/--
theorem `derivedSeriesOfIdeal_baseChange` / 定理 `derivedSeriesOfIdeal_baseChange`

English:
theorem derivedSeriesOfIdeal_baseChange
  given: {A : Type*} [CommRing A] [Algebra R A] (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, ih, LieSubmodule.lie_baseChange]

中文:
定理 derivedSeriesOfIdeal_baseChange
  条件: {A : 类型} [交换环 A] [代数 R A] (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, ih, LieSubmodule.lie_baseChange]
-/
@[simp] theorem derivedSeriesOfIdeal_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : Nat) :
    derivedSeriesOfIdeal A (A otimes[R] L) k (I.baseChange A) =
      (derivedSeriesOfIdeal R L k I).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, ih, LieSubmodule.lie_baseChange]

open TensorProduct in
/--
theorem `derivedSeries_baseChange` / 定理 `derivedSeries_baseChange`

English:
theorem derivedSeries_baseChange
  given: {A : Type*} [CommRing A] [Algebra R A] (k : Nat)
  proof: by
  rw [derivedSeries_def]; rw [derivedSeries_def]; rw [← derivedSeriesOfIdeal_baseChange]; rw [LieSubmodule.baseChange_top]

中文:
定理 derivedSeries_baseChange
  条件: {A : 类型} [交换环 A] [代数 R A] (k : 自然数)
  证明: by
  rw [derivedSeries_def]; rw [derivedSeries_def]; rw [← derivedSeriesOfIdeal_baseChange]; rw [LieSubmodule.baseChange_top]
-/
@[simp] theorem derivedSeries_baseChange {A : Type*} [CommRing A] [Algebra R A] (k : Nat) :
    derivedSeries A (A otimes[R] L) k = (derivedSeries R L k).baseChange A := by
  rw [derivedSeries_def]; rw [derivedSeries_def]; rw [← derivedSeriesOfIdeal_baseChange]; rw [LieSubmodule.baseChange_top]

end LieAlgebra

namespace LieIdeal

open LieAlgebra

variable {R L}

/--
theorem `derivedSeries_eq_derivedSeriesOfIdeal_comap` / 定理 `derivedSeries_eq_derivedSeriesOfIdeal_comap`

English:
theorem derivedSeries_eq_derivedSeriesOfIdeal_comap
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simp only [derivedSeries_def, comap_incl_self, derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (derivedSeriesOfIdeal_le_self I k)
      (derivedSeriesOfIde

中文:
定理 derivedSeries_eq_derivedSeriesOfIdeal_comap
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simp only [derivedSeries_def, comap_incl_self, derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (derivedSeriesOfIdeal_le_self I k)
      (derivedSeriesOfIde

Depends on / 依赖: comap_bracket_incl_of_le, comap_incl_self, derivedSeriesOfIdeal_le_self, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, derivedSeries_def
-/
theorem derivedSeries_eq_derivedSeriesOfIdeal_comap (k : Nat) :
    derivedSeries R I k = (derivedSeriesOfIdeal R L k I).comap I.incl := by
  induction k with
  | zero => simp only [derivedSeries_def, comap_incl_self, derivedSeriesOfIdeal_zero]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢; rw [ih]
    exact comap_bracket_incl_of_le I (derivedSeriesOfIdeal_le_self I k)
      (derivedSeriesOfIdeal_le_self I k)

/--
theorem `derivedSeries_eq_derivedSeriesOfIdeal_map` / 定理 `derivedSeries_eq_derivedSeriesOfIdeal_map`

English:
theorem derivedSeries_eq_derivedSeriesOfIdeal_map
  given: (k : Nat)
  proof: by
  rw [derivedSeries_eq_derivedSeriesOfIdeal_comap]; rw [map_comap_incl]; rw [inf_eq_right]
  apply derivedSeriesOfIdeal_le_self

中文:
定理 derivedSeries_eq_derivedSeriesOfIdeal_map
  条件: (k : 自然数)
  证明: by
  rw [derivedSeries_eq_derivedSeriesOfIdeal_comap]; rw [map_comap_incl]; rw [inf_eq_right]
  apply derivedSeriesOfIdeal_le_self

Depends on / 依赖: derivedSeriesOfIdeal_le_self, derivedSeries_eq_derivedSeriesOfIdeal_comap, inf_eq_right, map_comap_incl
-/
theorem derivedSeries_eq_derivedSeriesOfIdeal_map (k : Nat) :
    (derivedSeries R I k).map I.incl = derivedSeriesOfIdeal R L k I := by
  rw [derivedSeries_eq_derivedSeriesOfIdeal_comap]; rw [map_comap_incl]; rw [inf_eq_right]
  apply derivedSeriesOfIdeal_le_self

/--
theorem `derivedSeries_eq_bot_iff` / 定理 `derivedSeries_eq_bot_iff`

English:
theorem derivedSeries_eq_bot_iff
  given: (k : Nat)
  proof: by
  rw [← derivedSeries_eq_derivedSeriesOfIdeal_map]; rw [map_eq_bot_iff]; rw [ker_incl]; rw [eq_bot_iff]

中文:
定理 derivedSeries_eq_bot_iff
  条件: (k : 自然数)
  证明: by
  rw [← derivedSeries_eq_derivedSeriesOfIdeal_map]; rw [map_eq_bot_iff]; rw [ker_incl]; rw [eq_bot_iff]

Depends on / 依赖: derivedSeries_eq_derivedSeriesOfIdeal_map, eq_bot_iff, ker_incl, map_eq_bot_iff
-/
theorem derivedSeries_eq_bot_iff (k : Nat) :
    derivedSeries R I k = ⊥ ↔ derivedSeriesOfIdeal R L k I = ⊥ := by
  rw [← derivedSeries_eq_derivedSeriesOfIdeal_map]; rw [map_eq_bot_iff]; rw [ker_incl]; rw [eq_bot_iff]

/--
theorem `derivedSeries_add_eq_bot` / 定理 `derivedSeries_add_eq_bot`

English:
theorem derivedSeries_add_eq_bot
  statement: {k l : Nat} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
  proof: by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) <= D k I + D l J := derivedSeriesOfIdeal_add_le_add I J k l
    _ <= ⊥ := by rw [hI, hJ]; simp

中文:
定理 derivedSeries_add_eq_bot
  结论: {k l : 自然数} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
  证明: by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) <= D k I + D l J := derivedSeriesOfIdeal_add_le_add I J k l
    _ <= ⊥ := by rw [hI, hJ]; simp

Depends on / 依赖: LieIdeal, LieIdeal.derivedSeries_eq_bot_iff, derivedSeriesOfIdeal, derivedSeriesOfIdeal_add_le_add, derivedSeries_eq_bot_iff, le_bot_iff
-/
theorem derivedSeries_add_eq_bot {k l : Nat} {I J : LieIdeal R L} (hI : derivedSeries R I k = ⊥)
    (hJ : derivedSeries R J l = ⊥) : derivedSeries R (I + J) (k + l) = ⊥ := by
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hI hJ ⊢
  rw [← le_bot_iff]
  let D := derivedSeriesOfIdeal R L; change D k I = ⊥ at hI; change D l J = ⊥ at hJ
  calc
    D (k + l) (I + J) <= D k I + D l J := derivedSeriesOfIdeal_add_le_add I J k l
    _ <= ⊥ := by rw [hI, hJ]; simp

/--
theorem `derivedSeries_map_le` / 定理 `derivedSeries_map_le`

English:
theorem derivedSeries_map_le
  given: (k : Nat)
  statement: (derivedSeries R L' k).map f <= derivedSeries R L k
  proof: by
  induction k with
  | zero => simp only [derivedSeries_def, derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)

中文:
定理 derivedSeries_map_le
  条件: (k : 自然数)
  结论: (derivedSeries R L' k).map f <= derivedSeries R L k
  证明: by
  induction k with
  | zero => simp only [derivedSeries_def, derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)

Depends on / 依赖: LieSubmodule, LieSubmodule.mono_lie, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, derivedSeries_def, le_top, le_trans, map_bracket_le, mono_lie
-/
theorem derivedSeries_map_le (k : Nat) : (derivedSeries R L' k).map f <= derivedSeries R L k := by
  induction k with
  | zero => simp only [derivedSeries_def, derivedSeriesOfIdeal_zero, le_top]
  | succ k ih =>
    simp only [derivedSeries_def, derivedSeriesOfIdeal_succ] at ih ⊢
    exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie ih ih)

/--
theorem `derivedSeries_map_eq` / 定理 `derivedSeries_map_eq`

English:
theorem derivedSeries_map_eq
  given: (k : Nat) (h : Function.Surjective f)
  proof: by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [derivedSeries_def, map_bracket_eq f h, ih, derivedSeriesOfIdeal_succ]

中文:
定理 derivedSeries_map_eq
  条件: (k : 自然数) (h : 函数.满射 f)
  证明: by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [derivedSeries_def, map_bracket_eq f h, ih, derivedSeriesOfIdeal_succ]

Depends on / 依赖: LieIdeal, derivedSeriesOfIdeal_succ, derivedSeries_def, f.idealRange_eq_map, f.idealRange_eq_top_of_surjective, idealRange_eq_map, idealRange_eq_top_of_surjective, map_bracket_eq
-/
theorem derivedSeries_map_eq (k : Nat) (h : Function.Surjective f) :
    (derivedSeries R L' k).map f = derivedSeries R L k := by
  induction k with
  | zero =>
    change (⊤ : LieIdeal R L').map f = ⊤
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  | succ k ih => simp only [derivedSeries_def, map_bracket_eq f h, ih, derivedSeriesOfIdeal_succ]

/--
theorem `derivedSeries_succ_eq_top_iff` / 定理 `derivedSeries_succ_eq_top_iff`

English:
theorem derivedSeries_succ_eq_top_iff
  given: (n : Nat)
  proof: by
  simp only [derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeriesOfIdeal_succ]
    refine ⟨fun h => ?_, fun h => by rwa [ih.mpr h]⟩
    rw [← ih]; rw [eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _

中文:
定理 derivedSeries_succ_eq_top_iff
  条件: (n : 自然数)
  证明: by
  simp only [derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeriesOfIdeal_succ]
    refine ⟨fun h => ?_, fun h => by rwa [ih.mpr h]⟩
    rw [← ih]; rw [eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_le_right, conv_lhs, derivedSeriesOfIdeal_succ, derivedSeries_def, eq_top_iff, ih.mpr, lie_le_right
-/
theorem derivedSeries_succ_eq_top_iff (n : Nat) :
    derivedSeries R L (n + 1) = ⊤ ↔ derivedSeries R L 1 = ⊤ := by
  simp only [derivedSeries_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [derivedSeriesOfIdeal_succ]
    refine ⟨fun h => ?_, fun h => by rwa [ih.mpr h]⟩
    rw [← ih]; rw [eq_top_iff]
    conv_lhs => rw [← h]
    exact LieSubmodule.lie_le_right _ _

/--
theorem `derivedSeries_eq_top` / 定理 `derivedSeries_eq_top`

English:
theorem derivedSeries_eq_top
  given: (n : Nat) (h : derivedSeries R L 1 = ⊤)
  proof: by
  cases n
  · rfl
  · rwa [derivedSeries_succ_eq_top_iff]

中文:
定理 derivedSeries_eq_top
  条件: (n : 自然数) (h : derivedSeries R L 1 = ⊤)
  证明: by
  cases n
  · rfl
  · rwa [derivedSeries_succ_eq_top_iff]

Depends on / 依赖: derivedSeries_succ_eq_top_iff
-/
theorem derivedSeries_eq_top (n : Nat) (h : derivedSeries R L 1 = ⊤) :
    derivedSeries R L n = ⊤ := by
  cases n
  · rfl
  · rwa [derivedSeries_succ_eq_top_iff]

/--
theorem `coe_derivedSeries_eq_int_aux` / 定理 `coe_derivedSeries_eq_int_aux`

English:
theorem coe_derivedSeries_eq_int_aux
  statement: (R₁ R₂ L : Type*) [CommRing R₁] [CommRing R₂]
  proof: derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a in I) (b in I)}
    (Submodule.span R₁ S : Set L) <= (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  

中文:
定理 coe_derivedSeries_eq_int_aux
  结论: (R₁ R₂ L : 类型) [交换环 R₁] [交换环 R₂]
  证明: derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a in I) (b in I)}
    (Submodule.span R₁ S : Set L) <= (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  
-/
private theorem coe_derivedSeries_eq_int_aux (R₁ R₂ L : Type*) [CommRing R₁] [CommRing R₂]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] (k : Nat)
    (ih : forall (x : L), x in derivedSeriesOfIdeal R₁ L k ⊤ ↔ x in derivedSeriesOfIdeal R₂ L k ⊤) :
    let I := derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a in I) (b in I)}
    (Submodule.span R₁ S : Set L) <= (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      refine Submodule.subset_span ⟨c • a, ?_, b, hb, rfl⟩
      rw [← ih] at ha ⊢
      exact Submodule.smul_mem _ _ ha

/--
theorem `coe_derivedSeries_eq_int` / 定理 `coe_derivedSeries_eq_int`

English:
theorem coe_derivedSeries_eq_int
  given: (k : Nat)
  proof: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]; rw [derivedSeries_def]; rw [derivedSeries_def]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw

中文:
定理 coe_derivedSeries_eq_int
  条件: (k : 自然数)
  证明: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]; rw [derivedSeries_def]; rw [derivedSeries_def]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, Set.ext_iff, SetLike, SetLike.mem_coe, coe_derivedSeries_eq_int_aux, coe_toSubmodule, derivedSeriesOfIdeal_succ, derivedSeries_def, ext_iff, le_antisymm, lieIdeal_oper_eq_linear_span, mem_coe, mem_toSubmodule
-/
theorem coe_derivedSeries_eq_int (k : Nat) :
    (derivedSeries R L k : Set L) = (derivedSeries Int L k : Set L) := by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]; rw [derivedSeries_def]; rw [derivedSeries_def]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [derivedSeriesOfIdeal_succ]; rw [derivedSeriesOfIdeal_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [ih]
    apply le_antisymm
    · exact coe_derivedSeries_eq_int_aux _ _ L k ih
    · simp

end LieIdeal

namespace LieAlgebra

/-- A Lie algebra is solvable if its derived series reaches 0 (in a finite number of steps). -/
@[mk_iff isSolvable_iff_int]
/--
Definition of `IsSolvable` / `IsSolvable` 的定义

English:
class IsSolvable
  parameters: : Prop where
  axioms and operations (2):
    - mk_int : :
    - solvable_int : exists k, derivedSeries Int L k = ⊥

中文:
类 是可解
  参数: : 命题 where
  公理与运算 (2 个):
    - mk_int : :
    - solvable_int : 存在 k, derivedSeries 整数 L k = ⊥
-/
class IsSolvable : Prop where
  mk_int ::
  solvable_int : exists k, derivedSeries Int L k = ⊥

/--
Instance `isSolvableBot` / 实例 `isSolvableBot`

English:
instance isSolvableBot
  signature: : IsSolvable (⊥ : LieIdeal R L)
  body: ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩

中文:
实例 isSolvableBot
  签名: : 是可解 (⊥ : LieIdeal R L)
  定义体: ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance isSolvableBot : IsSolvable (⊥ : LieIdeal R L) :=
  ⟨⟨0, Subsingleton.elim _ ⊥⟩⟩

/--
lemma `isSolvable_iff` / 引理 `isSolvable_iff`

English:
lemma isSolvable_iff
  statement: IsSolvable L ↔ exists k, derivedSeries R L k = ⊥
  proof: by
  simp [isSolvable_iff_int, SetLike.ext'_iff, LieIdeal.coe_derivedSeries_eq_int]

中文:
引理 isSolvable_iff
  结论: 是可解 L ↔ 存在 k, derivedSeries R L k = ⊥
  证明: by
  simp [isSolvable_iff_int, SetLike.ext'_iff, LieIdeal.coe_derivedSeries_eq_int]

Depends on / 依赖: LieIdeal, LieIdeal.coe_derivedSeries_eq_int, SetLike, SetLike.ext, _iff, coe_derivedSeries_eq_int, isSolvable_iff_int
-/
lemma isSolvable_iff : IsSolvable L ↔ exists k, derivedSeries R L k = ⊥ := by
  simp [isSolvable_iff_int, SetLike.ext'_iff, LieIdeal.coe_derivedSeries_eq_int]

/--
lemma `IsSolvable.solvable` / 引理 `IsSolvable.solvable`

English:
lemma IsSolvable.solvable
  given: [IsSolvable L]
  statement: exists k, derivedSeries R L k = ⊥
  proof: (isSolvable_iff R L).mp ‹_›

中文:
引理 是可解.solvable
  条件: [是可解 L]
  结论: 存在 k, derivedSeries R L k = ⊥
  证明: (isSolvable_iff R L).mp ‹_›

Depends on / 依赖: isSolvable_iff
-/
lemma IsSolvable.solvable [IsSolvable L] : exists k, derivedSeries R L k = ⊥ :=
  (isSolvable_iff R L).mp ‹_›

variable {R L} in
/--
lemma `IsSolvable.mk` / 引理 `IsSolvable.mk`

English:
lemma IsSolvable.mk
  given: {k : Nat} (h : derivedSeries R L k = ⊥)
  statement: IsSolvable L
  proof: (isSolvable_iff R L).mpr ⟨k, h⟩

中文:
引理 是可解.mk
  条件: {k : 自然数} (h : derivedSeries R L k = ⊥)
  结论: 是可解 L
  证明: (isSolvable_iff R L).mpr ⟨k, h⟩

Depends on / 依赖: isSolvable_iff
-/
lemma IsSolvable.mk {k : Nat} (h : derivedSeries R L k = ⊥) : IsSolvable L :=
  (isSolvable_iff R L).mpr ⟨k, h⟩

/--
Instance `isSolvableAdd` / 实例 `isSolvableAdd`

English:
instance isSolvableAdd
  signature: {I J : LieIdeal R L} [IsSolvable I] [IsSolvable J]
  body: by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  obtain ⟨l, hl⟩ := IsSolvable.solvable R J
  exact IsSolvable.mk (LieIdeal.derivedSeries_add_eq_bot hk hl)

中文:
实例 isSolvableAdd
  签名: {I J : LieIdeal R L} [是可解 I] [是可解 J]
  定义体: by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  obtain ⟨l, hl⟩ := IsSolvable.solvable R J
  exact IsSolvable.mk (LieIdeal.derivedSeries_add_eq_bot hk hl)

Depends on / 依赖: IsSolvable, IsSolvable.mk, IsSolvable.solvable, LieIdeal, LieIdeal.derivedSeries_add_eq_bot, derivedSeries_add_eq_bot, solvable
-/
instance isSolvableAdd {I J : LieIdeal R L} [IsSolvable I] [IsSolvable J] :
    IsSolvable (I + J) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R I
  obtain ⟨l, hl⟩ := IsSolvable.solvable R J
  exact IsSolvable.mk (LieIdeal.derivedSeries_add_eq_bot hk hl)

/--
theorem `derivedSeries_lt_top_of_solvable` / 定理 `derivedSeries_lt_top_of_solvable`

English:
theorem derivedSeries_lt_top_of_solvable
  given: [IsSolvable L] [Nontrivial L]
  proof: by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (R := R) (L := L)
  rw [lt_top_iff_ne_top]
  intro contra
  rw [LieIdeal.derivedSeries_eq_top n contra] at hn
  exact top_ne_bot hn

中文:
定理 derivedSeries_lt_top_of_solvable
  条件: [是可解 L] [非平凡 L]
  证明: by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (R := R) (L := L)
  rw [lt_top_iff_ne_top]
  intro contra
  rw [LieIdeal.derivedSeries_eq_top n contra] at hn
  exact top_ne_bot hn

Depends on / 依赖: IsSolvable, IsSolvable.solvable, LieIdeal, LieIdeal.derivedSeries_eq_top, contra, derivedSeries_eq_top, lt_top_iff_ne_top, solvable, top_ne_bot
-/
theorem derivedSeries_lt_top_of_solvable [IsSolvable L] [Nontrivial L] :
    derivedSeries R L 1 < ⊤ := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (R := R) (L := L)
  rw [lt_top_iff_ne_top]
  intro contra
  rw [LieIdeal.derivedSeries_eq_top n contra] at hn
  exact top_ne_bot hn

open TensorProduct in
instance {A : Type*} [CommRing A] [Algebra R A] [IsSolvable L] : IsSolvable (A otimes[R] L) := by
  obtain ⟨k, hk⟩ := IsSolvable.solvable R L
  rw [isSolvable_iff A]
  use k
  rw [derivedSeries_baseChange]; rw [hk]; rw [LieSubmodule.baseChange_bot]

open TensorProduct in
variable {A : Type*} [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] in
/--
theorem `isSolvable_tensorProduct_iff` / 定理 `isSolvable_tensorProduct_iff`

English:
theorem isSolvable_tensorProduct_iff
  statement: IsSolvable (A otimes[R] L) ↔ IsSolvable L
  proof: by
  refine ⟨?_, fun _ => inferInstance⟩
  rw [isSolvable_iff A]; rw [isSolvable_iff R]
  rintro ⟨k, h⟩
  use k
  rw [eq_bot_iff] at h ⊢
  intro x hx
  rw [derivedSeries_baseChange] at h
specialize h Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [LieSubmodule.mem_bot] at h ⊢
  rwa [Module.Faithfull

中文:
定理 isSolvable_tensorProduct_iff
  结论: 是可解 (A otimes[R] L) ↔ 是可解 L
  证明: by
  refine ⟨?_, fun _ => inferInstance⟩
  rw [isSolvable_iff A]; rw [isSolvable_iff R]
  rintro ⟨k, h⟩
  use k
  rw [eq_bot_iff] at h ⊢
  intro x hx
  rw [derivedSeries_baseChange] at h
specialize h Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [LieSubmodule.mem_bot] at h ⊢
  rwa [Module.Faithfull

Depends on / 依赖: FaithfullyFlat, LieSubmodule, LieSubmodule.mem_bot, Module, Module.FaithfullyFlat.one_tmul_eq_zero_iff, Submodule, Submodule.tmul_mem_baseChange_of_mem, derivedSeries_baseChange, eq_bot_iff, isSolvable_iff, mem_bot, one_tmul_eq_zero_iff, specialize, tmul_mem_baseChange_of_mem
-/
theorem isSolvable_tensorProduct_iff : IsSolvable (A otimes[R] L) ↔ IsSolvable L := by
  refine ⟨?_, fun _ => inferInstance⟩
  rw [isSolvable_iff A]; rw [isSolvable_iff R]
  rintro ⟨k, h⟩
  use k
  rw [eq_bot_iff] at h ⊢
  intro x hx
  rw [derivedSeries_baseChange] at h
specialize h Submodule.tmul_mem_baseChange_of_mem 1 hx
  rw [LieSubmodule.mem_bot] at h ⊢
  rwa [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h

end LieAlgebra

variable {R L}

namespace Function

open LieAlgebra

/--
theorem `Injective.lieAlgebra_isSolvable` / 定理 `Injective.lieAlgebra_isSolvable`

English:
theorem Injective.lieAlgebra_isSolvable
  given: [hL : IsSolvable L] (h : Injective f)
  proof: by
  rw [isSolvable_iff R] at hL ⊢
  apply hL.imp
  intro k hk
  apply LieIdeal.bot_of_map_eq_bot h; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le

中文:
定理 单射.lieAlgebra_isSolvable
  条件: [hL : 是可解 L] (h : 单射 f)
  证明: by
  rw [isSolvable_iff R] at hL ⊢
  apply hL.imp
  intro k hk
  apply LieIdeal.bot_of_map_eq_bot h; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le

Depends on / 依赖: LieIdeal, LieIdeal.bot_of_map_eq_bot, LieIdeal.derivedSeries_map_le, bot_of_map_eq_bot, derivedSeries_map_le, eq_bot_iff, hL.imp, isSolvable_iff
-/
theorem Injective.lieAlgebra_isSolvable [hL : IsSolvable L] (h : Injective f) :
    IsSolvable L' := by
  rw [isSolvable_iff R] at hL ⊢
  apply hL.imp
  intro k hk
  apply LieIdeal.bot_of_map_eq_bot h; rw [eq_bot_iff, ← hk]
  apply LieIdeal.derivedSeries_map_le

instance (A : LieIdeal R L) [IsSolvable L] : IsSolvable A :=
  A.incl_injective.lieAlgebra_isSolvable

/--
theorem `Surjective.lieAlgebra_isSolvable` / 定理 `Surjective.lieAlgebra_isSolvable`

English:
theorem Surjective.lieAlgebra_isSolvable
  given: [hL' : IsSolvable L'] (h : Surjective f)
  proof: by
  rw [isSolvable_iff R] at hL' ⊢
  apply hL'.imp
  intro k hk
  rw [← LieIdeal.derivedSeries_map_eq k h]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

中文:
定理 满射.lieAlgebra_isSolvable
  条件: [hL' : 是可解 L'] (h : 满射 f)
  证明: by
  rw [isSolvable_iff R] at hL' ⊢
  apply hL'.imp
  intro k hk
  rw [← LieIdeal.derivedSeries_map_eq k h]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

Depends on / 依赖: LieIdeal, LieIdeal.derivedSeries_map_eq, LieIdeal.map_eq_bot_iff, bot_le, derivedSeries_map_eq, isSolvable_iff, map_eq_bot_iff
-/
theorem Surjective.lieAlgebra_isSolvable [hL' : IsSolvable L'] (h : Surjective f) :
    IsSolvable L := by
  rw [isSolvable_iff R] at hL' ⊢
  apply hL'.imp
  intro k hk
  rw [← LieIdeal.derivedSeries_map_eq k h]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

end Function

/--
Instance `LieHom.isSolvable_range` / 实例 `LieHom.isSolvable_range`

English:
instance LieHom.isSolvable_range
  signature: (f : L' ->ₗ⁅R⁆ L) [LieAlgebra.IsSolvable L']
  body: f.surjective_rangeRestrict.lieAlgebra_isSolvable

中文:
实例 Lie态射.isSolvable_range
  签名: (f : L' ->ₗ⁅R⁆ L) [Lie代数.是可解 L']
  定义体: f.surjective_rangeRestrict.lieAlgebra_isSolvable

Depends on / 依赖: f.surjective_rangeRestrict.lieAlgebra_isSolvable, lieAlgebra_isSolvable, surjective_rangeRestrict
-/
instance LieHom.isSolvable_range (f : L' ->ₗ⁅R⁆ L) [LieAlgebra.IsSolvable L'] :
    LieAlgebra.IsSolvable f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isSolvable

namespace LieAlgebra

/--
theorem `solvable_iff_equiv_solvable` / 定理 `solvable_iff_equiv_solvable`

English:
theorem solvable_iff_equiv_solvable
  given: (e : L' ≃ₗ⁅R⁆ L)
  statement: IsSolvable L' ↔ IsSolvable L
  proof: by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isSolvable
  · exact e.injective.lieAlgebra_isSolvable

中文:
定理 solvable_iff_equiv_solvable
  条件: (e : L' ≃ₗ⁅R⁆ L)
  结论: 是可解 L' ↔ 是可解 L
  证明: by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isSolvable
  · exact e.injective.lieAlgebra_isSolvable

Depends on / 依赖: e.injective.lieAlgebra_isSolvable, e.symm.injective.lieAlgebra_isSolvable, injective, lieAlgebra_isSolvable
-/
theorem solvable_iff_equiv_solvable (e : L' ≃ₗ⁅R⁆ L) : IsSolvable L' ↔ IsSolvable L := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isSolvable
  · exact e.injective.lieAlgebra_isSolvable

/--
theorem `le_solvable_ideal_solvable` / 定理 `le_solvable_ideal_solvable`

English:
theorem le_solvable_ideal_solvable
  given: {I J : LieIdeal R L} (h₁ : I <= J) (_ : IsSolvable J)
  proof: (LieIdeal.inclusion_injective h₁).lieAlgebra_isSolvable

中文:
定理 le_solvable_ideal_solvable
  条件: {I J : LieIdeal R L} (h₁ : I <= J) (_ : 是可解 J)
  证明: (LieIdeal.inclusion_injective h₁).lieAlgebra_isSolvable

Depends on / 依赖: LieIdeal, LieIdeal.inclusion_injective, inclusion_injective, lieAlgebra_isSolvable
-/
theorem le_solvable_ideal_solvable {I J : LieIdeal R L} (h₁ : I <= J) (_ : IsSolvable J) :
    IsSolvable I :=
  (LieIdeal.inclusion_injective h₁).lieAlgebra_isSolvable

variable (R L)

instance (priority := 100) ofAbelianIsSolvable [IsLieAbelian L] : IsSolvable L := by
  use 1
  rw [← abelian_iff_derived_one_eq_bot]; rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv]
  infer_instance

/--
Definition of `radical` / `radical` 的定义

English:
definition radical
  body: sSup { I : LieIdeal R L | IsSolvable I }

中文:
定义 radical
  定义体: sSup { I : LieIdeal R L | IsSolvable I }

Depends on / 依赖: IsSolvable, LieIdeal
-/
def radical :=
  sSup { I : LieIdeal R L | IsSolvable I }

/--
Instance `radicalIsSolvable` / 实例 `radicalIsSolvable`

English:
instance radicalIsSolvable
  signature: [IsNoetherian R L]
  body: by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | IsSolvable I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact LieAlgebra.isSolvableBot R L
  · rw [Set.mem_ofPred_eq] at hI hJ ⊢
    apply Lie

中文:
实例 radicalIsSolvable
  签名: [是Noether R L]
  定义体: by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | IsSolvable I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact LieAlgebra.isSolvableBot R L
  · rw [Set.mem_ofPred_eq] at hI hJ ⊢
    apply Lie

Depends on / 依赖: CompleteLattice, CompleteLattice.isSupClosedCompact_iff_wellFoundedGT, IsSolvable, LieAlgebra, LieAlgebra.isSolvableAdd, LieAlgebra.isSolvableBot, LieIdeal, LieSubmodule, LieSubmodule.wellFoundedGT_of_noetherian, Set.mem_ofPred_eq, isSolvableAdd, isSolvableBot, isSupClosedCompact_iff_wellFoundedGT, mem_ofPred_eq, wellFoundedGT_of_noetherian
-/
instance radicalIsSolvable [IsNoetherian R L] : IsSolvable (radical R L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | IsSolvable I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact LieAlgebra.isSolvableBot R L
  · rw [Set.mem_ofPred_eq] at hI hJ ⊢
    apply LieAlgebra.isSolvableAdd R L

/--
theorem `LieIdeal.solvable_iff_le_radical` / 定理 `LieIdeal.solvable_iff_le_radical`

English:
theorem LieIdeal.solvable_iff_le_radical
  given: [IsNoetherian R L] (I : LieIdeal R L)
  proof: ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩

中文:
定理 LieIdeal.solvable_iff_le_radical
  条件: [是Noether R L] (I : LieIdeal R L)
  证明: ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩

Depends on / 依赖: le_sSup, le_solvable_ideal_solvable
-/
theorem LieIdeal.solvable_iff_le_radical [IsNoetherian R L] (I : LieIdeal R L) :
    IsSolvable I ↔ I <= radical R L :=
  ⟨fun h => le_sSup h, fun h => le_solvable_ideal_solvable h inferInstance⟩

/--
theorem `center_le_radical` / 定理 `center_le_radical`

English:
theorem center_le_radical
  statement: center R L <= radical R L
  proof: have h : IsSolvable (center R L) := inferInstance
  le_sSup h

中文:
定理 center_le_radical
  结论: center R L <= radical R L
  证明: have h : IsSolvable (center R L) := inferInstance
  le_sSup h

Depends on / 依赖: IsSolvable, center, le_sSup
-/
theorem center_le_radical : center R L <= radical R L :=
  have h : IsSolvable (center R L) := inferInstance
  le_sSup h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSolvable
  signature: L] : IsSolvable (⊤
  body: by
  rwa [solvable_iff_equiv_solvable LieSubalgebra.topEquiv]

中文:
实例 [是可解
  签名: L] : 是可解 (⊤
  定义体: by
  rwa [solvable_iff_equiv_solvable LieSubalgebra.topEquiv]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.topEquiv, solvable_iff_equiv_solvable, topEquiv
-/
instance [IsSolvable L] : IsSolvable (⊤ : LieSubalgebra R L) := by
  rwa [solvable_iff_equiv_solvable LieSubalgebra.topEquiv]

/--
lemma `radical_eq_top_of_isSolvable` / 引理 `radical_eq_top_of_isSolvable`

English:
lemma radical_eq_top_of_isSolvable
  given: [IsSolvable L]
  proof: by
  rw [eq_top_iff]
  have h : IsSolvable (⊤ : LieSubalgebra R L) := inferInstance
  exact le_sSup h

中文:
引理 radical_eq_top_of_isSolvable
  条件: [是可解 L]
  证明: by
  rw [eq_top_iff]
  have h : IsSolvable (⊤ : LieSubalgebra R L) := inferInstance
  exact le_sSup h
-/
@[simp] lemma radical_eq_top_of_isSolvable [IsSolvable L] :
    radical R L = ⊤ := by
  rw [eq_top_iff]
  have h : IsSolvable (⊤ : LieSubalgebra R L) := inferInstance
  exact le_sSup h

/--
Definition of `derivedLengthOfIdeal` / `derivedLengthOfIdeal` 的定义

English:
definition derivedLengthOfIdeal
  signature: (I : LieIdeal R L)
  body: sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }

中文:
定义 derivedLengthOfIdeal
  签名: (I : LieIdeal R L)
  定义体: sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }

Depends on / 依赖: derivedSeriesOfIdeal
-/
noncomputable def derivedLengthOfIdeal (I : LieIdeal R L) : Nat :=
  sInf { k | derivedSeriesOfIdeal R L k I = ⊥ }

/--
Definition of `derivedLength` / `derivedLength` 的定义

English:
abbreviation derivedLength
  signature: : Nat
  body: derivedLengthOfIdeal R L ⊤

中文:
缩写 derivedLength
  签名: : 自然数
  定义体: derivedLengthOfIdeal R L ⊤

Depends on / 依赖: derivedLengthOfIdeal
-/
noncomputable abbrev derivedLength : Nat :=
  derivedLengthOfIdeal R L ⊤

/--
theorem `derivedSeries_of_derivedLength_succ` / 定理 `derivedSeries_of_derivedLength_succ`

English:
theorem derivedSeries_of_derivedLength_succ
  given: (I : LieIdeal R L) (k : Nat)
  proof: by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derivedSeriesOfIdeal R L k₂ I <= ⊥ by exact eq_bot_iff.m

中文:
定理 derivedSeries_of_derivedLength_succ
  条件: (I : LieIdeal R L) (k : 自然数)
  证明: by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derivedSeriesOfIdeal R L k₂ I <= ⊥ by exact eq_bot_iff.m

Depends on / 依赖: Nat.sInf_upward_closed_eq_succ_iff, abelian_iff_derived_succ_eq_bot, derivedSeriesOfIdeal, derivedSeriesOfIdeal_antitone, eq_bot_iff, eq_bot_iff.mpr, sInf_upward_closed_eq_succ_iff
-/
theorem derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : Nat) :
    derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (derivedSeriesOfIdeal R L k I) ∧ derivedSeriesOfIdeal R L k I != ⊥ := by
  rw [abelian_iff_derived_succ_eq_bot]
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs : forall k₁ k₂ : Nat, k₁ <= k₂ -> k₁ in s -> k₂ in s := by
    intro k₁ k₂ h₁₂ h₁
    suffices derivedSeriesOfIdeal R L k₂ I <= ⊥ by exact eq_bot_iff.mpr this
    change derivedSeriesOfIdeal R L k₁ I = ⊥ at h₁; rw [← h₁]
    exact derivedSeriesOfIdeal_antitone I h₁₂
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

/--
theorem `derivedLength_eq_derivedLengthOfIdeal` / 定理 `derivedLength_eq_derivedLengthOfIdeal`

English:
theorem derivedLength_eq_derivedLengthOfIdeal
  given: (I : LieIdeal R L)
  proof: by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s₁ = sInf s₂
  congr; ext k; exact I.derivedSeries_eq_bot_iff k

中文:
定理 derivedLength_eq_derivedLengthOfIdeal
  条件: (I : LieIdeal R L)
  证明: by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s₁ = sInf s₂
  congr; ext k; exact I.derivedSeries_eq_bot_iff k

Depends on / 依赖: I.derivedSeries_eq_bot_iff, derivedSeries, derivedSeriesOfIdeal, derivedSeries_eq_bot_iff
-/
theorem derivedLength_eq_derivedLengthOfIdeal (I : LieIdeal R L) :
    derivedLength R I = derivedLengthOfIdeal R L I := by
  let s₁ := { k | derivedSeries R I k = ⊥ }
  let s₂ := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s₁ = sInf s₂
  congr; ext k; exact I.derivedSeries_eq_bot_iff k

variable {R L}

/--
Definition of `derivedAbelianOfIdeal` / `derivedAbelianOfIdeal` 的定义

English:
definition derivedAbelianOfIdeal
  signature: (I : LieIdeal R L)
  body: match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I

中文:
定义 derivedAbelianOfIdeal
  签名: (I : LieIdeal R L)
  定义体: match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I

Depends on / 依赖: derivedLengthOfIdeal, derivedSeriesOfIdeal
-/
noncomputable def derivedAbelianOfIdeal (I : LieIdeal R L) : LieIdeal R L :=
  match derivedLengthOfIdeal R L I with
  | 0 => ⊥
  | k + 1 => derivedSeriesOfIdeal R L k I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique {x // x in (⊥ : LieIdeal R L)}
  body: inferInstanceAs Unique {x // x in (⊥ : Submodule R L)}

中文:
实例 :
  签名: 唯一 {x // x in (⊥ : LieIdeal R L)}
  定义体: inferInstanceAs Unique {x // x in (⊥ : Submodule R L)}

Depends on / 依赖: Submodule, Unique
-/
instance : Unique {x // x in (⊥ : LieIdeal R L)} :=
inferInstanceAs Unique {x // x in (⊥ : Submodule R L)}

/--
theorem `abelian_derivedAbelianOfIdeal` / 定理 `abelian_derivedAbelianOfIdeal`

English:
theorem abelian_derivedAbelianOfIdeal
  given: (I : LieIdeal R L)
  proof: by
  dsimp +instances only [derivedAbelianOfIdeal]
  rcases h : derivedLengthOfIdeal R L I with - | k
  · dsimp; infer_instance
  · rw [derivedSeries_of_derivedLength_succ] at h; exact h.1

中文:
定理 abelian_derivedAbelianOfIdeal
  条件: (I : LieIdeal R L)
  证明: by
  dsimp +instances only [derivedAbelianOfIdeal]
  rcases h : derivedLengthOfIdeal R L I with - | k
  · dsimp; infer_instance
  · rw [derivedSeries_of_derivedLength_succ] at h; exact h.1

Depends on / 依赖: derivedAbelianOfIdeal, derivedLengthOfIdeal, derivedSeries_of_derivedLength_succ, infer_instance, instances
-/
theorem abelian_derivedAbelianOfIdeal (I : LieIdeal R L) :
    IsLieAbelian (derivedAbelianOfIdeal I) := by
  dsimp +instances only [derivedAbelianOfIdeal]
  rcases h : derivedLengthOfIdeal R L I with - | k
  · dsimp; infer_instance
  · rw [derivedSeries_of_derivedLength_succ] at h; exact h.1

/--
theorem `derivedLength_zero` / 定理 `derivedLength_zero`

English:
theorem derivedLength_zero
  given: (I : LieIdeal R L) [IsSolvable I]
  proof: by
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = 0 ↔ _
  have hne : s.Nonempty :=
    have ⟨k, hk⟩ := IsSolvable.solvable R I
    ⟨k, by rwa [derivedSeries_def, LieIdeal.derivedSeries_eq_bot_iff] at hk⟩
  simp [s, hne.ne_empty]

中文:
定理 derivedLength_zero
  条件: (I : LieIdeal R L) [是可解 I]
  证明: by
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = 0 ↔ _
  have hne : s.Nonempty :=
    have ⟨k, hk⟩ := IsSolvable.solvable R I
    ⟨k, by rwa [derivedSeries_def, LieIdeal.derivedSeries_eq_bot_iff] at hk⟩
  simp [s, hne.ne_empty]

Depends on / 依赖: IsSolvable, IsSolvable.solvable, LieIdeal, LieIdeal.derivedSeries_eq_bot_iff, Nonempty, derivedSeriesOfIdeal, derivedSeries_def, derivedSeries_eq_bot_iff, hne.ne_empty, ne_empty, s.Nonempty, solvable
-/
theorem derivedLength_zero (I : LieIdeal R L) [IsSolvable I] :
    derivedLengthOfIdeal R L I = 0 ↔ I = ⊥ := by
  let s := { k | derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = 0 ↔ _
  have hne : s.Nonempty :=
    have ⟨k, hk⟩ := IsSolvable.solvable R I
    ⟨k, by rwa [derivedSeries_def, LieIdeal.derivedSeries_eq_bot_iff] at hk⟩
  simp [s, hne.ne_empty]

/--
theorem `abelian_of_solvable_ideal_eq_bot_iff` / 定理 `abelian_of_solvable_ideal_eq_bot_iff`

English:
theorem abelian_of_solvable_ideal_eq_bot_iff
  given: (I : LieIdeal R L) [h : IsSolvable I]
  proof: by
  dsimp only [derivedAbelianOfIdeal]
  split
  · simp_all only [derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I != ⊥ := by rintro rfl; apply h₂; apply derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

中文:
定理 abelian_of_solvable_ideal_eq_bot_iff
  条件: (I : LieIdeal R L) [h : 是可解 I]
  证明: by
  dsimp only [derivedAbelianOfIdeal]
  split
  · simp_all only [derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I != ⊥ := by rintro rfl; apply h₂; apply derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

Depends on / 依赖: derivedAbelianOfIdeal, derivedLength_zero, derivedSeries_of_bot_eq_bot, derivedSeries_of_derivedLength_succ, rename_i
-/
theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I] :
    derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ := by
  dsimp only [derivedAbelianOfIdeal]
  split
  · simp_all only [derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I != ⊥ := by rintro rfl; apply h₂; apply derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

end LieAlgebra
