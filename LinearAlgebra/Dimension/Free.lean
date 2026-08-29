/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.SetTheory.Cardinal.Finsupp

/-!
# Rank of free modules

## Main result
- `Module.nonempty_linearEquiv_iff_lift_rank_eq`:
  Two free modules are isomorphic iff they have the same dimension.
- `Module.finBasis`:
  An arbitrary basis of a finite free module indexed by `Fin n` given `finrank R M = n`.

-/

@[expose] public section


noncomputable section

universe u v v' w

open Cardinal Basis Submodule Function Set Module

section Tower

variable (F : Type u) (K : Type v) (A : Type w)
variable [Semiring F] [Semiring K] [AddCommMonoid A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]
variable [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]

/--
theorem `lift_rank_mul_lift_rank` / 定理 `lift_rank_mul_lift_rank`

English:
theorem lift_rank_mul_lift_rank
  proof: by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id]; rw [← b.mk_eq_rank]; rw [← (Module.rank K A).lift_id]; rw [← c.mk_eq_rank]; rw [← lift_umax.{w]; rw [v}]; rw [← (b.smulTower c).mk_eq_rank]; rw [mk_prod]; rw [lift_mul]; rw [lift_lift

中文:
定理 lift_rank_mul_lift_rank
  证明: by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id]; rw [← b.mk_eq_rank]; rw [← (Module.rank K A).lift_id]; rw [← c.mk_eq_rank]; rw [← lift_umax.{w]; rw [v}]; rw [← (b.smulTower c).mk_eq_rank]; rw [mk_prod]; rw [lift_mul]; rw [lift_lift

Depends on / 依赖: Module, Module.Free.chooseBasis, Module.rank, b.mk_eq_rank, b.smulTower, c.mk_eq_rank, chooseBasis, lift_id, lift_lift, lift_mul, lift_umax, mk_eq_rank, mk_prod, smulTower
-/
theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) := by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id]; rw [← b.mk_eq_rank]; rw [← (Module.rank K A).lift_id]; rw [← c.mk_eq_rank]; rw [← lift_umax.{w]; rw [v}]; rw [← (b.smulTower c).mk_eq_rank]; rw [mk_prod]; rw [lift_mul]; rw [lift_lift]; rw [lift_lift]; rw [lift_lift]; rw [lift_lift]; rw [lift_umax.{v]; rw [w}]

/-- Tower law: if `A` is a `K`-module and `K` is an extension of `F` then
$\operatorname{rank}_F(A) = \operatorname{rank}_F(K) * \operatorname{rank}_K(A)$.

This is a simpler version of `lift_rank_mul_lift_rank` with `K` and `A` in the same universe. -/
@[stacks 09G9]
/--
theorem `rank_mul_rank` / 定理 `rank_mul_rank`

English:
theorem rank_mul_rank
  statement: (A : Type v) [AddCommMonoid A]
  proof: by
  convert! lift_rank_mul_lift_rank F K A <;> rw [lift_id]

中文:
定理 rank_mul_rank
  结论: (A : 类型v) [AddCommMonoid A]
  证明: by
  convert! lift_rank_mul_lift_rank F K A <;> rw [lift_id]

Depends on / 依赖: convert, lift_id, lift_rank_mul_lift_rank
-/
theorem rank_mul_rank (A : Type v) [AddCommMonoid A]
    [Module K A] [Module F A] [IsScalarTower F K A] [Module.Free K A] :
    Module.rank F K * Module.rank K A = Module.rank F A := by
  convert! lift_rank_mul_lift_rank F K A <;> rw [lift_id]

/--
theorem `Module.finrank_mul_finrank` / 定理 `Module.finrank_mul_finrank`

English:
theorem Module.finrank_mul_finrank
  statement: finrank F K * finrank K A = finrank F A
  proof: by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (Module.rank F K)]; rw [← toNat_lift.{v} (Module.rank K A)]; rw [← toNat_mul]; rw [lift_rank_mul_lift_rank]; rw [toNat_lift]

中文:
定理 Module.finrank_mul_finrank
  结论: finrank F K * finrank K A = finrank F A
  证明: by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (Module.rank F K)]; rw [← toNat_lift.{v} (Module.rank K A)]; rw [← toNat_mul]; rw [lift_rank_mul_lift_rank]; rw [toNat_lift]

Depends on / 依赖: Module, Module.rank, finrank, lift_rank_mul_lift_rank, simp_rw, toNat_lift, toNat_mul
-/
theorem Module.finrank_mul_finrank : finrank F K * finrank K A = finrank F A := by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (Module.rank F K)]; rw [← toNat_lift.{v} (Module.rank K A)]; rw [← toNat_mul]; rw [lift_rank_mul_lift_rank]; rw [toNat_lift]

/--
theorem `Module.finrank_dvd_finrank_left` / 定理 `Module.finrank_dvd_finrank_left`

English:
theorem Module.finrank_dvd_finrank_left
  proof: Dvd.intro_left (finrank F K) (finrank_mul_finrank ..)

中文:
定理 Module.finrank_dvd_finrank_left
  证明: Dvd.intro_left (finrank F K) (finrank_mul_finrank ..)

Depends on / 依赖: Dvd.intro_left, finrank, finrank_mul_finrank, hasFiniteIntegral, hg.hasFiniteIntegral.mono, intro_left
-/
theorem Module.finrank_dvd_finrank_left :
    Module.finrank K A ∣ Module.finrank F A :=
  Dvd.intro_left (finrank F K) (finrank_mul_finrank ..)

/--
theorem `Module.finrank_dvd_finrank_right` / 定理 `Module.finrank_dvd_finrank_right`

English:
theorem Module.finrank_dvd_finrank_right
  proof: Dvd.intro (finrank K A) (finrank_mul_finrank ..)

中文:
定理 Module.finrank_dvd_finrank_right
  证明: Dvd.intro (finrank K A) (finrank_mul_finrank ..)

Depends on / 依赖: Dvd.intro, finrank, finrank_mul_finrank
-/
theorem Module.finrank_dvd_finrank_right :
    Module.finrank F K ∣ Module.finrank F A :=
  Dvd.intro (finrank K A) (finrank_mul_finrank ..)

/--
theorem `Module.finrank_div_finrank_cancel_right` / 定理 `Module.finrank_div_finrank_cancel_right`

English:
theorem Module.finrank_div_finrank_cancel_right
  given: (h : Module.finrank K A != 0)
  proof: Nat.div_eq_of_eq_mul_left h.bot_lt (finrank_mul_finrank ..).symm

中文:
定理 Module.finrank_div_finrank_cancel_right
  条件: (h : Module.finrank K A != 0)
  证明: Nat.div_eq_of_eq_mul_left h.bot_lt (finrank_mul_finrank ..).symm

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, bot_lt, div_eq_of_eq_mul_left, finrank_mul_finrank, h.bot_lt
-/
theorem Module.finrank_div_finrank_cancel_right (h : Module.finrank K A != 0) :
    Module.finrank F A / Module.finrank K A = Module.finrank F K :=
  Nat.div_eq_of_eq_mul_left h.bot_lt (finrank_mul_finrank ..).symm

/--
theorem `Module.finrank_div_finrank_cancel_left` / 定理 `Module.finrank_div_finrank_cancel_left`

English:
theorem Module.finrank_div_finrank_cancel_left
  given: (h : Module.finrank F K != 0)
  proof: Nat.div_eq_of_eq_mul_right h.bot_lt (finrank_mul_finrank ..).symm

中文:
定理 Module.finrank_div_finrank_cancel_left
  条件: (h : Module.finrank F K != 0)
  证明: Nat.div_eq_of_eq_mul_right h.bot_lt (finrank_mul_finrank ..).symm

Depends on / 依赖: Nat.div_eq_of_eq_mul_right, bot_lt, div_eq_of_eq_mul_right, finrank_mul_finrank, h.bot_lt, hasFiniteIntegral, hg.hasFiniteIntegral.mono
-/
theorem Module.finrank_div_finrank_cancel_left (h : Module.finrank F K != 0) :
    Module.finrank F A / Module.finrank F K = Module.finrank K A :=
  Nat.div_eq_of_eq_mul_right h.bot_lt (finrank_mul_finrank ..).symm

/--
theorem `Module.finrank_div_finrank_cancel_right_of_nontrivial` / 定理 `Module.finrank_div_finrank_cancel_right_of_nontrivial`

English:
theorem Module.finrank_div_finrank_cancel_right_of_nontrivial
  given: [Nontrivial A] [Module.Finite K A]
  proof: finrank_div_finrank_cancel_right F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

中文:
定理 Module.finrank_div_finrank_cancel_right_of_nontrivial
  条件: [Nontrivial A] [Module.Finite K A]
  证明: finrank_div_finrank_cancel_right F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

Depends on / 依赖: finrank_div_finrank_cancel_right, finrank_pos_iff_of_free
-/
theorem Module.finrank_div_finrank_cancel_right_of_nontrivial [Nontrivial A] [Module.Finite K A] :
    Module.finrank F A / Module.finrank K A = Module.finrank F K :=
  finrank_div_finrank_cancel_right F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

/--
theorem `Module.finrank_div_finrank_cancel_left_of_nontrivial` / 定理 `Module.finrank_div_finrank_cancel_left_of_nontrivial`

English:
theorem Module.finrank_div_finrank_cancel_left_of_nontrivial
  given: [Nontrivial K] [Module.Finite F K]
  proof: finrank_div_finrank_cancel_left F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

中文:
定理 Module.finrank_div_finrank_cancel_left_of_nontrivial
  条件: [Nontrivial K] [Module.Finite F K]
  证明: finrank_div_finrank_cancel_left F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

Depends on / 依赖: finrank_div_finrank_cancel_left, finrank_pos_iff_of_free, hasFiniteIntegral, hf.hasFiniteIntegral.congr
-/
theorem Module.finrank_div_finrank_cancel_left_of_nontrivial [Nontrivial K] [Module.Finite F K] :
    Module.finrank F A / Module.finrank F K = Module.finrank K A :=
  finrank_div_finrank_cancel_left F K A ((finrank_pos_iff_of_free ..).mpr ‹_›).ne'

end Tower

variable {R : Type u} {S : Type*} {M M₁ : Type v} {M' : Type v'}
variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [Module.Free R M]
variable [AddCommMonoid M'] [Module R M'] [Module.Free R M']
variable [AddCommMonoid M₁] [Module R M₁] [Module.Free R M₁]

namespace Module.Free

variable {N : Type v} [AddCommMonoid N] [Module R N]
variable {N' : Type v'} [AddCommMonoid N'] [Module R N']

/--
theorem `exists_linearMap_injective_of_linearIndependent_of_lift_rank_le` / 定理 `exists_linearMap_injective_of_linearIndependent_of_lift_rank_le`

English:
theorem exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
  proof: by
  nontriviality M
  have := Module.nontrivial R M
  rcases Module.Free.exists_set R M with ⟨_, ⟨B⟩⟩
  replace cnd := (Cardinal.lift_le.2 B.linearIndependent.cardinal_le_rank).trans cnd
  rw [Cardinal.lift_mk_le'] at cnd
  rcases cnd with ⟨i, hi⟩
  refine ⟨B.constr Nat (v ∘ i), B.injective_constr_

中文:
定理 exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
  证明: by
  nontriviality M
  have := Module.nontrivial R M
  rcases Module.Free.exists_set R M with ⟨_, ⟨B⟩⟩
  replace cnd := (Cardinal.lift_le.2 B.linearIndependent.cardinal_le_rank).trans cnd
  rw [Cardinal.lift_mk_le'] at cnd
  rcases cnd with ⟨i, hi⟩
  refine ⟨B.constr Nat (v ∘ i), B.injective_constr_

Depends on / 依赖: B.constr, B.injective_constr_of_linearIndependent, B.linearIndependent.cardinal_le_rank, Cardinal, Cardinal.lift_le, Cardinal.lift_mk_le, Module, Module.Free.exists_set, Module.nontrivial, cardinal_le_rank, constr, exists_set, hv.comp, injective_constr_of_linearIndependent, lift_le, lift_mk_le, linearIndependent, nontrivial, nontriviality, replace
-/
theorem exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    {ι : Type w} {v : ι -> N'} (hv : LinearIndependent R v)
    (cnd : Cardinal.lift.{w} (Module.rank R M) <= Cardinal.lift.{v} #ι) :
    exists f : M ->ₗ[R] N', Function.Injective f := by
  nontriviality M
  have := Module.nontrivial R M
  rcases Module.Free.exists_set R M with ⟨_, ⟨B⟩⟩
  replace cnd := (Cardinal.lift_le.2 B.linearIndependent.cardinal_le_rank).trans cnd
  rw [Cardinal.lift_mk_le'] at cnd
  rcases cnd with ⟨i, hi⟩
  refine ⟨B.constr Nat (v ∘ i), B.injective_constr_of_linearIndependent (hv.comp _ hi)⟩

/--
theorem `exists_linearMap_injective_of_linearIndependent_of_rank_le` / 定理 `exists_linearMap_injective_of_linearIndependent_of_rank_le`

English:
theorem exists_linearMap_injective_of_linearIndependent_of_rank_le
  proof: exists_linearMap_injective_of_linearIndependent_of_lift_rank_le hv (by simpa using cnd)

中文:
定理 exists_linearMap_injective_of_linearIndependent_of_rank_le
  证明: exists_linearMap_injective_of_linearIndependent_of_lift_rank_le hv (by simpa using cnd)

Depends on / 依赖: _enorm, enorm_eq_iff_norm_eq, enorm_eq_iff_norm_eq.mpr, exists_linearMap_injective_of_linearIndependent_of_lift_rank_le, h.mono, integrable_congr
-/
theorem exists_linearMap_injective_of_linearIndependent_of_rank_le
    {ι : Type v} {v : ι -> N} (hv : LinearIndependent R v) (cnd : Module.rank R M <= #ι) :
    exists f : M ->ₗ[R] N, Function.Injective f :=
  exists_linearMap_injective_of_linearIndependent_of_lift_rank_le hv (by simpa using cnd)

/--
theorem `exists_linearMap_injective_of_lift_rank_lt` / 定理 `exists_linearMap_injective_of_lift_rank_lt`

English:
theorem exists_linearMap_injective_of_lift_rank_lt
  proof: by
  rcases exists_set_linearIndependent_of_lt_lift_rank cnd with ⟨s, hs, hs₂⟩
  exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    hs₂.linearIndependent hs.symm.le

中文:
定理 exists_linearMap_injective_of_lift_rank_lt
  证明: by
  rcases exists_set_linearIndependent_of_lt_lift_rank cnd with ⟨s, hs, hs₂⟩
  exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    hs₂.linearIndependent hs.symm.le

Depends on / 依赖: exists_linearMap_injective_of_linearIndependent_of_lift_rank_le, exists_set_linearIndependent_of_lt_lift_rank, hs.symm.le, linearIndependent
-/
theorem exists_linearMap_injective_of_lift_rank_lt
    (cnd : Cardinal.lift.{v'} (Module.rank R M) < Cardinal.lift.{v} (Module.rank R N')) :
    exists f : M ->ₗ[R] N', Function.Injective f := by
  rcases exists_set_linearIndependent_of_lt_lift_rank cnd with ⟨s, hs, hs₂⟩
  exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le
    hs₂.linearIndependent hs.symm.le

/--
theorem `exists_linearMap_injective_of_rank_lt` / 定理 `exists_linearMap_injective_of_rank_lt`

English:
theorem exists_linearMap_injective_of_rank_lt
  given: (cnd : Module.rank R M < Module.rank R N)
  proof: exists_linearMap_injective_of_lift_rank_lt (by simpa using cnd)

中文:
定理 exists_linearMap_injective_of_rank_lt
  条件: (cnd : Module.rank R M < Module.rank R N)
  证明: exists_linearMap_injective_of_lift_rank_lt (by simpa using cnd)

Depends on / 依赖: exists_linearMap_injective_of_lift_rank_lt
-/
theorem exists_linearMap_injective_of_rank_lt (cnd : Module.rank R M < Module.rank R N) :
    exists f : M ->ₗ[R] N, Function.Injective f :=
  exists_linearMap_injective_of_lift_rank_lt (by simpa using cnd)

end Module.Free

section StrongRankCondition

variable [StrongRankCondition R]

namespace Module.Free

variable (R M)

/--
theorem `rank_eq_card_chooseBasisIndex` / 定理 `rank_eq_card_chooseBasisIndex`

English:
theorem rank_eq_card_chooseBasisIndex
  statement: Module.rank R M = #(ChooseBasisIndex R M)
  proof: (chooseBasis R M).mk_eq_rank''.symm

中文:
定理 rank_eq_card_chooseBasisIndex
  结论: Module.rank R M = #(ChooseBasisIndex R M)
  证明: (chooseBasis R M).mk_eq_rank''.symm

Depends on / 依赖: chooseBasis, mk_eq_rank
-/
theorem rank_eq_card_chooseBasisIndex : Module.rank R M = #(ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_rank''.symm

/--
theorem `_root_.Module.finrank_eq_card_chooseBasisIndex` / 定理 `_root_.Module.finrank_eq_card_chooseBasisIndex`

English:
theorem _root_.Module.finrank_eq_card_chooseBasisIndex
  given: [Module.Finite R M]
  proof: by
  simp [finrank, rank_eq_card_chooseBasisIndex]

中文:
定理 _root_.Module.finrank_eq_card_chooseBasisIndex
  条件: [Module.Finite R M]
  证明: by
  simp [finrank, rank_eq_card_chooseBasisIndex]

Depends on / 依赖: finrank, rank_eq_card_chooseBasisIndex
-/
theorem _root_.Module.finrank_eq_card_chooseBasisIndex [Module.Finite R M] :
    finrank R M = Fintype.card (ChooseBasisIndex R M) := by
  simp [finrank, rank_eq_card_chooseBasisIndex]

/--
lemma `rank_eq_mk_of_infinite_lt` / 引理 `rank_eq_mk_of_infinite_lt`

English:
lemma rank_eq_mk_of_infinite_lt
  given: [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M)
  proof: by
have : Infinite M := infinite_iff.mpr lift_le.mp le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M ->₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_i

中文:
引理 rank_eq_mk_of_infinite_lt
  条件: [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M)
  证明: by
have : Infinite M := infinite_iff.mpr lift_le.mp le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M ->₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_i

Depends on / 依赖: ChooseBasisIndex, Infinite, chooseBasis, h.symm, h_lt, h_lt.le, infinite_iff, infinite_iff.mpr, le_trans, lift_inj, lift_inj.mp, lift_le, lift_le.mp, lift_lift, lift_max, lift_mk_eq, lift_umax, max_eq_iff, max_eq_iff.mp, mk_finsupp_lift_of_infinite
-/
lemma rank_eq_mk_of_infinite_lt [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M) :
    Module.rank R M = #M := by
have : Infinite M := infinite_iff.mpr lift_le.mp le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M ->₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_inj.mp ((max_eq_iff.mp h.symm).resolve_right <| not_and_of_not_left _ ?_).left
  exact (lift_umax.{v, u}.symm ▸ h_lt).ne

end Module.Free

open Module.Free

open Cardinal

/--
theorem `lift_rank_le_iff_exists_linearMap` / 定理 `lift_rank_le_iff_exists_linearMap`

English:
theorem lift_rank_le_iff_exists_linearMap
  proof: by
    rcases Module.Free.exists_set R M' with ⟨_, ⟨B⟩⟩
    exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le B.linearIndependent
      (B.mk_eq_rank''.symm ▸ h)
  mpr := fun ⟨f, hf⟩ => LinearMap.lift_rank_le_of_injective f hf

中文:
定理 lift_rank_le_iff_exists_linearMap
  证明: by
    rcases Module.Free.exists_set R M' with ⟨_, ⟨B⟩⟩
    exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le B.linearIndependent
      (B.mk_eq_rank''.symm ▸ h)
  mpr := fun ⟨f, hf⟩ => LinearMap.lift_rank_le_of_injective f hf

Depends on / 依赖: B.linearIndependent, B.mk_eq_rank, LinearMap, LinearMap.lift_rank_le_of_injective, Module, Module.Free.exists_set, exists_linearMap_injective_of_linearIndependent_of_lift_rank_le, exists_set, lift_rank_le_of_injective, linearIndependent, mk_eq_rank
-/
theorem lift_rank_le_iff_exists_linearMap :
    Cardinal.lift.{v'} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R M') ↔
    exists f : M ->ₗ[R] M', Function.Injective f where
  mp h := by
    rcases Module.Free.exists_set R M' with ⟨_, ⟨B⟩⟩
    exact exists_linearMap_injective_of_linearIndependent_of_lift_rank_le B.linearIndependent
      (B.mk_eq_rank''.symm ▸ h)
  mpr := fun ⟨f, hf⟩ => LinearMap.lift_rank_le_of_injective f hf

/--
theorem `rank_le_iff_exists_linearMap` / 定理 `rank_le_iff_exists_linearMap`

English:
theorem rank_le_iff_exists_linearMap
  proof: by
  simp [← lift_rank_le_iff_exists_linearMap]

中文:
定理 rank_le_iff_exists_linearMap
  证明: by
  simp [← lift_rank_le_iff_exists_linearMap]

Depends on / 依赖: lift_rank_le_iff_exists_linearMap
-/
theorem rank_le_iff_exists_linearMap :
    Module.rank R M <= Module.rank R M₁ ↔ exists f : M ->ₗ[R] M₁, Function.Injective f := by
  simp [← lift_rank_le_iff_exists_linearMap]

/--
theorem `finrank_le_iff_exists_linearMap` / 定理 `finrank_le_iff_exists_linearMap`

English:
theorem finrank_le_iff_exists_linearMap
  given: [Module.Finite R M] [Module.Finite R M']
  proof: by
  simp [← lift_rank_le_iff_exists_linearMap, ← finrank_eq_rank]

中文:
定理 finrank_le_iff_exists_linearMap
  条件: [Module.Finite R M] [Module.Finite R M']
  证明: by
  simp [← lift_rank_le_iff_exists_linearMap, ← finrank_eq_rank]

Depends on / 依赖: finrank_eq_rank, lift_rank_le_iff_exists_linearMap
-/
theorem finrank_le_iff_exists_linearMap [Module.Finite R M] [Module.Finite R M'] :
    finrank R M <= finrank R M' ↔ exists f : M ->ₗ[R] M', Function.Injective f := by
  simp [← lift_rank_le_iff_exists_linearMap, ← finrank_eq_rank]

/--
theorem `nonempty_linearEquiv_of_lift_rank_eq` / 定理 `nonempty_linearEquiv_of_lift_rank_eq`

English:
theorem nonempty_linearEquiv_of_lift_rank_eq
  proof: by
  obtain ⟨⟨α, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨β, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #α = Cardinal.lift.{v, v'} #β := by
    rw [B.mk_eq_rank'']; rw [cnd]; rw [B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 th

中文:
定理 nonempty_linearEquiv_of_lift_rank_eq
  证明: by
  obtain ⟨⟨α, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨β, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #α = Cardinal.lift.{v, v'} #β := by
    rw [B.mk_eq_rank'']; rw [cnd]; rw [B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 th

Depends on / 依赖: B.equiv, B.mk_eq_rank, Cardinal, Cardinal.lift, Cardinal.lift_mk_eq, Module, Module.Free.exists_basis, exists_basis, lift_mk_eq, mk_eq_rank
-/
theorem nonempty_linearEquiv_of_lift_rank_eq
    (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    Nonempty (M ≃ₗ[R] M') := by
  obtain ⟨⟨α, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨β, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #α = Cardinal.lift.{v, v'} #β := by
    rw [B.mk_eq_rank'']; rw [cnd]; rw [B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')

/--
theorem `nonempty_linearEquiv_of_rank_eq` / 定理 `nonempty_linearEquiv_of_rank_eq`

English:
theorem nonempty_linearEquiv_of_rank_eq
  given: (cond : Module.rank R M = Module.rank R M₁)
  proof: nonempty_linearEquiv_of_lift_rank_eq congr_arg _ cond

中文:
定理 nonempty_linearEquiv_of_rank_eq
  条件: (cond : Module.rank R M = Module.rank R M₁)
  证明: nonempty_linearEquiv_of_lift_rank_eq congr_arg _ cond

Depends on / 依赖: congr_arg, nonempty_linearEquiv_of_lift_rank_eq
-/
theorem nonempty_linearEquiv_of_rank_eq (cond : Module.rank R M = Module.rank R M₁) :
    Nonempty (M ≃ₗ[R] M₁) :=
nonempty_linearEquiv_of_lift_rank_eq congr_arg _ cond

section

variable (M M' M₁)

/--
Definition of `LinearEquiv.ofLiftRankEq` / `LinearEquiv.ofLiftRankEq` 的定义

English:
definition LinearEquiv.ofLiftRankEq
  body: Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)

中文:
定义 LinearEquiv.ofLiftRankEq
  定义体: Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)

Depends on / 依赖: Classical, Classical.choice, choice, nonempty_linearEquiv_of_lift_rank_eq
-/
def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    M ≃ₗ[R] M' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)

/--
Definition of `LinearEquiv.ofRankEq` / `LinearEquiv.ofRankEq` 的定义

English:
definition LinearEquiv.ofRankEq
  signature: (cond : Module.rank R M = Module.rank R M₁)
  body: Classical.choice (nonempty_linearEquiv_of_rank_eq cond)

中文:
定义 LinearEquiv.ofRankEq
  签名: (cond : Module.rank R M = Module.rank R M₁)
  定义体: Classical.choice (nonempty_linearEquiv_of_rank_eq cond)

Depends on / 依赖: Classical, Classical.choice, choice, nonempty_linearEquiv_of_rank_eq
-/
def LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R M₁) : M ≃ₗ[R] M₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)

end

/--
theorem `Module.nonempty_linearEquiv_iff_lift_rank_eq` / 定理 `Module.nonempty_linearEquiv_iff_lift_rank_eq`

English:
theorem Module.nonempty_linearEquiv_iff_lift_rank_eq
  statement: Nonempty (M ≃ₗ[R] M') ↔
  proof: ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_lift_rank_eq := Module.nonempty_linearEquiv_iff_lift_rank_eq

中文:
定理 Module.nonempty_linearEquiv_iff_lift_rank_eq
  结论: Nonempty (M ≃ₗ[R] M') ↔
  证明: ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_lift_rank_eq := Module.nonempty_linearEquiv_iff_lift_rank_eq

Depends on / 依赖: LinearEquiv, LinearEquiv.lift_rank_eq, lift_rank_eq, nonempty_linearEquiv_of_lift_rank_eq
-/
theorem Module.nonempty_linearEquiv_iff_lift_rank_eq : Nonempty (M ≃ₗ[R] M') ↔
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_lift_rank_eq := Module.nonempty_linearEquiv_iff_lift_rank_eq

/--
theorem `Module.nonempty_linearEquiv_iff_rank_eq` / 定理 `Module.nonempty_linearEquiv_iff_rank_eq`

English:
theorem Module.nonempty_linearEquiv_iff_rank_eq
  proof: ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_rank_eq := Module.nonempty_linearEquiv_iff_rank_eq

中文:
定理 Module.nonempty_linearEquiv_iff_rank_eq
  证明: ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_rank_eq := Module.nonempty_linearEquiv_iff_rank_eq

Depends on / 依赖: LinearEquiv, LinearEquiv.rank_eq, nonempty_linearEquiv_of_rank_eq, rank_eq
-/
theorem Module.nonempty_linearEquiv_iff_rank_eq :
    Nonempty (M ≃ₗ[R] M₁) ↔ Module.rank R M = Module.rank R M₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩

@[deprecated (since := "2026-06-30")]
alias LinearEquiv.nonempty_equiv_iff_rank_eq := Module.nonempty_linearEquiv_iff_rank_eq

/--
theorem `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq` / 定理 `FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`

English:
theorem FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  proof: nonempty_linearEquiv_of_lift_rank_eq by simp only [← finrank_eq_rank, cond, lift_natCast]

中文:
定理 FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  证明: nonempty_linearEquiv_of_lift_rank_eq by simp only [← finrank_eq_rank, cond, lift_natCast]

Depends on / 依赖: finrank_eq_rank, lift_natCast, nonempty_linearEquiv_of_lift_rank_eq
-/
theorem FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    [Module.Finite R M] [Module.Finite R M'] (cond : finrank R M = finrank R M') :
    Nonempty (M ≃ₗ[R] M') :=
nonempty_linearEquiv_of_lift_rank_eq by simp only [← finrank_eq_rank, cond, lift_natCast]

/--
theorem `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq` / 定理 `FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq`

English:
theorem FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
  statement: [Module.Finite R M]
  proof: ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩

中文:
定理 FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
  结论: [Module.Finite R M]
  证明: ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩

Depends on / 依赖: finrank_eq, h.finrank_eq, nonempty_linearEquiv_of_finrank_eq
-/
theorem FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq [Module.Finite R M]
    [Module.Finite R M'] : Nonempty (M ≃ₗ[R] M') ↔ finrank R M = finrank R M' :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩

variable (M M') in
/--
Definition of `LinearEquiv.ofFinrankEq` / `LinearEquiv.ofFinrankEq` 的定义

English:
definition LinearEquiv.ofFinrankEq
  signature: [Module.Finite R M] [Module.Finite R M']
  body: Classical.choice FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond

中文:
定义 LinearEquiv.ofFinrankEq
  签名: [Module.Finite R M] [Module.Finite R M']
  定义体: Classical.choice FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond

Depends on / 依赖: Classical, Classical.choice, FiniteDimensional, FiniteDimensional.nonempty_linearEquiv_of_finrank_eq, choice, nonempty_linearEquiv_of_finrank_eq
-/
noncomputable def LinearEquiv.ofFinrankEq [Module.Finite R M] [Module.Finite R M']
    (cond : finrank R M = finrank R M') : M ≃ₗ[R] M' :=
Classical.choice FiniteDimensional.nonempty_linearEquiv_of_finrank_eq cond

namespace Module

/--
lemma `subsingleton_of_rank_zero` / 引理 `subsingleton_of_rank_zero`

English:
lemma subsingleton_of_rank_zero
  given: (h : Module.rank R M = 0)
  statement: Subsingleton M
  proof: by
  rw [← Basis.mk_eq_rank'' (Module.Free.chooseBasis R M)]; rw [Cardinal.mk_eq_zero_iff] at h
  exact (Module.Free.chooseBasis R M).repr.subsingleton

中文:
引理 subsingleton_of_rank_zero
  条件: (h : Module.rank R M = 0)
  结论: Subsingleton M
  证明: by
  rw [← Basis.mk_eq_rank'' (Module.Free.chooseBasis R M)]; rw [Cardinal.mk_eq_zero_iff] at h
  exact (Module.Free.chooseBasis R M).repr.subsingleton

Depends on / 依赖: Basis.mk_eq_rank, Cardinal, Cardinal.mk_eq_zero_iff, Module, Module.Free.chooseBasis, chooseBasis, mk_eq_rank, mk_eq_zero_iff, repr.subsingleton, subsingleton
-/
lemma subsingleton_of_rank_zero (h : Module.rank R M = 0) : Subsingleton M := by
  rw [← Basis.mk_eq_rank'' (Module.Free.chooseBasis R M)]; rw [Cardinal.mk_eq_zero_iff] at h
  exact (Module.Free.chooseBasis R M).repr.subsingleton

/--
lemma `rank_lt_aleph0_iff` / 引理 `rank_lt_aleph0_iff`

English:
lemma rank_lt_aleph0_iff
  statement: Module.rank R M < ℵ₀ ↔ Module.Finite R M
  proof: by
  rw [Free.rank_eq_card_chooseBasisIndex]; rw [mk_lt_aleph0_iff]
  exact ⟨fun h => Finite.of_basis (Free.chooseBasis R M),
    fun I => Finite.of_fintype (Free.ChooseBasisIndex R M)⟩

中文:
引理 rank_lt_aleph0_iff
  结论: Module.rank R M < ℵ₀ ↔ Module.Finite R M
  证明: by
  rw [Free.rank_eq_card_chooseBasisIndex]; rw [mk_lt_aleph0_iff]
  exact ⟨fun h => Finite.of_basis (Free.chooseBasis R M),
    fun I => Finite.of_fintype (Free.ChooseBasisIndex R M)⟩

Depends on / 依赖: ChooseBasisIndex, Finite, Finite.of_basis, Finite.of_fintype, Free.ChooseBasisIndex, Free.chooseBasis, Free.rank_eq_card_chooseBasisIndex, chooseBasis, mk_lt_aleph0_iff, of_basis, of_fintype, rank_eq_card_chooseBasisIndex
-/
lemma rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ Module.Finite R M := by
  rw [Free.rank_eq_card_chooseBasisIndex]; rw [mk_lt_aleph0_iff]
  exact ⟨fun h => Finite.of_basis (Free.chooseBasis R M),
    fun I => Finite.of_fintype (Free.ChooseBasisIndex R M)⟩

/--
theorem `finrank_of_not_finite` / 定理 `finrank_of_not_finite`

English:
theorem finrank_of_not_finite
  given: (h : ¬Module.Finite R M)
  statement: finrank R M = 0
  proof: by
  rw [finrank]; rw [toNat_eq_zero]; rw [← not_lt]; rw [Module.rank_lt_aleph0_iff]
  exact .inr h

中文:
定理 finrank_of_not_finite
  条件: (h : ¬Module.Finite R M)
  结论: finrank R M = 0
  证明: by
  rw [finrank]; rw [toNat_eq_zero]; rw [← not_lt]; rw [Module.rank_lt_aleph0_iff]
  exact .inr h

Depends on / 依赖: Module, Module.rank_lt_aleph0_iff, finrank, not_lt, rank_lt_aleph0_iff, toNat_eq_zero
-/
theorem finrank_of_not_finite (h : ¬Module.Finite R M) : finrank R M = 0 := by
  rw [finrank]; rw [toNat_eq_zero]; rw [← not_lt]; rw [Module.rank_lt_aleph0_iff]
  exact .inr h

/--
theorem `finite_of_finrank_pos` / 定理 `finite_of_finrank_pos`

English:
theorem finite_of_finrank_pos
  given: (h : 0 < finrank R M)
  statement: Module.Finite R M
  proof: by
  contrapose h
  simp [finrank_of_not_finite h]

中文:
定理 finite_of_finrank_pos
  条件: (h : 0 < finrank R M)
  结论: Module.Finite R M
  证明: by
  contrapose h
  simp [finrank_of_not_finite h]

Depends on / 依赖: contrapose, finrank_of_not_finite
-/
theorem finite_of_finrank_pos (h : 0 < finrank R M) : Module.Finite R M := by
  contrapose h
  simp [finrank_of_not_finite h]

/--
theorem `finite_of_finrank_eq_succ` / 定理 `finite_of_finrank_eq_succ`

English:
theorem finite_of_finrank_eq_succ
  given: {n : Nat} (hn : finrank R M = n.succ)
  statement: Module.Finite R M
  proof: finite_of_finrank_pos by rw [hn]; exact n.succ_pos

中文:
定理 finite_of_finrank_eq_succ
  条件: {n : 自然数} (hn : finrank R M = n.succ)
  结论: Module.Finite R M
  证明: finite_of_finrank_pos by rw [hn]; exact n.succ_pos

Depends on / 依赖: finite_of_finrank_pos, n.succ_pos, succ_pos
-/
theorem finite_of_finrank_eq_succ {n : Nat} (hn : finrank R M = n.succ) : Module.Finite R M :=
finite_of_finrank_pos by rw [hn]; exact n.succ_pos

/--
theorem `finite_iff_of_rank_eq_nsmul` / 定理 `finite_iff_of_rank_eq_nsmul`

English:
theorem finite_iff_of_rank_eq_nsmul
  statement: {W} [AddCommMonoid W] [Module R W] [Module.Free R W] {n : Nat}
  proof: by
  simp only [← rank_lt_aleph0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

中文:
定理 finite_iff_of_rank_eq_nsmul
  结论: {W} [AddCommMonoid W] [Module R W] [Module.Free R W] {n : 自然数}
  证明: by
  simp only [← rank_lt_aleph0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

Depends on / 依赖: nsmul_lt_aleph0_iff_of_ne_zero, rank_lt_aleph0_iff
-/
theorem finite_iff_of_rank_eq_nsmul {W} [AddCommMonoid W] [Module R W] [Module.Free R W] {n : Nat}
    (hn : n != 0) (hVW : Module.rank R M = n • Module.rank R W) :
    Module.Finite R M ↔ Module.Finite R W := by
  simp only [← rank_lt_aleph0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

variable (R S M) in
omit [Module.Free R M] in
/--
lemma `finrank_top_le_finrank_of_isScalarTower_of_free` / 引理 `finrank_top_le_finrank_of_isScalarTower_of_free`

English:
lemma finrank_top_le_finrank_of_isScalarTower_of_free
  statement: [Semiring S] [StrongRankCondition S]
  proof: by
  by_cases H : Module.Finite S M
  · have := Module.Finite.trans (R := R) S M
    exact finrank_top_le_finrank_of_isScalarTower R S M
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

中文:
引理 finrank_top_le_finrank_of_isScalarTower_of_free
  结论: [Semiring S] [StrongRankCondition S]
  证明: by
  by_cases H : Module.Finite S M
  · have := Module.Finite.trans (R := R) S M
    exact finrank_top_le_finrank_of_isScalarTower R S M
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_zero.mpr, Finite, Module, Module.Finite, Module.Finite.trans, Module.rank_lt_aleph0_iff, finrank, finrank_top_le_finrank_of_isScalarTower, not_lt, rank_lt_aleph0_iff, toNat_eq_zero, zero_le
-/
lemma finrank_top_le_finrank_of_isScalarTower_of_free [Semiring S] [StrongRankCondition S]
    [Module S M] [Module R S] [FaithfulSMul R S] [Module.Finite R S]
    [IsScalarTower R S S] [IsScalarTower R S M] [Module.Free S M] :
    finrank S M <= finrank R M := by
  by_cases H : Module.Finite S M
  · have := Module.Finite.trans (R := R) S M
    exact finrank_top_le_finrank_of_isScalarTower R S M
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

variable (R) in
/--
lemma `finrank_bot_le_finrank_of_isScalarTower_of_free` / 引理 `finrank_bot_le_finrank_of_isScalarTower_of_free`

English:
lemma finrank_bot_le_finrank_of_isScalarTower_of_free
  statement: (S T : Type*) [Semiring S] [Semiring T]
  proof: by
  by_cases H : Module.Finite R S
  · have := Module.Finite.trans (R := R) S T
    exact finrank_bot_le_finrank_of_isScalarTower R S T
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

中文:
引理 finrank_bot_le_finrank_of_isScalarTower_of_free
  结论: (S T : 类型) [Semiring S] [Semiring T]
  证明: by
  by_cases H : Module.Finite R S
  · have := Module.Finite.trans (R := R) S T
    exact finrank_bot_le_finrank_of_isScalarTower R S T
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_zero.mpr, Finite, Module, Module.Finite, Module.Finite.trans, Module.rank_lt_aleph0_iff, finrank, finrank_bot_le_finrank_of_isScalarTower, not_lt, rank_lt_aleph0_iff, toNat_eq_zero, zero_le
-/
lemma finrank_bot_le_finrank_of_isScalarTower_of_free (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite S T] [Module.Free R S] :
    finrank R S <= finrank R T := by
  by_cases H : Module.Finite R S
  · have := Module.Finite.trans (R := R) S T
    exact finrank_bot_le_finrank_of_isScalarTower R S T
  · rw [finrank, Cardinal.toNat_eq_zero.mpr (.inr _)]
    · exact zero_le
    · rwa [← not_lt, Module.rank_lt_aleph0_iff]

/--
theorem `nonempty_linearEquiv_iff_rank_eq_one` / 定理 `nonempty_linearEquiv_iff_rank_eq_one`

English:
theorem nonempty_linearEquiv_iff_rank_eq_one
  proof: by
  simp [nonempty_linearEquiv_iff_lift_rank_eq, eq_comm]

中文:
定理 nonempty_linearEquiv_iff_rank_eq_one
  证明: by
  simp [nonempty_linearEquiv_iff_lift_rank_eq, eq_comm]

Depends on / 依赖: eq_comm, nonempty_linearEquiv_iff_lift_rank_eq
-/
theorem nonempty_linearEquiv_iff_rank_eq_one :
    Nonempty (R ≃ₗ[R] M) ↔ Module.rank R M = 1 := by
  simp [nonempty_linearEquiv_iff_lift_rank_eq, eq_comm]

/--
theorem `nonempty_linearEquiv_iff_finrank_eq_one` / 定理 `nonempty_linearEquiv_iff_finrank_eq_one`

English:
theorem nonempty_linearEquiv_iff_finrank_eq_one
  proof: by
  simp [nonempty_linearEquiv_iff_rank_eq_one, finrank]

alias ⟨_, nonempty_linearEquiv_of_finrank_eq_one⟩ := nonempty_linearEquiv_iff_finrank_eq_one

中文:
定理 nonempty_linearEquiv_iff_finrank_eq_one
  证明: by
  simp [nonempty_linearEquiv_iff_rank_eq_one, finrank]

alias ⟨_, nonempty_linearEquiv_of_finrank_eq_one⟩ := nonempty_linearEquiv_iff_finrank_eq_one

Depends on / 依赖: finrank, nonempty_linearEquiv_iff_rank_eq_one
-/
theorem nonempty_linearEquiv_iff_finrank_eq_one :
    Nonempty (R ≃ₗ[R] M) ↔ finrank R M = 1 := by
  simp [nonempty_linearEquiv_iff_rank_eq_one, finrank]

alias ⟨_, nonempty_linearEquiv_of_finrank_eq_one⟩ := nonempty_linearEquiv_iff_finrank_eq_one

/--
theorem `nonempty_algEquiv_iff_finrank_eq_one` / 定理 `nonempty_algEquiv_iff_finrank_eq_one`

English:
theorem nonempty_algEquiv_iff_finrank_eq_one
  proof: by
  rw [← nonempty_linearEquiv_iff_finrank_eq_one]
  exact ⟨fun ⟨e⟩ => ⟨e⟩, fun ⟨e⟩ =>
    ⟨.ofBijective (Algebra.ofId R S) (bijective_algebraMap_of_linearEquiv e)⟩⟩

中文:
定理 nonempty_algEquiv_iff_finrank_eq_one
  证明: by
  rw [← nonempty_linearEquiv_iff_finrank_eq_one]
  exact ⟨fun ⟨e⟩ => ⟨e⟩, fun ⟨e⟩ =>
    ⟨.ofBijective (Algebra.ofId R S) (bijective_algebraMap_of_linearEquiv e)⟩⟩

Depends on / 依赖: Algebra, Algebra.ofId, bijective_algebraMap_of_linearEquiv, nonempty_linearEquiv_iff_finrank_eq_one, ofBijective
-/
theorem nonempty_algEquiv_iff_finrank_eq_one
    {R S : Type*} [CommSemiring R] [StrongRankCondition R] [Semiring S] [Algebra R S]
    [Free R S] : Nonempty (R ≃ₐ[R] S) ↔ finrank R S = 1 := by
  rw [← nonempty_linearEquiv_iff_finrank_eq_one]
  exact ⟨fun ⟨e⟩ => ⟨e⟩, fun ⟨e⟩ =>
    ⟨.ofBijective (Algebra.ofId R S) (bijective_algebraMap_of_linearEquiv e)⟩⟩

variable (R M)

/--
Definition of `finBasis` / `finBasis` 的定义

English:
definition finBasis
  signature: [Module.Finite R M]
  body: (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)

中文:
定义 finBasis
  签名: [Module.Finite R M]
  定义体: (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)

Depends on / 依赖: Fintype, Fintype.equivFinOfCardEq, Module, Module.Free.chooseBasis, chooseBasis, equivFinOfCardEq, finrank_eq_card_chooseBasisIndex, reindex
-/
noncomputable def finBasis [Module.Finite R M] :
    Basis (Fin (finrank R M)) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)

/--
Definition of `finBasisOfFinrankEq` / `finBasisOfFinrankEq` 的定义

English:
definition finBasisOfFinrankEq
  signature: [Module.Finite R M] {n : Nat} (hn : finrank R M = n)
  body: (finBasis R M).reindex (finCongr hn)

中文:
定义 finBasisOfFinrankEq
  签名: [Module.Finite R M] {n : 自然数} (hn : finrank R M = n)
  定义体: (finBasis R M).reindex (finCongr hn)

Depends on / 依赖: finBasis, finCongr, reindex
-/
noncomputable def finBasisOfFinrankEq [Module.Finite R M] {n : Nat} (hn : finrank R M = n) :
    Basis (Fin n) R M := (finBasis R M).reindex (finCongr hn)

variable {R M}

/--
Definition of `basisUnique` / `basisUnique` 的定义

English:
definition basisUnique
  signature: (ι : Type*) [Unique ι]
  body: haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.ofUnique _ _)

中文:
定义 basisUnique
  签名: (ι : 类型) [Unique ι]
  定义体: haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.ofUnique _ _)

Depends on / 依赖: Equiv.ofUnique, Finite, Module, Module.Finite, Module.finite_of_finrank_pos, _root_, _root_.zero_lt_one.trans_le, finBasisOfFinrankEq, finite_of_finrank_pos, h.symm.le, ofUnique, reindex, trans_le, zero_lt_one
-/
noncomputable def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R M = 1) :
    Basis ι R M :=
  haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.ofUnique _ _)

/--
theorem `Basis.nonempty_unique_index_of_finrank_eq_one` / 定理 `Basis.nonempty_unique_index_of_finrank_eq_one`

English:
theorem Basis.nonempty_unique_index_of_finrank_eq_one
  proof: by
  -- why isn't this an instance?
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  have : Module.Finite R M :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_succ d1)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  rwa [Module.finrank

中文:
定理 Basis.nonempty_unique_index_of_finrank_eq_one
  证明: by
  -- why isn't this an instance?
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  have : Module.Finite R M :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_succ d1)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  rwa [Module.finrank
-/
theorem Basis.nonempty_unique_index_of_finrank_eq_one
    {ι : Type*} (b : Module.Basis ι R M) (d1 : Module.finrank R M = 1) :
    Nonempty (Unique ι) := by
  -- why isn't this an instance?
  have : Nontrivial R := nontrivial_of_invariantBasisNumber R
  have : Module.Finite R M :=
    Module.finite_of_finrank_pos (Nat.lt_of_sub_eq_succ d1)
  have : Finite ι := Module.Finite.finite_basis b
  have : Fintype ι := Fintype.ofFinite ι
  rwa [Module.finrank_eq_card_basis b, Fintype.card_eq_one_iff_nonempty_unique] at d1

@[simp]
/--
theorem `basisUnique_repr_eq_zero_iff` / 定理 `basisUnique_repr_eq_zero_iff`

English:
theorem basisUnique_repr_eq_zero_iff
  statement: {ι : Type*} [Unique ι]
  proof: ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, map_zero, Finsupp.zero_apply]⟩

omit [StrongRankCondition R] in

中文:
定理 basisUnique_repr_eq_zero_iff
  结论: {ι : 类型} [Unique ι]
  证明: ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, map_zero, Finsupp.zero_apply]⟩

omit [StrongRankCondition R] in

Depends on / 依赖: Finsupp, Finsupp.ext, Finsupp.zero_apply, Subsingleton, Subsingleton.elim, basisUnique, map_eq_zero_iff, map_zero, repr.map_eq_zero_iff.mp, zero_apply
-/
theorem basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι]
    {h : finrank R M = 1} {v : M} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, map_zero, Finsupp.zero_apply]⟩

omit [StrongRankCondition R] in
/--
theorem `_root_.OrzechProperty.bijective_of_surjective_of_finrank_le` / 定理 `_root_.OrzechProperty.bijective_of_surjective_of_finrank_le`

English:
theorem _root_.OrzechProperty.bijective_of_surjective_of_finrank_le
  proof: by
  cases subsingleton_or_nontrivial R
  -- TODO : figure out how to make `nontriviality` work here nicely
  · have := Module.subsingleton R M
    exact ⟨Function.injective_of_subsingleton f, hf⟩
  rcases finrank_le_iff_exists_linearMap.mp h with ⟨_, hi⟩
  exact OrzechProperty.bijective_of_surjecti

中文:
定理 _root_.OrzechProperty.bijective_of_surjective_of_finrank_le
  证明: by
  cases subsingleton_or_nontrivial R
  -- TODO : figure out how to make `nontriviality` work here nicely
  · have := Module.subsingleton R M
    exact ⟨Function.injective_of_subsingleton f, hf⟩
  rcases finrank_le_iff_exists_linearMap.mp h with ⟨_, hi⟩
  exact OrzechProperty.bijective_of_surjecti

Depends on / 依赖: subsingleton_or_nontrivial
-/
theorem _root_.OrzechProperty.bijective_of_surjective_of_finrank_le
    [OrzechProperty R] [Module.Finite R M] [Module.Finite R M']
    (f : M ->ₗ[R] M') (hf : Function.Surjective f) (h : Module.finrank R M <= Module.finrank R M') :
    Function.Bijective f := by
  cases subsingleton_or_nontrivial R
  -- TODO : figure out how to make `nontriviality` work here nicely
  · have := Module.subsingleton R M
    exact ⟨Function.injective_of_subsingleton f, hf⟩
  rcases finrank_le_iff_exists_linearMap.mp h with ⟨_, hi⟩
  exact OrzechProperty.bijective_of_surjective_of_injective _ _ hi hf

variable {R : Type*} [CommSemiring R] [StrongRankCondition R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one` / 定理 `_root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one`

English:
theorem _root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
  proof: by
  let e := (nonempty_linearEquiv_of_finrank_eq_one d1).some
  set c := e.symm (u (e 1)) with hc
  suffices u = c • LinearMap.id by
    use c
    simp only [this, true_and]
    intro d hcd
    rw [LinearMap.ext_iff] at hcd
    simpa using (LinearEquiv.congr_arg (e := e.symm) (hcd (e 1))).symm
  ex

中文:
定理 _root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
  证明: by
  let e := (nonempty_linearEquiv_of_finrank_eq_one d1).some
  set c := e.symm (u (e 1)) with hc
  suffices u = c • LinearMap.id by
    use c
    simp only [this, true_and]
    intro d hcd
    rw [LinearMap.ext_iff] at hcd
    simpa using (LinearEquiv.congr_arg (e := e.symm) (hcd (e 1))).symm
  ex

Depends on / 依赖: LinearEquiv, LinearEquiv.congr_arg, LinearEquiv.map_smul, LinearMap, LinearMap.ext_iff, LinearMap.id, LinearMap.id_coe, LinearMap.smul_apply, congr_arg, e.symm, ext_iff, id_coe, id_eq, map_smul, nonempty_linearEquiv_of_finrank_eq_one, smul_apply, true_and
-/
theorem _root_.LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (d1 : Module.finrank R M = 1) (u : M ->ₗ[R] M) :
    exists! c : R, u = c • LinearMap.id := by
  let e := (nonempty_linearEquiv_of_finrank_eq_one d1).some
  set c := e.symm (u (e 1)) with hc
  suffices u = c • LinearMap.id by
    use c
    simp only [this, true_and]
    intro d hcd
    rw [LinearMap.ext_iff] at hcd
    simpa using (LinearEquiv.congr_arg (e := e.symm) (hcd (e 1))).symm
  ext x
  have (x : M) : x = (e.symm x) • (e 1) := by simp [← LinearEquiv.map_smul]
  rw [this x]
  simp only [hc, map_smul, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [← this]

/-- Endomorphisms of a free module of rank one are homotheties. -/
@[simps apply]
/--
Definition of `_root_.LinearEquiv.smul_id_of_finrank_eq_one` / `_root_.LinearEquiv.smul_id_of_finrank_eq_one` 的定义

English:
definition _root_.LinearEquiv.smul_id_of_finrank_eq_one
  signature: (d1 : Module.finrank R M = 1)
  body: fun c => c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose
  left_inv c := by
    simp [← (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 _).choose_spec.2 c]
  right_inv 

中文:
定义 _root_.LinearEquiv.smul_id_of_finrank_eq_one
  签名: (d1 : Module.finrank R M = 1)
  定义体: fun c => c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose
  left_inv c := by
    simp [← (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 _).choose_spec.2 c]
  right_inv 

Depends on / 依赖: LinearMap, LinearMap.id
-/
noncomputable def _root_.LinearEquiv.smul_id_of_finrank_eq_one (d1 : Module.finrank R M = 1) :
    R ≃ₗ[R] (M ->ₗ[R] M) where
  toFun := fun c => c • LinearMap.id
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]
  invFun u := (u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose
  left_inv c := by
    simp [← (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 _).choose_spec.2 c]
  right_inv u := ((u.existsUnique_eq_smul_id_of_finrank_eq_one d1).choose_spec.1).symm

end Module

end StrongRankCondition

namespace Algebra

instance (priority := 100) (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
    [Algebra R S] [IsQuadraticExtension R S] :
Module.Finite R S := finite_of_finrank_eq_succ IsQuadraticExtension.finrank_eq_two R S

end Algebra
