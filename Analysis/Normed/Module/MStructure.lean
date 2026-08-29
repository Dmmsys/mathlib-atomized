/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# M-structure

A projection P on a normed space X is said to be an L-projection (`IsLprojection`) if, for all `x`
in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

A projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

The L-projections on `X` form a Boolean algebra (`IsLprojection.Subtype.BooleanAlgebra`).

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB\*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW\*-triple with predual `X`, the M-summands
of `A` are exactly the weak\*-closed ideals, and their pre-duals can be identified with the
L-summands of `X`. In the special case when `A` is a C\*-algebra, the M-ideals are exactly the
norm-closed two-sided ideals of `A`, when `A` is also a W\*-algebra the M-summands are exactly the
weak\*-closed two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`MeasureTheory.MeasurableSpace`.

Instead of using `P : X →L[𝕜] X` to represent projections, we use an arbitrary ring `M` with a
faithful action on `X`. `ContinuousLinearMap.apply_module` can be used to recover the `X →L[𝕜] X`
special case.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

@[expose] public section

variable (X : Type*) [NormedAddCommGroup X]
variable {M : Type*} [Ring M] [Module M X]


/--
Definition of `IsLprojection` / `IsLprojection` 的定义

English:
structure IsLprojection
  parameters: (P : M)
  axioms and operations (2):
    - proj : IsIdempotentElem P
    - Lnorm : forall x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖

中文:
结构 IsLprojection
  参数: (P : M)
  公理与运算 (2 个):
    - proj : IsIdempotentElem P
    - Lnorm : 对任意 x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖
-/
structure IsLprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Lnorm : forall x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖

/--
Definition of `IsMprojection` / `IsMprojection` 的定义

English:
structure IsMprojection
  parameters: (P : M)
  axioms and operations (2):
    - proj : IsIdempotentElem P
    - Mnorm : forall x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖

中文:
结构 IsMprojection
  参数: (P : M)
  公理与运算 (2 个):
    - proj : IsIdempotentElem P
    - Mnorm : 对任意 x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖
-/
structure IsMprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Mnorm : forall x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖

variable {X}

namespace IsLprojection

-- TODO: The literature always uses uppercase 'L' for L-projections
/--
theorem `Lcomplement` / 定理 `Lcomplement`

English:
theorem Lcomplement
  given: {P : M} (h : IsLprojection X P)
  statement: IsLprojection X (1 - P)
  proof: ⟨h.proj.one_sub, fun x => by
    rw [add_comm]; rw [sub_sub_cancel]
    exact h.Lnorm x⟩

中文:
定理 Lcomplement
  条件: {P : M} (h : IsLprojection X P)
  结论: IsLprojection X (1 - P)
  证明: ⟨h.proj.one_sub, fun x => by
    rw [add_comm]; rw [sub_sub_cancel]
    exact h.Lnorm x⟩

Depends on / 依赖: add_comm, h.Lnorm, h.proj.one_sub, one_sub, sub_sub_cancel
-/
theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm]; rw [sub_sub_cancel]
    exact h.Lnorm x⟩

/--
theorem `Lcomplement_iff` / 定理 `Lcomplement_iff`

English:
theorem Lcomplement_iff
  given: (P : M)
  statement: IsLprojection X P ↔ IsLprojection X (1 - P)
  proof: ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

中文:
定理 Lcomplement_iff
  条件: (P : M)
  结论: IsLprojection X P ↔ IsLprojection X (1 - P)
  证明: ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

Depends on / 依赖: Lcomplement, h.Lcomplement, sub_sub_cancel
-/
theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

/--
theorem `commute` / 定理 `commute`

English:
theorem commute
  given: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  proof: by
  have PR_eq_RPR : forall R : M, IsLprojection X R -> P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ >= ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • 

中文:
定理 commute
  条件: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  证明: by
  have PR_eq_RPR : forall R : M, IsLprojection X R -> P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ >= ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • 

Depends on / 依赖: IsLprojection, PR_eq_RPR, eq_of_smul_eq_smul, mul_smul, norm_sub_eq_zero_iff, one_smul, smul_sub, sub_smul
-/
theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    Commute P Q := by
  have PR_eq_RPR : forall R : M, IsLprojection X R -> P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ >= ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖(R * R) • x - R • P • R • x‖ + ‖(1 - R) • (1 - P) • R • x‖) := by
            rw [h₁.Lnorm]; rw [h₃.Lnorm]; rw [h₃.Lnorm ((1 - P) • R • x)]; rw [sub_smul 1 P]; rw [one_smul]; rw [smul_sub]; rw [mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖((1 - R) * R) • x - (1 - R) • P • R • x‖) := by
            rw [h₃.proj.eq]; rw [sub_smul 1 P]; rw [one_smul]; rw [smul_sub]; rw [mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖(1 - R) • P • R • x‖) := by
            rw [sub_mul]; rw [h₃.proj.eq]; rw [one_mul]; rw [sub_self]; rw [zero_smul]; rw [zero_sub]; rw [norm_neg]
          _ = ‖R • P • R • x‖ + ‖R • x - R • P • R • x‖ + 2 • ‖(1 - R) • P • R • x‖ := by abel
          _ >= ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ := by
            rw [ge_iff_le]
            have :=
              add_le_add_left (norm_le_insert' (R • x) (R • P • R • x)) (2 • ‖(1 - R) • P • R • x‖)
            simpa only [mul_smul, sub_smul, one_smul] using this
      rw [two_smul] at e1
      nlinarith [e1, norm_nonneg ((P * R) • x - (R * P * R) • x)]
  have QP_eq_QPQ : Q * P = Q * P * Q := by
    have e1 : Q * P - Q * P * Q = 0 := by
      calc
        Q * P - Q * P * Q = P * (1 - Q) - (1 - Q) * P * (1 - Q) := by noncomm_ring
        _ = 0 := sub_eq_zero.mpr (PR_eq_RPR (1 - Q) h₂.Lcomplement)
    simpa [sub_eq_zero] using e1
  change P * Q = Q * P
  rw [QP_eq_QPQ]; rw [PR_eq_RPR Q h₂]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  proof: by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ <= ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P *

中文:
定理 mul
  条件: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  证明: by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ <= ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P *

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.mul_of_commute, add_sub_cancel, commute, le_antisymm, mul_of_commute, norm_add_le, one_smul, sub_smul
-/
theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ <= ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x]; rw [h₁.Lnorm (Q • x)]; rw [sub_smul]; rw [one_smul]; rw [sub_smul]; rw [one_smul]; rw [add_assoc]
      _ >= ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel']; rw [sub_smul]; rw [one_smul]; rw [mul_smul]

/--
theorem `join` / 定理 `join`

English:
theorem join
  given: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  proof: by
  convert! (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring

中文:
定理 join
  条件: [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q)
  证明: by
  convert! (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring

Depends on / 依赖: Lcomplement, Lcomplement.mul, Lcomplement_iff, convert, noncomm_ring
-/
theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert! (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring

/--
Instance `Subtype.instCompl` / 实例 `Subtype.instCompl`

English:
instance Subtype.instCompl
  signature: : Compl { f : M // IsLprojection X f }
  body: ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]

中文:
实例 Subtype.instCompl
  签名: : Compl { f : M // IsLprojection X f }
  定义体: ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]

Depends on / 依赖: Lcomplement, P.prop.Lcomplement
-/
instance Subtype.instCompl : Compl { f : M // IsLprojection X f } :=
  ⟨fun P => ⟨1 - P, P.prop.Lcomplement⟩⟩

@[simp]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (P : { P : M // IsLprojection X P })
  statement: ↑Pᶜ = (1 : M) - ↑P
  proof: rfl

中文:
定理 coe_compl
  条件: (P : { P : M // IsLprojection X P })
  结论: ↑Pᶜ = (1 : M) - ↑P
  证明: rfl
-/
theorem coe_compl (P : { P : M // IsLprojection X P }) : ↑Pᶜ = (1 : M) - ↑P :=
  rfl

/--
Instance `Subtype.inf` / 实例 `Subtype.inf`

English:
instance Subtype.inf
  signature: [FaithfulSMul M X]
  body: ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]

中文:
实例 Subtype.inf
  签名: [FaithfulSMul M X]
  定义体: ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]

Depends on / 依赖: P.prop.mul, Q.prop
-/
instance Subtype.inf [FaithfulSMul M X] : Min { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * Q, P.prop.mul Q.prop⟩⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  proof: rfl

中文:
定理 coe_inf
  条件: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  证明: rfl
-/
theorem coe_inf [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊓ Q) = (↑P : M) * ↑Q :=
  rfl

/--
Instance `Subtype.sup` / 实例 `Subtype.sup`

English:
instance Subtype.sup
  signature: [FaithfulSMul M X]
  body: ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]

中文:
实例 Subtype.sup
  签名: [FaithfulSMul M X]
  定义体: ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]

Depends on / 依赖: P.prop.join, Q.prop
-/
instance Subtype.sup [FaithfulSMul M X] : Max { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.prop.join Q.prop⟩⟩

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  proof: rfl

中文:
定理 coe_sup
  条件: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  证明: rfl
-/
theorem coe_sup [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P ⊔ Q) = (↑P : M) + ↑Q - ↑P * ↑Q :=
  rfl

/--
Instance `Subtype.sdiff` / 实例 `Subtype.sdiff`

English:
instance Subtype.sdiff
  signature: [FaithfulSMul M X]
  body: ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]

中文:
实例 Subtype.sdiff
  签名: [FaithfulSMul M X]
  定义体: ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]

Depends on / 依赖: Lcomplement, P.prop.mul, Q.prop.Lcomplement
-/
instance Subtype.sdiff [FaithfulSMul M X] : SDiff { P : M // IsLprojection X P } :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  proof: rfl

中文:
定理 coe_sdiff
  条件: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  证明: rfl
-/
theorem coe_sdiff [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    ↑(P \ Q) = (↑P : M) * (1 - ↑Q) :=
  rfl

/--
Instance `Subtype.partialOrder` / 实例 `Subtype.partialOrder`

English:
instance Subtype.partialOrder
  signature: [FaithfulSMul M X]
  body: (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁]; rw [mul_assoc]; rw [← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.ext (by convert! (P.prop.commute Q.prop).eq)

中文:
实例 Subtype.partialOrder
  签名: [FaithfulSMul M X]
  定义体: (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁]; rw [mul_assoc]; rw [← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.ext (by convert! (P.prop.commute Q.prop).eq)
-/
instance Subtype.partialOrder [FaithfulSMul M X] :
    PartialOrder { P : M // IsLprojection X P } where
  le P Q := (↑P : M) = ↑(P ⊓ Q)
  le_refl P := by simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans P Q R h₁ h₂ := by
    simp only [coe_inf] at h₁ h₂ ⊢
    rw [h₁]; rw [mul_assoc]; rw [← h₂]
  le_antisymm P Q h₁ h₂ := Subtype.ext (by convert! (P.prop.commute Q.prop).eq)

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  proof: Iff.rfl

中文:
定理 le_def
  条件: [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P })
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def [FaithfulSMul M X] (P Q : { P : M // IsLprojection X P }) :
    P <= Q ↔ (P : M) = ↑(P ⊓ Q) :=
  Iff.rfl

/--
Instance `Subtype.zero` / 实例 `Subtype.zero`

English:
instance Subtype.zero
  signature: : Zero { P : M // IsLprojection X P }
  body: ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]

中文:
实例 Subtype.zero
  签名: : Zero { P : M // IsLprojection X P }
  定义体: ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]

Depends on / 依赖: IsIdempotentElem, norm_zero, one_smul, sub_zero, zero_add, zero_mul, zero_smul
-/
instance Subtype.zero : Zero { P : M // IsLprojection X P } :=
  ⟨⟨0, ⟨by rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [zero_smul, norm_zero, sub_zero, one_smul, zero_add]⟩⟩⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : { P : M // IsLprojection X P }) = (0 : M)
  proof: rfl

中文:
定理 coe_zero
  结论: ↑(0 : { P : M // IsLprojection X P }) = (0 : M)
  证明: rfl
-/
theorem coe_zero : ↑(0 : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl

/--
Instance `Subtype.one` / 实例 `Subtype.one`

English:
instance Subtype.one
  signature: : One { P : M // IsLprojection X P }
  body: ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.Lcomplement⟩⟩

@[simp]

中文:
实例 Subtype.one
  签名: : One { P : M // IsLprojection X P }
  定义体: ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.Lcomplement⟩⟩

@[simp]

Depends on / 依赖: IsLprojection, Lcomplement, prop.Lcomplement, sub_zero
-/
instance Subtype.one : One { P : M // IsLprojection X P } :=
  ⟨⟨1, sub_zero (1 : M) ▸ (0 : { P : M // IsLprojection X P }).prop.Lcomplement⟩⟩

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : { P : M // IsLprojection X P }) = (1 : M)
  proof: rfl

中文:
定理 coe_one
  结论: ↑(1 : { P : M // IsLprojection X P }) = (1 : M)
  证明: rfl
-/
theorem coe_one : ↑(1 : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl

/--
Instance `Subtype.boundedOrder` / 实例 `Subtype.boundedOrder`

English:
instance Subtype.boundedOrder
  signature: [FaithfulSMul M X]
  body: 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]

中文:
实例 Subtype.boundedOrder
  签名: [FaithfulSMul M X]
  定义体: 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]
-/
instance Subtype.boundedOrder [FaithfulSMul M X] :
    BoundedOrder { P : M // IsLprojection X P } where
  top := 1
  le_top P := (mul_one (P : M)).symm
  bot := 0
  bot_le P := (zero_mul (P : M)).symm

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  given: [FaithfulSMul M X]
  proof: rfl

@[simp]

中文:
定理 coe_bot
  条件: [FaithfulSMul M X]
  证明: rfl

@[simp]
-/
theorem coe_bot [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderBot.toBot.bot : { P : M // IsLprojection X P }) = (0 : M) :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [FaithfulSMul M X]
  proof: rfl

中文:
定理 coe_top
  条件: [FaithfulSMul M X]
  证明: rfl
-/
theorem coe_top [FaithfulSMul M X] :
    ↑(BoundedOrder.toOrderTop.toTop.top : { P : M // IsLprojection X P }) = (1 : M) :=
  rfl

/--
theorem `compl_mul` / 定理 `compl_mul`

English:
theorem compl_mul
  given: {P : { P : M // IsLprojection X P }} {Q : M}
  statement: ↑Pᶜ * Q = Q - ↑P * Q
  proof: by
  rw [coe_compl]; rw [sub_mul]; rw [one_mul]

中文:
定理 compl_mul
  条件: {P : { P : M // IsLprojection X P }} {Q : M}
  结论: ↑Pᶜ * Q = Q - ↑P * Q
  证明: by
  rw [coe_compl]; rw [sub_mul]; rw [one_mul]

Depends on / 依赖: coe_compl, one_mul, sub_mul
-/
theorem compl_mul {P : { P : M // IsLprojection X P }} {Q : M} : ↑Pᶜ * Q = Q - ↑P * Q := by
  rw [coe_compl]; rw [sub_mul]; rw [one_mul]

/--
theorem `mul_compl_self` / 定理 `mul_compl_self`

English:
theorem mul_compl_self
  given: {P : { P : M // IsLprojection X P }}
  statement: (↑P : M) * ↑Pᶜ = 0
  proof: by
  rw [coe_compl]; rw [P.prop.proj.mul_one_sub_self]

中文:
定理 mul_compl_self
  条件: {P : { P : M // IsLprojection X P }}
  结论: (↑P : M) * ↑Pᶜ = 0
  证明: by
  rw [coe_compl]; rw [P.prop.proj.mul_one_sub_self]

Depends on / 依赖: P.prop.proj.mul_one_sub_self, coe_compl, mul_one_sub_self
-/
theorem mul_compl_self {P : { P : M // IsLprojection X P }} : (↑P : M) * ↑Pᶜ = 0 := by
  rw [coe_compl]; rw [P.prop.proj.mul_one_sub_self]

/--
theorem `distrib_lattice_lemma` / 定理 `distrib_lattice_lemma`

English:
theorem distrib_lattice_lemma
  given: [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }}
  proof: by
  rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [(mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ))]; rw [← mul_assoc (R : M) (↑Q * ↑R) _]; rw [← coe_inf Q]; rw [(Pᶜ.prop.commute R.prop).eq]; rw [((Q ⊓ R).prop.commute Pᶜ.prop).eq]; rw [(R.prop.commute (Q ⊓ R).prop).eq]; rw [coe_inf Q]; rw [mul_assoc (Q : M)]; 

中文:
定理 distrib_lattice_lemma
  条件: [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }}
  证明: by
  rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [(mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ))]; rw [← mul_assoc (R : M) (↑Q * ↑R) _]; rw [← coe_inf Q]; rw [(Pᶜ.prop.commute R.prop).eq]; rw [((Q ⊓ R).prop.commute Pᶜ.prop).eq]; rw [(R.prop.commute (Q ⊓ R).prop).eq]; rw [coe_inf Q]; rw [mul_assoc (Q : M)]; 

Depends on / 依赖: P.prop, P.prop.proj.eq, R.prop, R.prop.commute, add_mul, add_zero, coe_inf, commute, mul_add, mul_assoc, mul_compl_self, mul_zero, prop.commute, zero_add, zero_mul
-/
theorem distrib_lattice_lemma [FaithfulSMul M X] {P Q R : { P : M // IsLprojection X P }} :
    ((↑P : M) + ↑Pᶜ * R) * (↑P + ↑Q * ↑R * ↑Pᶜ) = ↑P + ↑Q * ↑R * ↑Pᶜ := by
  rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [(mul_assoc _ (R : M) (↑Q * ↑R * ↑Pᶜ))]; rw [← mul_assoc (R : M) (↑Q * ↑R) _]; rw [← coe_inf Q]; rw [(Pᶜ.prop.commute R.prop).eq]; rw [((Q ⊓ R).prop.commute Pᶜ.prop).eq]; rw [(R.prop.commute (Q ⊓ R).prop).eq]; rw [coe_inf Q]; rw [mul_assoc (Q : M)]; rw [← mul_assoc]; rw [mul_assoc (R : M)]; rw [(Pᶜ.prop.commute P.prop).eq]; rw [mul_compl_self]; rw [zero_mul]; rw [mul_zero]; rw [zero_add]; rw [add_zero]; rw [← mul_assoc]; rw [P.prop.proj.eq]; rw [R.prop.proj.eq]; rw [← coe_inf Q]; rw [mul_assoc]; rw [((Q ⊓ R).prop.commute Pᶜ.prop).eq]; rw [← mul_assoc]; rw [Pᶜ.prop.proj.eq]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FaithfulSMul
  signature: M X] : Lattice { P
  body: max
  inf := min
  le_sup_left P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [P.prop.proj.eq]; rw [sub_self]; rw [add_zero]
  le_sup_right P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw

中文:
实例 [FaithfulSMul
  签名: M X] : Lattice { P
  定义体: max
  inf := min
  le_sup_left P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [P.prop.proj.eq]; rw [sub_self]; rw [add_zero]
  le_sup_right P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw
-/
instance [FaithfulSMul M X] : Lattice { P : M // IsLprojection X P } where
  sup := max
  inf := min
  le_sup_left P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [P.prop.proj.eq]; rw [sub_self]; rw [add_zero]
  le_sup_right P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [mul_add]; rw [mul_sub]; rw [(P.prop.commute Q.prop).eq]; rw [← mul_assoc]; rw [Q.prop.proj.eq]; rw [add_sub_cancel]
  sup_le P Q R := by
    rw [le_def]; rw [le_def]; rw [le_def]; rw [coe_inf]; rw [coe_inf]; rw [coe_sup]; rw [coe_inf]; rw [coe_sup]; rw [← add_sub]; rw [add_mul]; rw [sub_mul]; rw [mul_assoc]
    intro h₁ h₂
    rw [← h₂]; rw [← h₁]
  inf_le_left P Q := by
    rw [le_def]; rw [coe_inf]; rw [coe_inf]; rw [coe_inf]; rw [mul_assoc]; rw [(Q.prop.commute P.prop).eq]; rw [← mul_assoc]; rw [P.prop.proj.eq]
  inf_le_right P Q := by rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq]
  le_inf P Q R := by
    rw [le_def]; rw [le_def]; rw [le_def]; rw [coe_inf]; rw [coe_inf]; rw [coe_inf]; rw [coe_inf]; rw [← mul_assoc]
    intro h₁ h₂
    rw [← h₁]; rw [← h₂]

/--
Instance `Subtype.distribLattice` / 实例 `Subtype.distribLattice`

English:
instance Subtype.distribLattice
  signature: [FaithfulSMul M X]
  body: by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf]; rw [coe_sup]; rw [coe_sup]; rw [← add_sub]; rw [← add_sub]; rw [← compl_mul]; rw [← compl_mul]; rw [add_mul]; rw [mul_add]; rw [(Pᶜ.prop.commute Q.prop).eq]; rw [mul_add]; rw [← mul_assoc]; rw [mul_assoc (Q : M

中文:
实例 Subtype.distribLattice
  签名: [FaithfulSMul M X]
  定义体: by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf]; rw [coe_sup]; rw [coe_sup]; rw [← add_sub]; rw [← add_sub]; rw [← compl_mul]; rw [← compl_mul]; rw [add_mul]; rw [mul_add]; rw [(Pᶜ.prop.commute Q.prop).eq]; rw [mul_add]; rw [← mul_assoc]; rw [mul_assoc (Q : M

Depends on / 依赖: P.prop, P.prop.proj.eq, Q.prop, add_mul, add_sub, add_zero, coe_inf, coe_sup, commute, compl_mul, mul_add, mul_assoc, mul_compl_self, mul_zero, prop.commute, prop.proj.eq, zero_add, zero_mul
-/
instance Subtype.distribLattice [FaithfulSMul M X] :
    DistribLattice { P : M // IsLprojection X P } where
  le_sup_inf P Q R := by
    have e₁ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) = ↑P + ↑Q * (R : M) * ↑Pᶜ := by
      rw [coe_inf]; rw [coe_sup]; rw [coe_sup]; rw [← add_sub]; rw [← add_sub]; rw [← compl_mul]; rw [← compl_mul]; rw [add_mul]; rw [mul_add]; rw [(Pᶜ.prop.commute Q.prop).eq]; rw [mul_add]; rw [← mul_assoc]; rw [mul_assoc (Q : M)]; rw [(Pᶜ.prop.commute P.prop).eq]; rw [mul_compl_self]; rw [zero_mul]; rw [mul_zero]; rw [zero_add]; rw [add_zero]; rw [← mul_assoc]; rw [mul_assoc (Q : M)]; rw [P.prop.proj.eq]; rw [Pᶜ.prop.proj.eq]; rw [mul_assoc]; rw [(Pᶜ.prop.commute R.prop).eq]; rw [← mul_assoc]
    have e₂ : ↑((P ⊔ Q) ⊓ (P ⊔ R)) * ↑(P ⊔ Q ⊓ R) = (P : M) + ↑Q * ↑R * ↑Pᶜ := by
      rw [coe_inf]; rw [coe_sup]; rw [coe_sup]; rw [coe_sup]; rw [← add_sub]; rw [← add_sub]; rw [← add_sub]; rw [← compl_mul]; rw [←
        compl_mul]; rw [← compl_mul]; rw [(Pᶜ.prop.commute (Q ⊓ R).prop).eq]; rw [coe_inf]; rw [mul_assoc]; rw [distrib_lattice_lemma]; rw [(Q.prop.commute R.prop).eq]; rw [distrib_lattice_lemma]
    rw [le_def]; rw [e₁]; rw [coe_inf]; rw [e₂]

/--
Instance `Subtype.BooleanAlgebra` / 实例 `Subtype.BooleanAlgebra`

English:
instance Subtype.BooleanAlgebra
  signature: [FaithfulSMul M X]
  body: { IsLprojection.Subtype.instCompl,
    IsLprojection.Subtype.sdiff,
    IsLprojection.Subtype.boundedOrder with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
        (by
 

中文:
实例 Subtype.BooleanAlgebra
  签名: [FaithfulSMul M X]
  定义体: { IsLprojection.Subtype.instCompl,
    IsLprojection.Subtype.sdiff,
    IsLprojection.Subtype.boundedOrder with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
        (by
 

Depends on / 依赖: IsLprojection, IsLprojection.Subtype.boundedOrder, IsLprojection.Subtype.instCompl, IsLprojection.Subtype.sdiff, Subtype, Subtype.ext, add_sub_cancel, boundedOrder, coe_bot, coe_compl, coe_inf, coe_sdiff, coe_sup, coe_top, inf_compl_le_bot, instCompl, mul_compl_self, sdiff_eq, sub_zero, top_le_sup_compl
-/
instance Subtype.BooleanAlgebra [FaithfulSMul M X] :
    BooleanAlgebra { P : M // IsLprojection X P } :=
  { IsLprojection.Subtype.instCompl,
    IsLprojection.Subtype.sdiff,
    IsLprojection.Subtype.boundedOrder with
    inf_compl_le_bot := fun P =>
      (Subtype.ext (by rw [coe_inf, coe_compl, coe_bot, ← coe_compl, mul_compl_self])).le
    top_le_sup_compl := fun P =>
      (Subtype.ext
        (by
          rw [coe_top]; rw [coe_sup]; rw [coe_compl]; rw [add_sub_cancel]; rw [← coe_compl]; rw [mul_compl_self]; rw [sub_zero])).le
sdiff_eq := fun P Q => Subtype.ext by rw [coe_sdiff, ← coe_compl, coe_inf] }

end IsLprojection
