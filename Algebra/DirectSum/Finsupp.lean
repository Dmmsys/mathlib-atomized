/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
   the direct sum of copies of `M` indexed by `ι`.
-/

@[expose] public section


universe u v w

noncomputable section

open DirectSum

open LinearMap Submodule

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

section finsuppLequivDirectSum

variable (R M) (ι : Type*) [DecidableEq ι]

/--
Definition of `finsuppLEquivDirectSum` / `finsuppLEquivDirectSum` 的定义

English:
definition finsuppLEquivDirectSum
  signature: : (ι ->₀ M) ≃ₗ[R] ⨁ _ : ι, M
  body: haveI : forall m : M, Decidable (m != 0) := Classical.decPred _
  finsuppLequivDFinsupp R

@[simp]

中文:
定义 finsuppLEquivDirectSum
  签名: : (ι ->₀ M) ≃ₗ[R] ⨁ _ : ι, M
  定义体: haveI : forall m : M, Decidable (m != 0) := Classical.decPred _
  finsuppLequivDFinsupp R

@[simp]

Depends on / 依赖: Classical, Classical.decPred, Decidable, decPred, finsuppLequivDFinsupp
-/
def finsuppLEquivDirectSum : (ι ->₀ M) ≃ₗ[R] ⨁ _ : ι, M :=
  haveI : forall m : M, Decidable (m != 0) := Classical.decPred _
  finsuppLequivDFinsupp R

@[simp]
/--
theorem `finsuppLEquivDirectSum_single` / 定理 `finsuppLEquivDirectSum_single`

English:
theorem finsuppLEquivDirectSum_single
  given: (i : ι) (m : M)
  proof: Finsupp.toDFinsupp_single i m

@[simp]

中文:
定理 finsuppLEquivDirectSum_single
  条件: (i : ι) (m : M)
  证明: Finsupp.toDFinsupp_single i m

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.toDFinsupp_single i m

@[simp]
/--
theorem `finsuppLEquivDirectSum_apply` / 定理 `finsuppLEquivDirectSum_apply`

English:
theorem finsuppLEquivDirectSum_apply
  given: (m : ι ->₀ M) (i : ι)
  proof: by
  rfl

@[simp]

中文:
定理 finsuppLEquivDirectSum_apply
  条件: (m : ι ->₀ M) (i : ι)
  证明: by
  rfl

@[simp]
-/
theorem finsuppLEquivDirectSum_apply (m : ι ->₀ M) (i : ι) :
    finsuppLEquivDirectSum R M ι m i = m i := by
  rfl

@[simp]
/--
theorem `finsuppLEquivDirectSum_symm_lof` / 定理 `finsuppLEquivDirectSum_symm_lof`

English:
theorem finsuppLEquivDirectSum_symm_lof
  given: (i : ι) (m : M)
  proof: letI : forall m : M, Decidable (m != 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m

中文:
定理 finsuppLEquivDirectSum_symm_lof
  条件: (i : ι) (m : M)
  证明: letI : forall m : M, Decidable (m != 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m

Depends on / 依赖: Classical, Classical.decPred, DFinsupp, DFinsupp.toFinsupp_single, Decidable, decPred, toFinsupp_single
-/
theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m :=
  letI : forall m : M, Decidable (m != 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m

/--
theorem `lmap_finsuppLEquivDirectSum_eq` / 定理 `lmap_finsuppLEquivDirectSum_eq`

English:
theorem lmap_finsuppLEquivDirectSum_eq
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: by
  ext i
  rfl

中文:
定理 lmap_finsuppLEquivDirectSum_eq
  结论: {N : 类型} [加法交换幺半群 N] [模 R N]
  证明: by
  ext i
  rfl
-/
theorem lmap_finsuppLEquivDirectSum_eq {N : Type*} [AddCommMonoid N] [Module R N]
    (ε : M ->ₗ[R] N) (m : ι ->₀ M) :
    (lmap fun _ => ε) ((finsuppLEquivDirectSum R M ι) m) =
      (finsuppLEquivDirectSum R N ι) (m.mapRange ⇑ε ε.map_zero) := by
  ext i
  rfl

end finsuppLequivDirectSum
