/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-!
# Results on `DualNumber R` related to the norm

These are just restatements of similar statements about `TrivSqZeroExt R M`.

## Main results

* `exp_eps`

-/

public section

open NormedSpace -- For `NormedSpace.exp`.

namespace DualNumber

open TrivSqZeroExt

variable {R : Type*}
variable [CommRing R] [Algebra ℚ R]
variable [UniformSpace R] [IsTopologicalRing R] [T2Space R]

@[simp]
/-
**DualNumber.exp_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：exp_eps : exp (eps : DualNumber R) = 1 + eps
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.exp_inr`：exp_inr (m : M) : exp (inr m : tsze R M) = 1 + in
r m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
theorem exp_eps : exp (eps : DualNumber R) = 1 + eps :=
  exp_inr _

@[simp]
/-
**DualNumber.exp_smul_eps** 是 Mathlib 中的一个定理，位于命名空间 `DualNumber`。
形式化陈述：exp_smul_eps (r : R) : exp (r • eps : DualNumber R) = 1 + r • eps
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TrivSqZeroExt.instIsTopologicalRingOfIsTopologicalAddGroupOfContinuousSM
ulMulOpposite`：∀ {R : Type u_3} {M : Type u_4} [inst : TopologicalSpace R] [inst
_1 : TopologicalSpace M] [inst_2 : Ring R]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DualNumber.eps.eq_1`：∀ {R : Type u_1} [inst : Zero R] [inst_1 : One R], 
DualNumber.eps = TrivSqZeroExt.inr 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S M]
 (r : S) (m : M) : (inr (r • m) : tsze R M) = r • inr m
· 使用定理 `TrivSqZeroExt.exp_inr`：exp_inr (m : M) : exp (inr m : tsze R M) = 1 + in
r m
-/
theorem exp_smul_eps (r : R) : exp (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]

end DualNumber

