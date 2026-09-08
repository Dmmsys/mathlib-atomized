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

/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
/-
**finsuppLEquivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppLEquivDirectSum : (ι ->₀ M) ≃ₗ[R] ⨁ _ : ι, M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finitely supported functions `ι →₀ M` are in linear equivalence with the dir
ect sum of
copies of M indexed by ι.
-/
def finsuppLEquivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ _ : ι, M :=
  haveI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDFinsupp R

@[simp]
/-
**finsuppLEquivDirectSum_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppLEquivDirectSum_single (i : ι) (m : M) : finsuppLEquivDirectSum R M
 ι (Finsupp.single i m) = DirectSum.lof R ι _ i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
-/
theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.toDFinsupp_single i m

@[simp]
/-
**finsuppLEquivDirectSum_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppLEquivDirectSum_apply (m : ι ->₀ M) (i : ι) : finsuppLEquivDirectSu
m R M ι m i = m i
参数：m : ι ->₀ M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsuppLEquivDirectSum_apply (m : ι →₀ M) (i : ι) :
    finsuppLEquivDirectSum R M ι m i = m i := by
  rfl

@[simp]
/-
**finsuppLEquivDirectSum_symm_lof** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) : (finsuppLEquivDirectSum 
R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
-/
theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m :=
  letI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m
/-
**lmap_finsuppLEquivDirectSum_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lmap_finsuppLEquivDirectSum_eq {N : Type*} [AddCommMonoid N] [Module R N] 
(ε : M ->ₗ[R] N) (m : ι ->₀ M) : (lmap fun _ => ε) ((finsuppLEquivDirectSum R M 
ι) m) = (finsuppLEquivDirectSum R N ι) (m.mapRange ⇑ε ε.map_zero)
参数：ε : M ->ₗ[R] N；m : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem lmap_finsuppLEquivDirectSum_eq {N : Type*} [AddCommMonoid N] [Module R N]
    (ε : M →ₗ[R] N) (m : ι →₀ M) :
    (lmap fun _ ↦ ε) ((finsuppLEquivDirectSum R M ι) m) =
      (finsuppLEquivDirectSum R N ι) (m.mapRange ⇑ε ε.map_zero) := by
  ext i
  rfl

end finsuppLequivDirectSum

