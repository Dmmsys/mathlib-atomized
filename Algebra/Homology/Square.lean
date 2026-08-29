/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

This file is the bundled counterpart of `Mathlib/Algebra/Homology/CommSq.lean`.
The same results are obtained here for squares `sq : Square C` where
`C` is an additive category.

-/

@[expose] public section
namespace CategoryTheory

open Category Limits

namespace Square

variable {C : Type*} [Category* C] [Preadditive C]
  (sq : Square C) [HasBinaryBiproduct sq.X₂ sq.X₃]

/--
Definition of `cokernelCofork` / `cokernelCofork` 的定义

English:
abbreviation cokernelCofork
  signature: :
  body: CokernelCofork.ofπ (biprod.desc sq.f₂₄ sq.f₃₄) (by simp [sq.fac])

中文:
缩写 cokernelCofork
  签名: :
  定义体: CokernelCofork.ofπ (biprod.desc sq.f₂₄ sq.f₃₄) (by simp [sq.fac])

Depends on / 依赖: CokernelCofork, CokernelCofork.of, biprod, biprod.desc, sq.f, sq.fac
-/
noncomputable abbrev cokernelCofork :
    CokernelCofork (biprod.lift sq.f₁₂ (-sq.f₁₃)) :=
  CokernelCofork.ofπ (biprod.desc sq.f₂₄ sq.f₃₄) (by simp [sq.fac])

/--
Definition of `isPushoutEquivIsColimitCokernelCofork` / `isPushoutEquivIsColimitCokernelCofork` 的定义

English:
definition isPushoutEquivIsColimitCokernelCofork
  signature: :
  body: Equiv.trans
    { toFun := fun h => h.isColimit
      invFun := fun h => IsPushout.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isColimitEquivIsColimitCokernelCofork

中文:
定义 isPushoutEquivIsColimitCokernelCofork
  签名: :
  定义体: Equiv.trans
    { toFun := fun h => h.isColimit
      invFun := fun h => IsPushout.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isColimitEquivIsColimitCokernelCofork

Depends on / 依赖: Equiv.trans, IsPushout, IsPushout.mk, Subsingleton, Subsingleton.elim, commSq, h.isColimit, invFun, isColimit, isColimitEquivIsColimitCokernelCofork, right_inv, sq.commSq.isColimitEquivIsColimitCokernelCofork
-/
noncomputable def isPushoutEquivIsColimitCokernelCofork :
    sq.IsPushout ≃ IsColimit sq.cokernelCofork :=
  Equiv.trans
    { toFun := fun h => h.isColimit
      invFun := fun h => IsPushout.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isColimitEquivIsColimitCokernelCofork

variable {sq} in
/--
Definition of `IsPushout.isColimitCokernelCofork` / `IsPushout.isColimitCokernelCofork` 的定义

English:
definition IsPushout.isColimitCokernelCofork
  signature: (h : sq.IsPushout)
  body: h.isColimitEquivIsColimitCokernelCofork h.isColimit

中文:
定义 是推出.isColimitCokernelCofork
  签名: (h : sq.是推出)
  定义体: h.isColimitEquivIsColimitCokernelCofork h.isColimit
-/
noncomputable def IsPushout.isColimitCokernelCofork (h : sq.IsPushout) :
    IsColimit sq.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

/--
Definition of `kernelFork` / `kernelFork` 的定义

English:
abbreviation kernelFork
  signature: :
  body: KernelFork.ofι (biprod.lift sq.f₁₂ sq.f₁₃) (by simp [sq.fac])

中文:
缩写 kernelFork
  签名: :
  定义体: KernelFork.ofι (biprod.lift sq.f₁₂ sq.f₁₃) (by simp [sq.fac])

Depends on / 依赖: KernelFork, KernelFork.of, biprod, biprod.lift, sq.f, sq.fac
-/
noncomputable abbrev kernelFork :
    KernelFork (biprod.desc sq.f₂₄ (-sq.f₃₄)) :=
  KernelFork.ofι (biprod.lift sq.f₁₂ sq.f₁₃) (by simp [sq.fac])

/--
Definition of `isPullbackEquivIsLimitKernelFork` / `isPullbackEquivIsLimitKernelFork` 的定义

English:
definition isPullbackEquivIsLimitKernelFork
  signature: :
  body: Equiv.trans
    { toFun := fun h => h.isLimit
      invFun := fun h => IsPullback.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isLimitEquivIsLimitKernelFork

中文:
定义 isPullbackEquivIsLimitKernelFork
  签名: :
  定义体: Equiv.trans
    { toFun := fun h => h.isLimit
      invFun := fun h => IsPullback.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isLimitEquivIsLimitKernelFork

Depends on / 依赖: Equiv.trans, IsPullback, IsPullback.mk, Subsingleton, Subsingleton.elim, commSq, h.isLimit, invFun, isLimit, isLimitEquivIsLimitKernelFork, right_inv, sq.commSq.isLimitEquivIsLimitKernelFork
-/
noncomputable def isPullbackEquivIsLimitKernelFork :
    sq.IsPullback ≃ IsLimit sq.kernelFork :=
  Equiv.trans
    { toFun := fun h => h.isLimit
      invFun := fun h => IsPullback.mk _ h
      right_inv := fun _ => Subsingleton.elim _ _ }
    sq.commSq.isLimitEquivIsLimitKernelFork

variable {sq} in
/--
Definition of `IsPullback.isLimitKernelFork` / `IsPullback.isLimitKernelFork` 的定义

English:
definition IsPullback.isLimitKernelFork
  signature: (h : sq.IsPullback)
  body: h.isLimitEquivIsLimitKernelFork h.isLimit

中文:
定义 是拉回.isLimitKernelFork
  签名: (h : sq.是拉回)
  定义体: h.isLimitEquivIsLimitKernelFork h.isLimit
-/
noncomputable def IsPullback.isLimitKernelFork (h : sq.IsPullback) :
    IsLimit sq.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

end Square

end CategoryTheory
