/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

universe v
variable {R α β : Type*} [CommSemiring R]

namespace Equiv
variable (e : α ≃ β)

-- See note [instance transfer via equivalence]
variable (R) in
/--
Definition of `algebra` / `algebra` 的定义

English:
abbreviation algebra
  signature: (e : α ≃ β) [Semiring β]
  body: Equiv.semiring e
    forall [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.invFun (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (alg

中文:
缩写 algebra
  签名: (e : α ≃ β) [半环 β]
  定义体: Equiv.semiring e
    forall [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.invFun (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (alg
-/
protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
    forall [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.invFun (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (algebraMap R β r)) * e x)) =
          e.symm (e x * e (e.symm (algebraMap R β r))) by
        simp [Algebra.commutes]
    smul_def' r x :=
      show e.symm (r • e x) = e.symm (e (e.symm (algebraMap R β r)) * e x) by
        simp [Algebra.smul_def] }

/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  given: (e : α ≃ β) [Semiring β] [Algebra R β] (r : R)
  proof: Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

中文:
引理 algebraMap_def
  条件: (e : α ≃ β) [半环 β] [代数 R β] (r : R)
  证明: Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

Depends on / 依赖: Equiv.semiring, semiring
-/
lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

variable (R) in
/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (e : α ≃ β) [Semiring β] [Algebra R β]
  body: Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_ap

中文:
定义 algEquiv
  签名: (e : α ≃ β) [半环 β] [代数 R β]
  定义体: Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_ap

Depends on / 依赖: Equiv.semiring, semiring
-/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }

@[simp]
/--
theorem `algEquiv_apply` / 定理 `algEquiv_apply`

English:
theorem algEquiv_apply
  given: (e : α ≃ β) [Semiring β] [Algebra R β] (a : α)
  statement: (algEquiv R e) a = e a
  proof: rfl

中文:
定理 algEquiv_apply
  条件: (e : α ≃ β) [半环 β] [代数 R β] (a : α)
  结论: (algEquiv R e) a = e a
  证明: rfl
-/
theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv R e) a = e a :=
  rfl

/--
theorem `algEquiv_symm_apply` / 定理 `algEquiv_symm_apply`

English:
theorem algEquiv_symm_apply
  given: (e : α ≃ β) [Semiring β] [Algebra R β] (b : β)
  statement: by
  proof: Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

中文:
定理 algEquiv_symm_apply
  条件: (e : α ≃ β) [半环 β] [代数 R β] (b : β)
  结论: by
  证明: Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

Depends on / 依赖: Equiv.semiring, semiring
-/
theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

end Equiv
