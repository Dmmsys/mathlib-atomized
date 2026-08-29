/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Bimodules

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : Module (R ⊗[ℕ] Sᵐᵒᵖ) M := TensorProduct.Algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `Module`s and most of their properties follow from the
theory of `Module`s. In particular a two-sided Submodule of a bimodule is simply a term of type
`Submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

* `Subbimodule.mk`
* `Subbimodule.smul_mem`
* `Subbimodule.smul_mem'`
* `Subbimodule.toSubmodule`
* `Subbimodule.toSubmodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[Module S M] [SMulCommClass R S M]` rather than `[Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `Submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/

@[expose] public section


open TensorProduct

attribute [local instance] TensorProduct.Algebra.module

namespace Subbimodule

section Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]
variable [SMulCommClass A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChange`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (p : AddSubmonoid M) (hA : forall (a : A) {m : M}, m in p -> a • m in p)
  body: { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simp only [zero_smul, SetLike.mem_coe, zero_mem])
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using! hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] 

中文:
定义 mk
  签名: (p : AddSubmonoid M) (hA : 对任意 (a : A) {m : M}, m in p -> a • m in p)
  定义体: { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simp only [zero_smul, SetLike.mem_coe, zero_mem])
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using! hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] 

Depends on / 依赖: Algebra, SetLike, SetLike.mem_coe, TensorProduct, TensorProduct.Algebra.smul_def, TensorProduct.induction_on, add_mem, add_smul, carrier, induction_on, mem_coe, p.add_mem, smul_def, smul_mem, zero_mem, zero_smul
-/
def mk (p : AddSubmonoid M) (hA : forall (a : A) {m : M}, m in p -> a • m in p)
    (hB : forall (b : B) {m : M}, m in p -> b • m in p) : Submodule (A otimes[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simp only [zero_smul, SetLike.mem_coe, zero_mem])
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using! hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] using! p.add_mem (hz hm) (hw hm) }

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: (p : Submodule (A otimes[R] B) M) (a : A) {m : M} (hm : m in p)
  statement: a • m in p
  proof: by
  suffices a • m = a otimesₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

中文:
定理 smul_mem
  条件: (p : Submodule (A otimes[R] B) M) (a : A) {m : M} (hm : m in p)
  结论: a • m in p
  证明: by
  suffices a • m = a otimesₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

Depends on / 依赖: Algebra, TensorProduct, TensorProduct.Algebra.smul_def, p.smul_mem, smul_def, smul_mem, this.symm
-/
theorem smul_mem (p : Submodule (A otimes[R] B) M) (a : A) {m : M} (hm : m in p) : a • m in p := by
  suffices a • m = a otimesₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

/--
theorem `smul_mem'` / 定理 `smul_mem'`

English:
theorem smul_mem'
  given: (p : Submodule (A otimes[R] B) M) (b : B) {m : M} (hm : m in p)
  statement: b • m in p
  proof: by
  suffices b • m = (1 : A) otimesₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

中文:
定理 smul_mem'
  条件: (p : Submodule (A otimes[R] B) M) (b : B) {m : M} (hm : m in p)
  结论: b • m in p
  证明: by
  suffices b • m = (1 : A) otimesₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

Depends on / 依赖: Algebra, TensorProduct, TensorProduct.Algebra.smul_def, p.smul_mem, smul_def, smul_mem, this.symm
-/
theorem smul_mem' (p : Submodule (A otimes[R] B) M) (b : B) {m : M} (hm : m in p) : b • m in p := by
  suffices b • m = (1 : A) otimesₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

/-- If `A` and `B` are also `Algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps!]
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
  body: mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

中文:
定义 baseChange
  签名: (S : 类型) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
  定义体: mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

Depends on / 依赖: p.toAddSubmonoid, smul_mem, toAddSubmonoid
-/
def baseChange (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
    [IsScalarTower S A M] [IsScalarTower S B M] (p : Submodule (A otimes[R] B) M) :
    Submodule (A otimes[S] B) M :=
  mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `A`. -/
@[simps]
/--
Definition of `toSubmodule` / `toSubmodule` 的定义

English:
definition toSubmodule
  signature: (p : Submodule (A otimes[R] B) M)
  body: { p with
    carrier := p
    smul_mem' := smul_mem p }

中文:
定义 toSubmodule
  签名: (p : Submodule (A otimes[R] B) M)
  定义体: { p with
    carrier := p
    smul_mem' := smul_mem p }

Depends on / 依赖: carrier, smul_mem
-/
def toSubmodule (p : Submodule (A otimes[R] B) M) : Submodule A M :=
  { p with
    carrier := p
    smul_mem' := smul_mem p }

/-- Forgetting the `A` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `B`. -/
@[simps]
/--
Definition of `toSubmodule'` / `toSubmodule'` 的定义

English:
definition toSubmodule'
  signature: (p : Submodule (A otimes[R] B) M)
  body: { p with
    carrier := p
    smul_mem' := smul_mem' p }

中文:
定义 toSubmodule'
  签名: (p : Submodule (A otimes[R] B) M)
  定义体: { p with
    carrier := p
    smul_mem' := smul_mem' p }

Depends on / 依赖: carrier, smul_mem
-/
def toSubmodule' (p : Submodule (A otimes[R] B) M) : Submodule B M :=
  { p with
    carrier := p
    smul_mem' := smul_mem' p }

end Algebra

section Ring

variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module S M] [SMulCommClass R S M]

/-- A `Submodule` over `R ⊗[ℕ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps!]
/--
Definition of `toSubbimoduleInt` / `toSubbimoduleInt` 的定义

English:
definition toSubbimoduleInt
  signature: (p : Submodule (R otimes[Nat] S) M)
  body: baseChange Int p

中文:
定义 toSubbimoduleInt
  签名: (p : Submodule (R otimes[自然数] S) M)
  定义体: baseChange Int p

Depends on / 依赖: baseChange
-/
def toSubbimoduleInt (p : Submodule (R otimes[Nat] S) M) : Submodule (R otimes[Int] S) M :=
  baseChange Int p

/-- A `Submodule` over `R ⊗[ℤ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps!]
/--
Definition of `toSubbimoduleNat` / `toSubbimoduleNat` 的定义

English:
definition toSubbimoduleNat
  signature: (p : Submodule (R otimes[Int] S) M)
  body: baseChange Nat p

中文:
定义 toSubbimoduleNat
  签名: (p : Submodule (R otimes[整数] S) M)
  定义体: baseChange Nat p

Depends on / 依赖: baseChange
-/
def toSubbimoduleNat (p : Submodule (R otimes[Int] S) M) : Submodule (R otimes[Nat] S) M :=
  baseChange Nat p

end Ring

end Subbimodule
