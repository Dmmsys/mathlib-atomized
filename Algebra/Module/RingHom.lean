/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Composing modules with a ring hom

## Main definitions

* `Module.compHom`: compose a `Module` with a `RingHom`, with action `f s • m`.
* `RingHom.toModule`: a `RingHom` defines a module structure by `r • x = f r * x`.

## Tags

semimodule, module, vector space
-/

@[expose] public section

assert_not_exists Field Invertible Multiset Pi.single_smul₀ Set.indicator

open Function Set

universe u v

variable {R S M M₂ : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

variable (R)

/--
Definition of `Function.Surjective.moduleLeft` / `Function.Surjective.moduleLeft` 的定义

English:
abbreviation Function.Surjective.moduleLeft
  signature: {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  body: { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }

中文:
缩写 函数.满射.moduleLeft
  签名: {R S M : 类型} [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }

Depends on / 依赖: add_smul, distribMulActionLeft, f.map_add, f.map_zero, f.toMonoidHom, hf.distribMulActionLeft, hf.forall, map_add, map_zero, toMonoidHom, zero_smul
-/
abbrev Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [SMul S M] (f : R ->+* S) (hf : Function.Surjective f)
    (hsmul : forall (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }

variable {R} (M)

/--
Definition of `Module.compHom` / `Module.compHom` 的定义

English:
abbreviation Module.compHom
  signature: [Semiring S] (f : S ->+* R)
  body: { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S ->* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- 

中文:
缩写 模.compHom
  签名: [半环 S] (f : S ->+* R)
  定义体: { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S ->* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- 

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, MulActionWithZero, MulActionWithZero.compHom, compHom, f.toMonoidWithZeroHom, toMonoidWithZeroHom
-/
abbrev Module.compHom [Semiring S] (f : S ->+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S ->* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields. See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    -- TODO(jmc): there should be a rw-lemma `smul_comp` close to `SMulZeroClass.compFun`
    add_smul := fun r s x => show f (r + s) • x = f r • x + f s • x by simp [add_smul] }

end AddCommMonoid

/--
Definition of `RingHom.toModule` / `RingHom.toModule` 的定义

English:
abbreviation RingHom.toModule
  signature: [Semiring R] [Semiring S] (f : R ->+* S)
  body: Module.compHom S f

中文:
缩写 环态射.toModule
  签名: [半环 R] [半环 S] (f : R ->+* S)
  定义体: Module.compHom S f

Depends on / 依赖: Module, Module.compHom, compHom
-/
abbrev RingHom.toModule [Semiring R] [Semiring S] (f : R ->+* S) : Module R S :=
  Module.compHom S f

/--
lemma `RingHom.toModule_smul` / 引理 `RingHom.toModule_smul`

English:
lemma RingHom.toModule_smul
  given: [Semiring R] [Semiring S] (f : R ->+* S) (x : R) (y : S)
  proof: f.toModule
    x • y = f x * y :=
  rfl

中文:
引理 环态射.toModule_smul
  条件: [半环 R] [半环 S] (f : R ->+* S) (x : R) (y : S)
  证明: f.toModule
    x • y = f x * y :=
  rfl

Depends on / 依赖: f.toModule, toModule
-/
lemma RingHom.toModule_smul [Semiring R] [Semiring S] (f : R ->+* S) (x : R) (y : S) :
    letI := f.toModule
    x • y = f x * y :=
  rfl

/--
Definition of `RingHom.smulOneHom` / `RingHom.smulOneHom` 的定义

English:
definition RingHom.smulOneHom
  body: MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)

中文:
定义 环态射.smulOneHom
  定义体: MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)
-/
@[simps!] def RingHom.smulOneHom
    [Semiring R] [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] : R ->+* S where
  __ := MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)

/--
Definition of `ringHomEquivModuleIsScalarTower` / `ringHomEquivModuleIsScalarTower` 的定义

English:
definition ringHomEquivModuleIsScalarTower
  signature: [Semiring R] [Semiring S]
  body: ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ => RingHom.smulOneHom
  left_inv f := RingHom.ext fun r => mul_one (f r)
right_inv := fun ⟨_, _⟩ => Subtype.ext Module.ext funext₂ smul_one_smul S

中文:
定义 ringHomEquivModuleIsScalarTower
  签名: [半环 R] [半环 S]
  定义体: ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ => RingHom.smulOneHom
  left_inv f := RingHom.ext fun r => mul_one (f r)
right_inv := fun ⟨_, _⟩ => Subtype.ext Module.ext funext₂ smul_one_smul S

Depends on / 依赖: Module, Module.compHom, SMul.comp.isScalarTower, compHom, isScalarTower
-/
def ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] :
    (R ->+* S) ≃ {_inst : Module R S // IsScalarTower R S S} where
  toFun f := ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ => RingHom.smulOneHom
  left_inv f := RingHom.ext fun r => mul_one (f r)
right_inv := fun ⟨_, _⟩ => Subtype.ext Module.ext funext₂ smul_one_smul S
