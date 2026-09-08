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

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →+* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.distribMulActionLeft`.
-/
/-
**Function.Surjective.moduleLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid
 M] [Module R M] [Semiring S] [SMul S M] (f : R ->+* S) (hf : Function.Surjectiv
e f) (hsmul : forall (c) (x : M), f c • x = c • x) : Module S M
参数：f : R ->+* S；hf : Function.Surjective f；hsmul : forall (c) (x : M), f c • x =
 c • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Push forward the action of `R` on `M` along a compatible surjective map `f : R →
+* S`.

See also `Function.Surjective.mulActionLeft` and `Function.Surjective.distribMul
ActionLeft`.
-/
abbrev Function.Surjective.moduleLeft {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring S] [SMul S M] (f : R →+* S) (hf : Function.Surjective f)
    (hsmul : ∀ (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with
    zero_smul := fun x => by rw [← f.map_zero, hsmul, zero_smul]
    add_smul := hf.forall₂.mpr fun a b x => by simp only [← f.map_add, hsmul, add_smul] }

variable {R} (M)

/-- Compose a `Module` with a `RingHom`, with action `f s • m`.

See note [reducible non-instances]. -/
/-
**Module.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Module.compHom [Semiring S] (f : S ->+* R) : Module S M
参数：f : S ->+* R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a `Module` with a `RingHom`, with action `f s • m`.

See note [reducible non-instances].
-/
abbrev Module.compHom [Semiring S] (f : S →+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S →* R) with
    -- Porting note: the `show f (r + s) • x = f r • x + f s • x` wasn't needed in mathlib3.
    -- Somehow, now that `SMul` is heterogeneous, it can't unfold earlier fields of a definition for
    -- use in later fields.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Heterogeneous.20scalar.20multiplication
    -- TODO(jmc): there should be a rw-lemma `smul_comp` close to `SMulZeroClass.compFun`
    add_smul := fun r s x => show f (r + s) • x = f r • x + f s • x by simp [add_smul] }

end AddCommMonoid

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`.
See note [reducible non-instances]. -/
/-
**RingHom.toModule** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：RingHom.toModule [Semiring R] [Semiring S] (f : R ->+* S) : Module R S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x
`.
See note [reducible non-instances].
-/
abbrev RingHom.toModule [Semiring R] [Semiring S] (f : R →+* S) : Module R S :=
  Module.compHom S f
/-
**RingHom.toModule_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.toModule_smul [Semiring R] [Semiring S] (f : R ->+* S) (x : R) (y 
: S) : letI
参数：f : R ->+* S；x : R；y : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.toModule_smul [Semiring R] [Semiring S] (f : R →+* S) (x : R) (y : S) :
    letI := f.toModule
    x • y = f x * y :=
  rfl

/-- If the module action of `R` on `S` is compatible with multiplication on `S`, then
`fun x ↦ x • 1` is a ring homomorphism from `R` to `S`.

This is the `RingHom` version of `MonoidHom.smulOneHom`.

When `R` is commutative, usually `algebraMap` should be preferred. -/
/-
**RingHom.smulOneHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring R] → [inst_1 : No
nAssocSemiring S] → [inst_2 : _root_.Module R S] → [IsScalarTower R S S] → R →+*
 S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the module action of `R` on `S` is compatible with multiplication on `S`, the
n
`fun x ↦ x • 1` is a ring homomorphism from `R` to `S`.

This is the `RingHom` version of `MonoidHom.smulOneHom`.

When `R` is commutative, usually `algebraMap` should be preferred.
-/
@[simps!] def RingHom.smulOneHom
    [Semiring R] [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] : R →+* S where
  __ := MonoidHom.smulOneHom
  map_zero' := zero_smul R 1
  map_add' := (add_smul · · 1)

/-- A homomorphism between semirings R and S can be equivalently specified by an R-module
/-
**on** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on S such that S/S/R is a scalar tower. -/
/-
**ringHomEquivModuleIsScalarTower** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] : (R ->+* S) ≃ {
_inst : Module R S // IsScalarTower R S S} where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism between semirings R and S can be equivalently specified by an R-m
odule
structure on S such that S/S/R is a scalar tower.
-/
def ringHomEquivModuleIsScalarTower [Semiring R] [Semiring S] :
    (R →+* S) ≃ {_inst : Module R S // IsScalarTower R S S} where
  toFun f := ⟨Module.compHom S f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ RingHom.smulOneHom
  left_inv f := RingHom.ext fun r ↦ mul_one (f r)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| Module.ext <| funext₂ <| smul_one_smul S
