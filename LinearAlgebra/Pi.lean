/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `LinearMap.ker`.

## Main definitions

- pi types in the codomain:
  - `LinearMap.pi`
  - `LinearMap.single`
- pi types in the domain:
  - `LinearMap.proj`
  - `LinearMap.diag`

-/

@[expose] public section


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι -> Type i} [(i : ι) -> AddCommMonoid (φ i)] [(i : ι) -> Module R (φ i)]

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  body: { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]

中文:
定义 pi
  签名: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  定义体: { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]

Depends on / 依赖: AddHom, AddHom.pi, map_smul, toAddHom
-/
def pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : M₂ ->ₗ[R] (i : ι) -> φ i :=
  { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]
/--
theorem `pi_apply` / 定理 `pi_apply`

English:
theorem pi_apply
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i : ι)
  statement: pi f c i = f i c
  proof: rfl

中文:
定理 pi_apply
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i : ι)
  结论: pi f c i = f i c
  证明: rfl
-/
theorem pi_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl

/--
theorem `ker_pi` / 定理 `ker_pi`

English:
theorem ker_pi
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  statement: ker (pi f) = ⨅ i : ι, ker (f i)
  proof: by
  ext c; simp [funext_iff]

中文:
定理 ker_pi
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  结论: ker (pi f) = ⨅ i : ι, ker (f i)
  证明: by
  ext c; simp [funext_iff]

Depends on / 依赖: funext_iff
-/
theorem ker_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c; simp [funext_iff]

/--
theorem `pi_eq_zero` / 定理 `pi_eq_zero`

English:
theorem pi_eq_zero
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  statement: pi f = 0 ↔ forall i, f i = 0
  proof: by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

中文:
定理 pi_eq_zero
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i)
  结论: pi f = 0 ↔ 对任意 i, f i = 0
  证明: by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, funext_iff, pi_apply
-/
theorem pi_eq_zero (f : (i : ι) -> M₂ ->ₗ[R] φ i) : pi f = 0 ↔ forall i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

/--
theorem `pi_zero` / 定理 `pi_zero`

English:
theorem pi_zero
  statement: pi (fun _ => 0 : (i : ι) -> M₂ ->ₗ[R] φ i) = 0
  proof: by ext; rfl

中文:
定理 pi_zero
  结论: pi (fun _ => 0 : (i : ι) -> M₂ ->ₗ[R] φ i) = 0
  证明: by ext; rfl
-/
theorem pi_zero : pi (fun _ => 0 : (i : ι) -> M₂ ->ₗ[R] φ i) = 0 := by ext; rfl

/--
theorem `pi_comp` / 定理 `pi_comp`

English:
theorem pi_comp
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (g : M₃ ->ₗ[R] M₂)
  proof: rfl

中文:
定理 pi_comp
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (g : M₃ ->ₗ[R] M₂)
  证明: rfl
-/
theorem pi_comp (f : (i : ι) -> M₂ ->ₗ[R] φ i) (g : M₃ ->ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: : M₂ ->ₗ[R] (ι -> M₂)
  body: pi fun _ => .id

中文:
定义 const
  签名: : M₂ ->ₗ[R] (ι -> M₂)
  定义体: pi fun _ => .id
-/
def const : M₂ ->ₗ[R] (ι -> M₂) := pi fun _ => .id

/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: (x : M₂)
  statement: LinearMap.const (R := R) x = Function.const ι x
  proof: rfl

中文:
引理 const_apply
  条件: (x : M₂)
  结论: 线性映射.const (R := R) x = 函数.const ι x
  证明: rfl
-/
@[simp] lemma const_apply (x : M₂) : LinearMap.const (R := R) x = Function.const ι x := rfl

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : ι)
  body: Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 proj
  签名: (i : ι)
  定义体: Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: Function, Function.eval
-/
def proj (i : ι) : ((i : ι) -> φ i) ->ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `coe_proj` / 定理 `coe_proj`

English:
theorem coe_proj
  given: (i : ι)
  statement: ⇑(proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) = Function.eval i
  proof: rfl

@[simp]

中文:
定理 coe_proj
  条件: (i : ι)
  结论: ⇑(proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) = 函数.eval i
  证明: rfl

@[simp]
-/
theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) = Function.eval i :=
  rfl

@[simp]
/--
theorem `toAddMonoidHom_proj` / 定理 `toAddMonoidHom_proj`

English:
theorem toAddMonoidHom_proj
  given: (i : ι)
  statement: (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i
  proof: rfl

中文:
定理 toAddMonoidHom_proj
  条件: (i : ι)
  结论: (proj i).toAddMonoidHom (R := R) = 依赖函数类型.evalAddMonoidHom φ i
  证明: rfl

Depends on / 依赖: Pi.evalAddMonoidHom, evalAddMonoidHom
-/
theorem toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i :=
  rfl

/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (i : ι) (b : (i : ι) -> φ i)
  statement: (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) b = b i
  proof: rfl

@[simp]

中文:
定理 proj_apply
  条件: (i : ι) (b : (i : ι) -> φ i)
  结论: (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) b = b i
  证明: rfl

@[simp]
-/
theorem proj_apply (i : ι) (b : (i : ι) -> φ i) : (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) b = b i :=
  rfl

@[simp]
/--
theorem `proj_pi` / 定理 `proj_pi`

English:
theorem proj_pi
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (i : ι)
  statement: (proj i).comp (pi f) = f i
  proof: rfl

@[simp]

中文:
定理 proj_pi
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (i : ι)
  结论: (proj i).comp (pi f) = f i
  证明: rfl

@[simp]
-/
theorem proj_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
/--
theorem `pi_proj` / 定理 `pi_proj`

English:
theorem pi_proj
  statement: pi proj = LinearMap.id (R := R) (M := forall i, φ i)
  proof: rfl

@[simp]

中文:
定理 pi_proj
  结论: pi proj = 线性映射.id (R := R) (M := 对任意 i, φ i)
  证明: rfl

@[simp]
-/
theorem pi_proj : pi proj = LinearMap.id (R := R) (M := forall i, φ i) := rfl

@[simp]
/--
theorem `pi_proj_comp` / 定理 `pi_proj_comp`

English:
theorem pi_proj_comp
  given: (f : M₂ ->ₗ[R] forall i, φ i)
  statement: pi (proj · ∘ₗ f) = f
  proof: rfl

中文:
定理 pi_proj_comp
  条件: (f : M₂ ->ₗ[R] 对任意 i, φ i)
  结论: pi (proj · ∘ₗ f) = f
  证明: rfl
-/
theorem pi_proj_comp (f : M₂ ->ₗ[R] forall i, φ i) : pi (proj · ∘ₗ f) = f := rfl

/--
theorem `proj_surjective` / 定理 `proj_surjective`

English:
theorem proj_surjective
  given: (i : ι)
  statement: Surjective (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i)
  proof: surjective_eval i

中文:
定理 proj_surjective
  条件: (i : ι)
  结论: 满射 (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i)
  证明: surjective_eval i

Depends on / 依赖: surjective_eval
-/
theorem proj_surjective (i : ι) : Surjective (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) :=
  surjective_eval i

/--
Definition of `_root_.LinearEquiv.linearMapPi` / `_root_.LinearEquiv.linearMapPi` 的定义

English:
definition _root_.LinearEquiv.linearMapPi
  signature: (S) [Semiring S] [(i : ι) -> Module S (φ i)]
  body: pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f i := proj i ∘ₗ f
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 _root_.线性等价.linearMapPi
  签名: (S) [半环 S] [(i : ι) -> 模 S (φ i)]
  定义体: pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f i := proj i ∘ₗ f
  left_inv _ := rfl
  right_inv _ := rfl
-/
@[simps] def _root_.LinearEquiv.linearMapPi (S) [Semiring S] [(i : ι) -> Module S (φ i)]
    [forall i, SMulCommClass R S (φ i)] : (Π i, M₂ ->ₗ[R] φ i) ≃ₗ[S] M₂ ->ₗ[R] Π i, φ i where
  toFun := pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f i := proj i ∘ₗ f
  left_inv _ := rfl
  right_inv _ := rfl

/--
theorem `iInf_ker_proj` / 定理 `iInf_ker_proj`

English:
theorem iInf_ker_proj
  statement: (⨅ i, ker (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) :
  proof: bot_unique
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)

中文:
定理 iInf_ker_proj
  结论: (⨅ i, ker (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) :
  证明: bot_unique
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)

Depends on / 依赖: SetLike, SetLike.le_def, bot_unique, le_def, mem_bot, mem_iInf, mem_ker, proj_apply
-/
theorem iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) :
    Submodule R ((i : ι) -> φ i)) = ⊥ :=
bot_unique
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)

/--
Instance `CompatibleSMul.pi` / 实例 `CompatibleSMul.pi`

English:
instance CompatibleSMul.pi
  signature: (R S M N ι : Type*) [Semiring S]
  body: by ext i; apply ((LinearMap.proj i).comp f).map_smul_of_tower

中文:
实例 余mpatibleSMul.pi
  签名: (R S M N ι : 类型) [半环 S]
  定义体: by ext i; apply ((LinearMap.proj i).comp f).map_smul_of_tower

Depends on / 依赖: LinearMap, LinearMap.proj, map_smul_of_tower
-/
instance CompatibleSMul.pi (R S M N ι : Type*) [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [SMul R M] [SMul R N] [Module S M] [Module S N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι -> N) R S where
  map_smul f r m := by ext i; apply ((LinearMap.proj i).comp f).map_smul_of_tower

/--
Definition of `piMap` / `piMap` 的定义

English:
definition piMap
  signature: {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Module R (ψ i)]
  body: .pi fun i => f i ∘ₗ proj i

@[simp]

中文:
定义 piMap
  签名: {ψ : ι -> 类型} [对任意 i, 加法交换幺半群 (ψ i)] [对任意 i, 模 R (ψ i)]
  定义体: .pi fun i => f i ∘ₗ proj i

@[simp]
-/
def piMap {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Module R (ψ i)]
    (f : forall i, φ i ->ₗ[R] ψ i) : (forall i, φ i) ->ₗ[R] (forall i, ψ i) :=
  .pi fun i => f i ∘ₗ proj i

@[simp]
/--
theorem `coe_piMap` / 定理 `coe_piMap`

English:
theorem coe_piMap
  statement: {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Module R (ψ i)]
  proof: rfl

中文:
定理 coe_piMap
  结论: {ψ : ι -> 类型} [对任意 i, 加法交换幺半群 (ψ i)] [对任意 i, 模 R (ψ i)]
  证明: rfl
-/
theorem coe_piMap {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Module R (ψ i)]
    (f : forall i, φ i ->ₗ[R] ψ i) : ⇑(piMap f) = Pi.map fun i => f i :=
  rfl

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
/--
Definition of `compLeft` / `compLeft` 的定义

English:
definition compLeft
  signature: (f : M₂ ->ₗ[R] M₃) (I : Type*)
  body: { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }

中文:
定义 compLeft
  签名: (f : M₂ ->ₗ[R] M₃) (I : 类型)
  定义体: { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }
-/
protected def compLeft (f : M₂ ->ₗ[R] M₃) (I : Type*) : (I -> M₂) ->ₗ[R] I -> M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }

/--
theorem `apply_single` / 定理 `apply_single`

English:
theorem apply_single
  statement: [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) -> φ i ->ₗ[R] M)
  proof: Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

中文:
定理 apply_single
  结论: [加法交换幺半群 M] [模 R M] [DecidableEq ι] (f : (i : ι) -> φ i ->ₗ[R] M)
  证明: Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

Depends on / 依赖: Pi.apply_single, apply_single, map_zero
-/
theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) -> φ i ->ₗ[R] M)
    (i j : ι) (x : φ i) : f j (Pi.single i x j) = (Pi.single i (f i x) : ι -> M) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

variable (R φ)

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: [DecidableEq ι] (i : ι)
  body: { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }

中文:
定义 single
  签名: [DecidableEq ι] (i : ι)
  定义体: { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.single, Pi.single, Pi.single_smul, map_smul, single, single_smul
-/
def single [DecidableEq ι] (i : ι) : φ i ->ₗ[R] (i : ι) -> φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }

/--
lemma `single_apply` / 引理 `single_apply`

English:
lemma single_apply
  given: [DecidableEq ι] {i : ι} (v : φ i)
  proof: rfl

中文:
引理 single_apply
  条件: [DecidableEq ι] {i : ι} (v : φ i)
  证明: rfl
-/
lemma single_apply [DecidableEq ι] {i : ι} (v : φ i) :
    single R φ i v = Pi.single i v :=
  rfl

/--
lemma `sum_single_apply` / 引理 `sum_single_apply`

English:
lemma sum_single_apply
  given: [Fintype ι] [DecidableEq ι] (v : Π i, φ i)
  proof: by ext; simp

@[simp]

中文:
引理 sum_single_apply
  条件: [有限类型 ι] [DecidableEq ι] (v : Π i, φ i)
  证明: by ext; simp

@[simp]
-/
lemma sum_single_apply [Fintype ι] [DecidableEq ι] (v : Π i, φ i) :
    ∑ i, Pi.single i (v i) = v := by ext; simp

@[simp]
/--
theorem `coe_single` / 定理 `coe_single`

English:
theorem coe_single
  given: [DecidableEq ι] (i : ι)
  proof: rfl

中文:
定理 coe_single
  条件: [DecidableEq ι] (i : ι)
  证明: rfl
-/
theorem coe_single [DecidableEq ι] (i : ι) :
    ⇑(single R φ i : φ i ->ₗ[R] (i : ι) -> φ i) = Pi.single i :=
  rfl

variable [DecidableEq ι]

/--
theorem `proj_comp_single_same` / 定理 `proj_comp_single_same`

English:
theorem proj_comp_single_same
  given: (i : ι)
  statement: (proj i).comp (single R φ i) = id
  proof: LinearMap.ext Pi.single_eq_same i

中文:
定理 proj_comp_single_same
  条件: (i : ι)
  结论: (proj i).comp (single R φ i) = id
  证明: LinearMap.ext Pi.single_eq_same i

Depends on / 依赖: LinearMap, LinearMap.ext, Pi.single_eq_same, single_eq_same
-/
theorem proj_comp_single_same (i : ι) : (proj i).comp (single R φ i) = id :=
LinearMap.ext Pi.single_eq_same i

/--
theorem `proj_comp_single_ne` / 定理 `proj_comp_single_ne`

English:
theorem proj_comp_single_ne
  given: (i j : ι) (h : i != j)
  statement: (proj i).comp (single R φ j) = 0
  proof: LinearMap.ext Pi.single_eq_of_ne h

中文:
定理 proj_comp_single_ne
  条件: (i j : ι) (h : i != j)
  结论: (proj i).comp (single R φ j) = 0
  证明: LinearMap.ext Pi.single_eq_of_ne h

Depends on / 依赖: LinearMap, LinearMap.ext, Pi.single_eq_of_ne, single_eq_of_ne
-/
theorem proj_comp_single_ne (i j : ι) (h : i != j) : (proj i).comp (single R φ j) = 0 :=
LinearMap.ext Pi.single_eq_of_ne h

/--
theorem `iSup_range_single_le_iInf_ker_proj` / 定理 `iSup_range_single_le_iInf_ker_proj`

English:
theorem iSup_range_single_le_iInf_ker_proj
  given: (I J : Set ι) (h : Disjoint I J)
  proof: by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_comp_single_ne R φ j i]; rw [zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩

中文:
定理 iSup_range_single_le_iInf_ker_proj
  条件: (I J : 集合 ι) (h : Disjoint I J)
  证明: by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_comp_single_ne R φ j i]; rw [zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩

Depends on / 依赖: SetLike, SetLike.le_def, comap_iInf, eq_top_iff, h.le_bot, iSup_le, ker_comp, le_bot, le_def, mem_iInf, mem_ker, proj_comp_single_ne, range_le_iff_comap, zero_apply
-/
theorem iSup_range_single_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    ⨆ i in I, range (single R φ i) <= ⨅ i in J, ker (proj i : (forall i, φ i) ->ₗ[R] φ i) := by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_comp_single_ne R φ j i]; rw [zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩

/--
theorem `iInf_ker_proj_le_iSup_range_single` / 定理 `iInf_ker_proj_le_iSup_range_single`

English:
theorem iInf_ker_proj_le_iSup_range_single
  given: {I J : Set ι} (hI : I.Finite) (hIJ : Codisjoint I J)
  proof: by
  lift I to Finset ι using hI
  intro b hb
  simp only [mem_iInf, mem_ker, proj_apply] at hb
  rw [←
    show (∑ i in I]; rw [Pi.single i (b i)) = b by
      ext i
      rw [Finset.sum_apply]; rw [← Pi.single_eq_same i (b i)]
      refine Finset.sum_eq_single i (fun j _ ne => Pi.single_eq_of_ne n

中文:
定理 iInf_ker_proj_le_iSup_range_single
  条件: {I J : 集合 ι} (hI : I.有限) (hIJ : Codisjoint I J)
  证明: by
  lift I to Finset ι using hI
  intro b hb
  simp only [mem_iInf, mem_ker, proj_apply] at hb
  rw [←
    show (∑ i in I]; rw [Pi.single i (b i)) = b by
      ext i
      rw [Finset.sum_apply]; rw [← Pi.single_eq_same i (b i)]
      refine Finset.sum_eq_single i (fun j _ ne => Pi.single_eq_of_ne n

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_eq_single, Pi.single, Pi.single_eq_of_ne, Pi.single_eq_same, hIJ.top_le, mem_iInf, mem_ker, mem_range_self, ne.symm, proj_apply, resolve_left, single, single_eq_of_ne, single_eq_same, sum_apply, sum_eq_single, sum_mem_biSup, top_le
-/
theorem iInf_ker_proj_le_iSup_range_single {I J : Set ι} (hI : I.Finite) (hIJ : Codisjoint I J) :
    ⨅ i in J, ker (proj i : (forall i, φ i) ->ₗ[R] φ i) <= ⨆ i in I, range (single R φ i) := by
  lift I to Finset ι using hI
  intro b hb
  simp only [mem_iInf, mem_ker, proj_apply] at hb
  rw [←
    show (∑ i in I]; rw [Pi.single i (b i)) = b by
      ext i
      rw [Finset.sum_apply]; rw [← Pi.single_eq_same i (b i)]
      refine Finset.sum_eq_single i (fun j _ ne => Pi.single_eq_of_ne ne.symm _) ?_
      intro hiI
      rw [Pi.single_eq_same]
      exact hb _ ((hIJ.top_le trivial).resolve_left hiI)]
  exact sum_mem_biSup fun i _ => mem_range_self (single R φ i) (b i)

/--
theorem `iSup_range_single_eq_iInf_ker_proj` / 定理 `iSup_range_single_eq_iInf_ker_proj`

English:
theorem iSup_range_single_eq_iInf_ker_proj
  given: {I J : Set ι} (hIJ : IsCompl I J) (hI : I.Finite)
  proof: le_antisymm (iSup_range_single_le_iInf_ker_proj _ _ _ _ hIJ.disjoint)
    iInf_ker_proj_le_iSup_range_single R φ hI hIJ.codisjoint

中文:
定理 iSup_range_single_eq_iInf_ker_proj
  条件: {I J : 集合 ι} (hIJ : 是补集 I J) (hI : I.有限)
  证明: le_antisymm (iSup_range_single_le_iInf_ker_proj _ _ _ _ hIJ.disjoint)
    iInf_ker_proj_le_iSup_range_single R φ hI hIJ.codisjoint

Depends on / 依赖: codisjoint, disjoint, hIJ.codisjoint, hIJ.disjoint, iInf_ker_proj_le_iSup_range_single, iSup_range_single_le_iInf_ker_proj, le_antisymm
-/
theorem iSup_range_single_eq_iInf_ker_proj {I J : Set ι} (hIJ : IsCompl I J) (hI : I.Finite) :
    ⨆ i in I, range (single R φ i) = ⨅ i in J, ker (proj i : (forall i, φ i) ->ₗ[R] φ i) :=
le_antisymm (iSup_range_single_le_iInf_ker_proj _ _ _ _ hIJ.disjoint)
    iInf_ker_proj_le_iSup_range_single R φ hI hIJ.codisjoint

/--
theorem `iSup_range_single` / 定理 `iSup_range_single`

English:
theorem iSup_range_single
  given: [Finite ι]
  statement: ⨆ i, range (single R φ i) = ⊤
  proof: by
  simpa using iInf_ker_proj_le_iSup_range_single R φ Set.finite_univ isCompl_top_bot.codisjoint

中文:
定理 iSup_range_single
  条件: [有限 ι]
  结论: ⨆ i, range (single R φ i) = ⊤
  证明: by
  simpa using iInf_ker_proj_le_iSup_range_single R φ Set.finite_univ isCompl_top_bot.codisjoint

Depends on / 依赖: Set.finite_univ, codisjoint, finite_univ, iInf_ker_proj_le_iSup_range_single, isCompl_top_bot, isCompl_top_bot.codisjoint
-/
theorem iSup_range_single [Finite ι] : ⨆ i, range (single R φ i) = ⊤ := by
  simpa using iInf_ker_proj_le_iSup_range_single R φ Set.finite_univ isCompl_top_bot.codisjoint

/--
theorem `disjoint_single_single` / 定理 `disjoint_single_single`

English:
theorem disjoint_single_single
  given: (I J : Set ι) (h : Disjoint I J)
  proof: by
  refine
    Disjoint.mono (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro

中文:
定理 disjoint_single_single
  条件: (I J : 集合 ι) (h : Disjoint I J)
  证明: by
  refine
    Disjoint.mono (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro

Depends on / 依赖: Disjoint, Disjoint.mono, SetLike, SetLike.le_def, classical, disjoint_compl_right, disjoint_iff_inf_le, funext_iff, h.le_bot, iSup_range_single_le_iInf_ker_proj, le_bot, le_def, mem_bot, mem_iInf, mem_inf, mem_ker, proj_apply
-/
theorem disjoint_single_single (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i in I, range (single R φ i)) (⨆ i in J, range (single R φ i)) := by
  refine
    Disjoint.mono (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
    by_cases hiI : i in I
    · by_cases hiJ : i in J
      · exact (h.le_bot ⟨hiI, hiJ⟩).elim
      · exact hJ i hiJ
    · exact hI i hiI

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps symm_apply]
/--
Definition of `lsum` / `lsum` 的定义

English:
definition lsum
  signature: (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Module S M]
  body: ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single R φ i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  ri

中文:
定义 lsum
  签名: (S) [加法交换幺半群 M] [模 R M] [有限类型 ι] [半环 S] [模 S M]
  定义体: ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single R φ i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  ri
-/
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : ((i : ι) -> φ i ->ₗ[R] M) ≃ₗ[S] ((i : ι) -> φ i) ->ₗ[R] M where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single R φ i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  right_inv f := by
    ext x
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]

@[simp]
/--
theorem `lsum_apply` / 定理 `lsum_apply`

English:
theorem lsum_apply
  statement: (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
  proof: rfl

中文:
定理 lsum_apply
  结论: (S) [加法交换幺半群 M] [模 R M] [有限类型 ι] [半环 S]
  证明: rfl
-/
theorem lsum_apply (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ i ->ₗ[R] M) :
    lsum R φ S f = ∑ i : ι, (f i).comp (proj i) := rfl

/--
theorem `lsum_piSingle` / 定理 `lsum_piSingle`

English:
theorem lsum_piSingle
  statement: (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
  proof: by
  simp_rw [lsum_apply, sum_apply, comp_apply, proj_apply, apply_single, Fintype.sum_pi_single']

@[simp high]

中文:
定理 lsum_piSingle
  结论: (S) [加法交换幺半群 M] [模 R M] [有限类型 ι] [半环 S]
  证明: by
  simp_rw [lsum_apply, sum_apply, comp_apply, proj_apply, apply_single, Fintype.sum_pi_single']

@[simp high]

Depends on / 依赖: Fintype, Fintype.sum_pi_single, apply_single, comp_apply, lsum_apply, proj_apply, simp_rw, sum_apply, sum_pi_single
-/
theorem lsum_piSingle (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ i ->ₗ[R] M) (i : ι) (x : φ i) :
    lsum R φ S f (Pi.single i x) = f i x := by
  simp_rw [lsum_apply, sum_apply, comp_apply, proj_apply, apply_single, Fintype.sum_pi_single']

@[simp high]
/--
theorem `lsum_single` / 定理 `lsum_single`

English:
theorem lsum_single
  statement: (S) [Fintype ι] [Semiring S]
  proof: LinearMap.ext fun x => by simp [Finset.univ_sum_single]

中文:
定理 lsum_single
  结论: (S) [有限类型 ι] [半环 S]
  证明: LinearMap.ext fun x => by simp [Finset.univ_sum_single]

Depends on / 依赖: Finset, Finset.univ_sum_single, LinearMap, LinearMap.ext, univ_sum_single
-/
theorem lsum_single (S) [Fintype ι] [Semiring S]
    [forall i, Module S (φ i)] [forall i, SMulCommClass R S (φ i)] :
    LinearMap.lsum R φ S (LinearMap.single R φ) = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]

variable {R φ}

section Ext

variable [Finite ι] [AddCommMonoid M] [Module R M] {f g : ((i : ι) -> φ i) ->ₗ[R] M}

/--
theorem `pi_ext` / 定理 `pi_ext`

English:
theorem pi_ext
  given: (h : forall i x, f (Pi.single i x) = g (Pi.single i x))
  statement: f = g
  proof: toAddMonoidHom_injective AddMonoidHom.functions_ext _ _ _ h

中文:
定理 pi_ext
  条件: (h : 对任意 i x, f (依赖函数类型.single i x) = g (依赖函数类型.single i x))
  结论: f = g
  证明: toAddMonoidHom_injective AddMonoidHom.functions_ext _ _ _ h

Depends on / 依赖: AddMonoidHom, AddMonoidHom.functions_ext, functions_ext, toAddMonoidHom_injective
-/
theorem pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
toAddMonoidHom_injective AddMonoidHom.functions_ext _ _ _ h

/--
theorem `pi_ext_iff` / 定理 `pi_ext_iff`

English:
theorem pi_ext_iff
  statement: f = g ↔ forall i x, f (Pi.single i x) = g (Pi.single i x)
  proof: ⟨fun h _ _ => h ▸ rfl, pi_ext⟩

中文:
定理 pi_ext_iff
  结论: f = g ↔ 对任意 i x, f (依赖函数类型.single i x) = g (依赖函数类型.single i x)
  证明: ⟨fun h _ _ => h ▸ rfl, pi_ext⟩

Depends on / 依赖: pi_ext
-/
theorem pi_ext_iff : f = g ↔ forall i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h _ _ => h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `LinearMap.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `pi_ext'` / 定理 `pi_ext'`

English:
theorem pi_ext'
  given: (h : forall i, f.comp (single R φ i) = g.comp (single R φ i))
  statement: f = g
  proof: by
  refine pi_ext fun i x => ?_
  convert! LinearMap.congr_fun (h i) x

中文:
定理 pi_ext'
  条件: (h : 对任意 i, f.comp (single R φ i) = g.comp (single R φ i))
  结论: f = g
  证明: by
  refine pi_ext fun i x => ?_
  convert! LinearMap.congr_fun (h i) x

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, convert, pi_ext
-/
theorem pi_ext' (h : forall i, f.comp (single R φ i) = g.comp (single R φ i)) : f = g := by
  refine pi_ext fun i x => ?_
  convert! LinearMap.congr_fun (h i) x

end Ext

section

variable (R φ)

/--
Definition of `iInfKerProjEquiv` / `iInfKerProjEquiv` 的定义

English:
definition iInfKerProjEquiv
  signature: {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
  body: by
  refine
    LinearEquiv.ofLinearMap (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i in I then proj (⟨i, h⟩ : I) else 0) ?_) ?_ ?_
  · intro b
    simp only [mem_iInf, mem_ker, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => 

中文:
定义 iInfKerProjEquiv
  签名: {I J : 集合 ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
  定义体: by
  refine
    LinearEquiv.ofLinearMap (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i in I then proj (⟨i, h⟩ : I) else 0) ?_) ?_ ?_
  · intro b
    simp only [mem_iInf, mem_ker, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => 

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coe_proj, LinearMap.pi_apply, Submodule, Submodule.subtype, Subtype, Subtype.coe_prop, codRestrict, coe_proj, coe_prop, comp_assoc, dif_neg, dif_pos, hd.le_bot, le_bot, mem_iInf, mem_ker, ofLinearMap
-/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjoint I J)
    (hu : Set.univ subseteq I union J) :
    (⨅ i in J, ker (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) :
    Submodule R ((i : ι) -> φ i)) ≃ₗ[R] (i : I) -> φ i := by
  refine
    LinearEquiv.ofLinearMap (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i in I then proj (⟨i, h⟩ : I) else 0) ?_) ?_ ?_
  · intro b
    simp only [mem_iInf, mem_ker, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this]; rw [zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_codRestrict, proj_pi, Subtype.coe_prop]
    ext b ⟨j, hj⟩
    simp only [dif_pos,
      LinearMap.coe_proj, LinearMap.pi_apply]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : forall i in J, b i = 0 := by
      simpa only [mem_iInf, mem_ker, proj_apply] using (mem_iInf _).1 hb
    simp only [comp_apply, pi_apply, id_apply, codRestrict_apply]
    split_ifs with h
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm

end

section

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: (i j : ι)
  body: @Function.update ι (fun j => φ i ->ₗ[R] φ j) _ 0 i id j

中文:
定义 diag
  签名: (i j : ι)
  定义体: @Function.update ι (fun j => φ i ->ₗ[R] φ j) _ 0 i id j

Depends on / 依赖: Function, Function.update, update
-/
def diag (i j : ι) : φ i ->ₗ[R] φ j :=
  @Function.update ι (fun j => φ i ->ₗ[R] φ j) _ 0 i id j

/--
theorem `update_apply` / 定理 `update_apply`

English:
theorem update_apply
  given: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ ->ₗ[R] φ i)
  proof: by
  by_cases h : j = i
  · rw [h, update_self, update_self]
  · rw [update_of_ne h, update_of_ne h]

中文:
定理 update_apply
  条件: (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ ->ₗ[R] φ i)
  证明: by
  by_cases h : j = i
  · rw [h, update_self, update_self]
  · rw [update_of_ne h, update_of_ne h]

Depends on / 依赖: update_of_ne, update_self
-/
theorem update_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ ->ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j := by
  by_cases h : j = i
  · rw [h, update_self, update_self]
  · rw [update_of_ne h, update_of_ne h]

variable (R φ)

/--
theorem `single_eq_pi_diag` / 定理 `single_eq_pi_diag`

English:
theorem single_eq_pi_diag
  given: (i : ι)
  statement: single R φ i = pi (diag i)
  proof: by
  ext x j
  convert! (update_apply 0 x i j _).symm
  rfl

中文:
定理 single_eq_pi_diag
  条件: (i : ι)
  结论: single R φ i = pi (diag i)
  证明: by
  ext x j
  convert! (update_apply 0 x i j _).symm
  rfl

Depends on / 依赖: convert, update_apply
-/
theorem single_eq_pi_diag (i : ι) : single R φ i = pi (diag i) := by
  ext x j
  convert! (update_apply 0 x i j _).symm
  rfl

/--
theorem `ker_single` / 定理 `ker_single`

English:
theorem ker_single
  given: (i : ι)
  statement: ker (single R φ i) = ⊥
  proof: ker_eq_bot_of_injective Pi.single_injective _

中文:
定理 ker_single
  条件: (i : ι)
  结论: ker (single R φ i) = ⊥
  证明: ker_eq_bot_of_injective Pi.single_injective _

Depends on / 依赖: Pi.single_injective, ker_eq_bot_of_injective, single_injective
-/
theorem ker_single (i : ι) : ker (single R φ i) = ⊥ :=
ker_eq_bot_of_injective Pi.single_injective _

/--
theorem `proj_comp_single` / 定理 `proj_comp_single`

English:
theorem proj_comp_single
  given: (i j : ι)
  statement: (proj i).comp (single R φ j) = diag j i
  proof: by
  rw [single_eq_pi_diag]; rw [proj_pi]

中文:
定理 proj_comp_single
  条件: (i j : ι)
  结论: (proj i).comp (single R φ j) = diag j i
  证明: by
  rw [single_eq_pi_diag]; rw [proj_pi]

Depends on / 依赖: proj_pi, single_eq_pi_diag
-/
theorem proj_comp_single (i j : ι) : (proj i).comp (single R φ j) = diag j i := by
  rw [single_eq_pi_diag]; rw [proj_pi]

end

/--
theorem `pi_apply_eq_sum_univ` / 定理 `pi_apply_eq_sum_univ`

English:
theorem pi_apply_eq_sum_univ
  given: [Fintype ι] (f : (ι -> R) ->ₗ[R] M₂) (x : ι -> R)
  proof: by
  conv_lhs => rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [map_smul]

中文:
定理 pi_apply_eq_sum_univ
  条件: [有限类型 ι] (f : (ι -> R) ->ₗ[R] M₂) (x : ι -> R)
  证明: by
  conv_lhs => rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [map_smul]

Depends on / 依赖: Finset, Finset.sum_congr, conv_lhs, map_smul, map_sum, pi_eq_sum_univ, sum_congr
-/
theorem pi_apply_eq_sum_univ [Fintype ι] (f : (ι -> R) ->ₗ[R] M₂) (x : ι -> R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
  conv_lhs => rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [map_smul]

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι -> Type*} [(i : ι) -> AddCommMonoid (φ i)] [(i : ι) -> Module R (φ i)]

open LinearMap

/-- A version of `Set.pi` for submodules. Given an index set `I` and a family of submodules
`p : (i : ι) → Submodule R (φ i)`, `pi I p` is the submodule of dependent functions
`f : (i : ι) → φ i` such that `f i` belongs to `p i` whenever `i ∈ I`. -/
@[simps]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (I : Set ι) (p : (i : ι) -> Submodule R (φ i))
  body: Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)

中文:
定义 pi
  签名: (I : 集合 ι) (p : (i : ι) -> 子模 R (φ i))
  定义体: Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)

Depends on / 依赖: Set.pi
-/
def pi (I : Set ι) (p : (i : ι) -> Submodule R (φ i)) : Submodule R ((i : ι) -> φ i) where
  carrier := Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)

attribute [norm_cast] coe_pi

variable {I : Set ι} {p q : (i : ι) -> Submodule R (φ i)} {x : (i : ι) -> φ i}

@[simp]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  statement: x in pi I p ↔ forall i in I, x i in p i
  proof: Iff.rfl

@[simp]

中文:
定理 mem_pi
  结论: x in pi I p ↔ 对任意 i in I, x i in p i
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_pi : x in pi I p ↔ forall i in I, x i in p i :=
  Iff.rfl

@[simp]
/--
theorem `pi_empty` / 定理 `pi_empty`

English:
theorem pi_empty
  given: (p : (i : ι) -> Submodule R (φ i))
  statement: pi ∅ p = ⊤
  proof: SetLike.coe_injective Set.empty_pi _

@[simp]

中文:
定理 pi_empty
  条件: (p : (i : ι) -> 子模 R (φ i))
  结论: pi ∅ p = ⊤
  证明: SetLike.coe_injective Set.empty_pi _

@[simp]

Depends on / 依赖: Set.empty_pi, SetLike, SetLike.coe_injective, coe_injective, empty_pi
-/
theorem pi_empty (p : (i : ι) -> Submodule R (φ i)) : pi ∅ p = ⊤ :=
SetLike.coe_injective Set.empty_pi _

@[simp]
/--
theorem `pi_top` / 定理 `pi_top`

English:
theorem pi_top
  given: (s : Set ι)
  statement: (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤
  proof: SetLike.coe_injective Set.pi_univ _

@[simp]

中文:
定理 pi_top
  条件: (s : 集合 ι)
  结论: (pi s fun i : ι => (⊤ : 子模 R (φ i))) = ⊤
  证明: SetLike.coe_injective Set.pi_univ _

@[simp]

Depends on / 依赖: Set.pi_univ, SetLike, SetLike.coe_injective, coe_injective, pi_univ
-/
theorem pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤ :=
SetLike.coe_injective Set.pi_univ _

@[simp]
/--
theorem `pi_univ_bot` / 定理 `pi_univ_bot`

English:
theorem pi_univ_bot
  statement: (pi Set.univ fun i : ι => (⊥ : Submodule R (φ i))) = ⊥
  proof: le_bot_iff.mp fun _ h => funext fun i => h i trivial

@[gcongr]

中文:
定理 pi_univ_bot
  结论: (pi 集合.univ fun i : ι => (⊥ : 子模 R (φ i))) = ⊥
  证明: le_bot_iff.mp fun _ h => funext fun i => h i trivial

@[gcongr]

Depends on / 依赖: le_bot_iff, le_bot_iff.mp
-/
theorem pi_univ_bot : (pi Set.univ fun i : ι => (⊥ : Submodule R (φ i))) = ⊥ :=
  le_bot_iff.mp fun _ h => funext fun i => h i trivial

@[gcongr]
/--
theorem `pi_mono` / 定理 `pi_mono`

English:
theorem pi_mono
  given: {s : Set ι} (h : forall i in s, p i <= q i)
  statement: pi s p <= pi s q
  proof: Set.pi_mono h

中文:
定理 pi_mono
  条件: {s : 集合 ι} (h : 对任意 i in s, p i <= q i)
  结论: pi s p <= pi s q
  证明: Set.pi_mono h

Depends on / 依赖: Set.pi_mono, pi_mono
-/
theorem pi_mono {s : Set ι} (h : forall i in s, p i <= q i) : pi s p <= pi s q :=
  Set.pi_mono h

/--
theorem `biInf_comap_proj` / 定理 `biInf_comap_proj`

English:
theorem biInf_comap_proj
  proof: by
  ext x
  simp

中文:
定理 biInf_comap_proj
  证明: by
  ext x
  simp

Depends on / 依赖: NeZero, Nonempty
-/
theorem biInf_comap_proj :
    ⨅ i in I, comap (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) (p i) = pi I p := by
  ext x
  simp

/--
theorem `iInf_comap_proj` / 定理 `iInf_comap_proj`

English:
theorem iInf_comap_proj
  proof: by
  ext x
  simp

中文:
定理 iInf_comap_proj
  证明: by
  ext x
  simp
-/
theorem iInf_comap_proj :
    ⨅ i, comap (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) (p i) = pi Set.univ p := by
  ext x
  simp

/--
theorem `le_comap_single_pi` / 定理 `le_comap_single_pi`

English:
theorem le_comap_single_pi
  given: [DecidableEq ι] (p : (i : ι) -> Submodule R (φ i)) {I i}
  proof: by
  intro x hx
  rw [Submodule.mem_comap]; rw [Submodule.mem_pi]
  rintro j -
  rcases eq_or_ne j i with rfl | hne <;> simp [*]

中文:
定理 le_comap_single_pi
  条件: [DecidableEq ι] (p : (i : ι) -> 子模 R (φ i)) {I i}
  证明: by
  intro x hx
  rw [Submodule.mem_comap]; rw [Submodule.mem_pi]
  rintro j -
  rcases eq_or_ne j i with rfl | hne <;> simp [*]

Depends on / 依赖: Submodule, Submodule.mem_comap, Submodule.mem_pi, eq_or_ne, mem_comap, mem_pi
-/
theorem le_comap_single_pi [DecidableEq ι] (p : (i : ι) -> Submodule R (φ i)) {I i} :
    p i <= Submodule.comap (LinearMap.single R φ i : φ i ->ₗ[R] _) (Submodule.pi I p) := by
  intro x hx
  rw [Submodule.mem_comap]; rw [Submodule.mem_pi]
  rintro j -
  rcases eq_or_ne j i with rfl | hne <;> simp [*]

/--
theorem `iSup_map_single_le` / 定理 `iSup_map_single_le`

English:
theorem iSup_map_single_le
  given: [DecidableEq ι]
  proof: iSup_le fun _ => map_le_iff_le_comap.mpr le_comap_single_pi _

中文:
定理 iSup_map_single_le
  条件: [DecidableEq ι]
  证明: iSup_le fun _ => map_le_iff_le_comap.mpr le_comap_single_pi _

Depends on / 依赖: iSup_le, le_comap_single_pi, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem iSup_map_single_le [DecidableEq ι] :
    ⨆ i, map (LinearMap.single R φ i) (p i) <= pi I p :=
iSup_le fun _ => map_le_iff_le_comap.mpr le_comap_single_pi _

/--
theorem `iSup_map_single` / 定理 `iSup_map_single`

English:
theorem iSup_map_single
  given: [DecidableEq ι] [Finite ι]
  proof: by
  cases nonempty_fintype ι
  refine iSup_map_single_le.antisymm fun x hx => ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)

中文:
定理 iSup_map_single
  条件: [DecidableEq ι] [有限 ι]
  证明: by
  cases nonempty_fintype ι
  refine iSup_map_single_le.antisymm fun x hx => ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)

Depends on / 依赖: Finset, Finset.univ_sum_single, antisymm, iSup_map_single_le, iSup_map_single_le.antisymm, mem_map_of_mem, nonempty_fintype, sum_mem_iSup, univ_sum_single
-/
theorem iSup_map_single [DecidableEq ι] [Finite ι] :
    ⨆ i, map (LinearMap.single R φ i : φ i ->ₗ[R] (i : ι) -> φ i) (p i) = pi Set.univ p := by
  cases nonempty_fintype ι
  refine iSup_map_single_le.antisymm fun x hx => ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)

end Submodule

namespace LinearMap

variable [Semiring R]

/--
lemma `ker_compLeft` / 引理 `ker_compLeft`

English:
lemma ker_compLeft
  statement: [AddCommMonoid M] [AddCommMonoid M₂]
  proof: Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

中文:
引理 ker_compLeft
  结论: [加法交换幺半群 M] [加法交换幺半群 M₂]
  证明: Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

Depends on / 依赖: Submodule, Submodule.ext, congr_fun
-/
lemma ker_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) (I : Type*) :
    LinearMap.ker (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.ker f) :=
  Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩

/--
lemma `range_compLeft` / 引理 `range_compLeft`

English:
lemma range_compLeft
  statement: [AddCommMonoid M] [AddCommMonoid M₂]
  proof: Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

中文:
引理 range_compLeft
  结论: [加法交换幺半群 M] [加法交换幺半群 M₂]
  证明: Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

Depends on / 依赖: Submodule, Submodule.ext, congr_fun
-/
lemma range_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) (I : Type*) :
    LinearMap.range (f.compLeft I) =
      Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.range f) :=
  Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

end LinearMap

namespace LinearEquiv

variable [Semiring R] {φ ψ χ : ι -> Type*}
variable [(i : ι) -> AddCommMonoid (φ i)] [(i : ι) -> Module R (φ i)]
variable [(i : ι) -> AddCommMonoid (ψ i)] [(i : ι) -> Module R (ψ i)]
variable [(i : ι) -> AddCommMonoid (χ i)] [(i : ι) -> Module R (χ i)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: (e : (i : ι) -> φ i ≃ₗ[R] ψ i)
  body: { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }

@[simp]

中文:
定义 piCongrRight
  签名: (e : (i : ι) -> φ i ≃ₗ[R] ψ i)
  定义体: { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.piCongrRight, invFun, map_smul, piCongrRight, toAddEquiv
-/
def piCongrRight (e : (i : ι) -> φ i ≃ₗ[R] ψ i) : ((i : ι) -> φ i) ≃ₗ[R] (i : ι) -> ψ i :=
  { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }

@[simp]
/--
theorem `piCongrRight_apply` / 定理 `piCongrRight_apply`

English:
theorem piCongrRight_apply
  given: (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f i)
  proof: rfl

@[simp]

中文:
定理 piCongrRight_apply
  条件: (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f i)
  证明: rfl

@[simp]
-/
theorem piCongrRight_apply (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f i) :
    piCongrRight e f i = e i (f i) := rfl

@[simp]
/--
theorem `piCongrRight_refl` / 定理 `piCongrRight_refl`

English:
theorem piCongrRight_refl
  statement: (piCongrRight fun j => refl R (φ j)) = refl _ _
  proof: rfl

@[simp]

中文:
定理 piCongrRight_refl
  结论: (piCongrRight fun j => refl R (φ j)) = refl _ _
  证明: rfl

@[simp]
-/
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl

@[simp]
/--
theorem `piCongrRight_symm` / 定理 `piCongrRight_symm`

English:
theorem piCongrRight_symm
  given: (e : (i : ι) -> φ i ≃ₗ[R] ψ i)
  proof: rfl

@[simp]

中文:
定理 piCongrRight_symm
  条件: (e : (i : ι) -> φ i ≃ₗ[R] ψ i)
  证明: rfl

@[simp]
-/
theorem piCongrRight_symm (e : (i : ι) -> φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
/--
theorem `piCongrRight_trans` / 定理 `piCongrRight_trans`

English:
theorem piCongrRight_trans
  given: (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f : (i : ι) -> ψ i ≃ₗ[R] χ i)
  proof: rfl

中文:
定理 piCongrRight_trans
  条件: (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f : (i : ι) -> ψ i ≃ₗ[R] χ i)
  证明: rfl
-/
theorem piCongrRight_trans (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f : (i : ι) -> ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `LinearEquiv`. -/
@[simps +simpRhs]
/--
Definition of `piCongrLeft'` / `piCongrLeft'` 的定义

English:
definition piCongrLeft'
  signature: (e : ι ≃ ι')
  body: { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

中文:
定义 piCongrLeft'
  签名: (e : ι ≃ ι')
  定义体: { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.piCongrLeft, map_add, map_smul, piCongrLeft
-/
def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) -> φ i') ≃ₗ[R] (i : ι') -> φ e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/--
Definition of `piCongrLeft` / `piCongrLeft` 的定义

English:
definition piCongrLeft
  signature: (e : ι' ≃ ι)
  body: (piCongrLeft' R φ e.symm).symm

中文:
定义 piCongrLeft
  签名: (e : ι' ≃ ι)
  定义体: (piCongrLeft' R φ e.symm).symm

Depends on / 依赖: e.symm, piCongrLeft
-/
def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') -> φ (e i')) ≃ₗ[R] (i : ι) -> φ i :=
  (piCongrLeft' R φ e.symm).symm

/--
Definition of `piCurry` / `piCurry` 的定义

English:
definition piCurry
  signature: {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
  body: Equiv.piCurry α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 piCurry
  签名: {ι : 类型} {κ : ι -> 类型} (α : 对任意 i, κ i -> 类型)
  定义体: Equiv.piCurry α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Equiv.piCurry, piCurry
-/
def piCurry {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
    [forall i k, AddCommMonoid (α i k)] [forall i k, Module R (α i k)] :
    (Π i : Sigma κ, α i.1 i.2) ≃ₗ[R] Π i j, α i j where
  __ := Equiv.piCurry α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `piCurry_apply` / 定理 `piCurry_apply`

English:
theorem piCurry_apply
  statement: {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
  proof: rfl

中文:
定理 piCurry_apply
  结论: {ι : 类型} {κ : ι -> 类型} (α : 对任意 i, κ i -> 类型)
  证明: rfl
-/
@[simp] theorem piCurry_apply {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
    [forall i k, AddCommMonoid (α i k)] [forall i k, Module R (α i k)]
    (f : forall x : Σ i, κ i, α x.1 x.2) :
    piCurry R α f = Sigma.curry f :=
  rfl

/--
theorem `piCurry_symm_apply` / 定理 `piCurry_symm_apply`

English:
theorem piCurry_symm_apply
  statement: {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
  proof: rfl

中文:
定理 piCurry_symm_apply
  结论: {ι : 类型} {κ : ι -> 类型} (α : 对任意 i, κ i -> 类型)
  证明: rfl
-/
@[simp] theorem piCurry_symm_apply {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*)
    [forall i k, AddCommMonoid (α i k)] [forall i k, Module R (α i k)]
    (f : forall a b, α a b) :
    (piCurry R α).symm f = Sigma.uncurry f :=
  rfl

/--
Definition of `piOptionEquivProd` / `piOptionEquivProd` 的定义

English:
definition piOptionEquivProd
  signature: {ι : Type*} {M : Option ι -> Type*} [(i : Option ι) -> AddCommMonoid (M i)]
  body: { Equiv.piOptionEquivProd with
    map_add' := by simp [funext_iff]
    map_smul' := by simp [funext_iff] }

中文:
定义 piOptionEquivProd
  签名: {ι : 类型} {M : 选项类型 ι -> 类型} [(i : 选项类型 ι) -> 加法交换幺半群 (M i)]
  定义体: { Equiv.piOptionEquivProd with
    map_add' := by simp [funext_iff]
    map_smul' := by simp [funext_iff] }

Depends on / 依赖: Equiv.piOptionEquivProd, funext_iff, map_add, map_smul, piOptionEquivProd
-/
def piOptionEquivProd {ι : Type*} {M : Option ι -> Type*} [(i : Option ι) -> AddCommMonoid (M i)]
    [(i : Option ι) -> Module R (M i)] :
    ((i : Option ι) -> M i) ≃ₗ[R] M none × ((i : ι) -> M (some i)) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [funext_iff]
    map_smul' := by simp [funext_iff] }

variable (ι M) (S : Type*) [Fintype ι] [DecidableEq ι] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [SMulCommClass R S M]

/--
Definition of `piRing` / `piRing` 的定义

English:
definition piRing
  signature: : ((ι -> R) ->ₗ[R] M) ≃ₗ[S] ι -> M
  body: (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)

中文:
定义 piRing
  签名: : ((ι -> R) ->ₗ[R] M) ≃ₗ[S] ι -> M
  定义体: (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)

Depends on / 依赖: LinearMap, LinearMap.lsum, LinearMap.ringLmapEquivSelf, piCongrRight, ringLmapEquivSelf, symm.trans
-/
def piRing : ((ι -> R) ->ₗ[R] M) ≃ₗ[S] ι -> M :=
  (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)

variable {ι R M}

@[simp]
/--
theorem `piRing_apply` / 定理 `piRing_apply`

English:
theorem piRing_apply
  given: (f : (ι -> R) ->ₗ[R] M) (i : ι)
  statement: piRing R M ι S f i = f (Pi.single i 1)
  proof: rfl

@[simp]

中文:
定理 piRing_apply
  条件: (f : (ι -> R) ->ₗ[R] M) (i : ι)
  结论: piRing R M ι S f i = f (依赖函数类型.single i 1)
  证明: rfl

@[simp]
-/
theorem piRing_apply (f : (ι -> R) ->ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl

@[simp]
/--
theorem `piRing_symm_apply` / 定理 `piRing_symm_apply`

English:
theorem piRing_symm_apply
  given: (f : ι -> M) (g : ι -> R)
  statement: (piRing R M ι S).symm f g = ∑ i, g i • f i
  proof: by
  simp [piRing, LinearMap.lsum_apply]

中文:
定理 piRing_symm_apply
  条件: (f : ι -> M) (g : ι -> R)
  结论: (piRing R M ι S).symm f g = ∑ i, g i • f i
  证明: by
  simp [piRing, LinearMap.lsum_apply]

Depends on / 依赖: LinearMap, LinearMap.lsum_apply, lsum_apply, piRing
-/
theorem piRing_symm_apply (f : ι -> M) (g : ι -> R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [piRing, LinearMap.lsum_apply]

-- TODO additive version?
/--
Definition of `sumArrowLequivProdArrow` / `sumArrowLequivProdArrow` 的定义

English:
definition sumArrowLequivProdArrow
  signature: (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  body: { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]

中文:
定义 sumArrowLequivProdArrow
  签名: (α β R M : 类型) [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, map_add, map_smul, sumArrowEquivProdArrow
-/
def sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (α oplus β -> M) ≃ₗ[R] (α -> M) × (β -> M) :=
  { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]
/--
theorem `sumArrowLequivProdArrow_apply_fst` / 定理 `sumArrowLequivProdArrow_apply_fst`

English:
theorem sumArrowLequivProdArrow_apply_fst
  given: {α β} (f : α oplus β -> M) (a : α)
  proof: rfl

@[simp]

中文:
定理 sumArrowLequivProdArrow_apply_fst
  条件: {α β} (f : α oplus β -> M) (a : α)
  证明: rfl

@[simp]
-/
theorem sumArrowLequivProdArrow_apply_fst {α β} (f : α oplus β -> M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl

@[simp]
/--
theorem `sumArrowLequivProdArrow_apply_snd` / 定理 `sumArrowLequivProdArrow_apply_snd`

English:
theorem sumArrowLequivProdArrow_apply_snd
  given: {α β} (f : α oplus β -> M) (b : β)
  proof: rfl

@[simp]

中文:
定理 sumArrowLequivProdArrow_apply_snd
  条件: {α β} (f : α oplus β -> M) (b : β)
  证明: rfl

@[simp]
-/
theorem sumArrowLequivProdArrow_apply_snd {α β} (f : α oplus β -> M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl

@[simp]
/--
theorem `sumArrowLequivProdArrow_symm_apply_inl` / 定理 `sumArrowLequivProdArrow_symm_apply_inl`

English:
theorem sumArrowLequivProdArrow_symm_apply_inl
  given: {α β} (f : α -> M) (g : β -> M) (a : α)
  proof: rfl

@[simp]

中文:
定理 sumArrowLequivProdArrow_symm_apply_inl
  条件: {α β} (f : α -> M) (g : β -> M) (a : α)
  证明: rfl

@[simp]
-/
theorem sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α -> M) (g : β -> M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl

@[simp]
/--
theorem `sumArrowLequivProdArrow_symm_apply_inr` / 定理 `sumArrowLequivProdArrow_symm_apply_inr`

English:
theorem sumArrowLequivProdArrow_symm_apply_inr
  given: {α β} (f : α -> M) (g : β -> M) (b : β)
  proof: rfl

中文:
定理 sumArrowLequivProdArrow_symm_apply_inr
  条件: {α β} (f : α -> M) (g : β -> M) (b : β)
  证明: rfl
-/
theorem sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α -> M) (g : β -> M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl

/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps +simpRhs -fullyApplied symm_apply]
/--
Definition of `funUnique` / `funUnique` 的定义

English:
definition funUnique
  signature: (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  body: .funUnique ι M
  map_smul' _ _ := rfl

@[simp]

中文:
定义 funUnique
  签名: (ι R M : 类型) [唯一 ι] [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: .funUnique ι M
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: funUnique
-/
def funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι -> M) ≃ₗ[R] M where
  toAddEquiv := .funUnique ι M
  map_smul' _ _ := rfl

@[simp]
/--
theorem `funUnique_apply` / 定理 `funUnique_apply`

English:
theorem funUnique_apply
  given: (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  proof: rfl

中文:
定理 funUnique_apply
  条件: (ι R M : 类型) [唯一 ι] [半环 R] [加法交换幺半群 M] [模 R M]
  证明: rfl
-/
theorem funUnique_apply (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (funUnique ι R M : (ι -> M) -> M) = eval default := rfl

variable (R M)

/-- Linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`. -/
@[simps +simpRhs -fullyApplied symm_apply]
/--
Definition of `piFinTwo` / `piFinTwo` 的定义

English:
definition piFinTwo
  signature: (M : Fin 2 -> Type v)
  body: { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 piFinTwo
  签名: (M : 有限集 2 -> 类型v)
  定义体: { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]

Depends on / 依赖: map_add, map_smul, piFinTwoEquiv
-/
def piFinTwo (M : Fin 2 -> Type v)
    [(i : Fin 2) -> AddCommMonoid (M i)] [(i : Fin 2) -> Module R (M i)] :
    ((i : Fin 2) -> M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
/--
theorem `piFinTwo_apply` / 定理 `piFinTwo_apply`

English:
theorem piFinTwo_apply
  statement: (M : Fin 2 -> Type v)
  proof: rfl

中文:
定理 piFinTwo_apply
  结论: (M : 有限集 2 -> 类型v)
  证明: rfl
-/
theorem piFinTwo_apply (M : Fin 2 -> Type v)
    [(i : Fin 2) -> AddCommMonoid (M i)] [(i : Fin 2) -> Module R (M i)] :
    (piFinTwo R M : ((i : Fin 2) -> M i) -> M 0 × M 1) = fun f => (f 0, f 1) := rfl

/-- Linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied]
/--
Definition of `finTwoArrow` / `finTwoArrow` 的定义

English:
definition finTwoArrow
  signature: : (Fin 2 -> M) ≃ₗ[R] M × M
  body: { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

中文:
定义 finTwoArrow
  签名: : (有限集 2 -> M) ≃ₗ[R] M × M
  定义体: { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

Depends on / 依赖: finTwoArrowEquiv, piFinTwo
-/
def finTwoArrow : (Fin 2 -> M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

end LinearEquiv

/--
lemma `Pi.mem_span_range_single_inl_iff` / 引理 `Pi.mem_span_range_single_inl_iff`

English:
lemma Pi.mem_span_range_single_inl_iff
  proof: by
  refine ⟨fun hx k => ?_, fun hx => ?_⟩
  · induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; simp
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]
  · have := Fintype.ofFinite ι
    suffices x = ∑ i : ι, x (Sum.inl i) • Pi.s

中文:
引理 依赖函数类型.mem_span_range_single_inl_iff
  证明: by
  refine ⟨fun hx k => ?_, fun hx => ?_⟩
  · induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; simp
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]
  · have := Fintype.ofFinite ι
    suffices x = ∑ i : ι, x (Sum.inl i) • Pi.s

Depends on / 依赖: Fintype, Fintype.ofFinite, Pi.single, SMulMemClass, SMulMemClass.smul_mem, Set.mem_range_self, Sum.inl, mem_range_self, ofFinite, single, single_apply, smul_mem, span_induction, subset_span, sum_mem
-/
lemma Pi.mem_span_range_single_inl_iff
    [DecidableEq ι] [DecidableEq ι'] [Finite ι] [Semiring R] {x : ι oplus ι' -> R} :
    x in span R (Set.range fun i => single (Sum.inl i) 1) ↔ forall k, x (Sum.inr k) = 0 := by
  refine ⟨fun hx k => ?_, fun hx => ?_⟩
  · induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; simp
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]
  · have := Fintype.ofFinite ι
    suffices x = ∑ i : ι, x (Sum.inl i) • Pi.single (M := fun _ => R) (Sum.inl i) (1 : R) by
      rw [this]
exact sum_mem fun i _ => SMulMemClass.smul_mem _ subset_span Set.mem_range_self i
    ext (i | i)
    · simp [single_apply]
    · simp [hx i]

section Extend

variable (R) {η : Type*} [Semiring R] (s : ι -> η)

/-- `Function.extend s f 0` as a bundled linear map. -/
@[simps]
/--
Definition of `Function.ExtendByZero.linearMap` / `Function.ExtendByZero.linearMap` 的定义

English:
definition Function.ExtendByZero.linearMap
  signature: : (ι -> R) ->ₗ[R] η -> R
  body: { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

中文:
定义 函数.ExtendByZero.linearMap
  签名: : (ι -> R) ->ₗ[R] η -> R
  定义体: { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

Depends on / 依赖: ExtendByZero, Function, Function.ExtendByZero.hom, Function.extend, Function.extend_smul, extend, extend_smul, map_smul
-/
noncomputable def Function.ExtendByZero.linearMap : (ι -> R) ->ₗ[R] η -> R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

end Extend

variable (R) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps]
/--
Definition of `Fin.consLinearEquiv` / `Fin.consLinearEquiv` 的定义

English:
definition Fin.consLinearEquiv
  body: Fin.consEquiv M
map_add' x y := funext Fin.cases rfl (by simp)
map_smul' c x := funext Fin.cases rfl (by simp)

中文:
定义 有限集.consLinearEquiv
  定义体: Fin.consEquiv M
map_add' x y := funext Fin.cases rfl (by simp)
map_smul' c x := funext Fin.cases rfl (by simp)

Depends on / 依赖: Fin.consEquiv, consEquiv
-/
def Fin.consLinearEquiv
    {n : Nat} (M : Fin n.succ -> Type*) [Semiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)] :
    (M 0 × Π i, M (Fin.succ i)) ≃ₗ[R] (Π i, M i) where
  __ := Fin.consEquiv M
map_add' x y := funext Fin.cases rfl (by simp)
map_smul' c x := funext Fin.cases rfl (by simp)


/-! ### Bundled versions of `Matrix.vecCons` and `Matrix.vecEmpty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vecCons <| f₂.vecCons <| f₃.vecCons <| vecEmpty`.

While the same thing could be achieved using `LinearMap.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `LinearMap.vecCons`, as `Fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Fin

section Semiring

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/--
Definition of `LinearMap.vecEmpty` / `LinearMap.vecEmpty` 的定义

English:
definition LinearMap.vecEmpty
  signature: : M ->ₗ[R] Fin 0 -> M₃ where
  body: Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

@[simp]

中文:
定义 线性映射.vecEmpty
  签名: : M ->ₗ[R] 有限集 0 -> M₃ where
  定义体: Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

@[simp]

Depends on / 依赖: Matrix, Matrix.vecEmpty, vecEmpty
-/
def LinearMap.vecEmpty : M ->ₗ[R] Fin 0 -> M₃ where
  toFun _ := Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

@[simp]
/--
theorem `LinearMap.vecEmpty_apply` / 定理 `LinearMap.vecEmpty_apply`

English:
theorem LinearMap.vecEmpty_apply
  given: (m : M)
  statement: (LinearMap.vecEmpty : M ->ₗ[R] Fin 0 -> M₃) m = ![]
  proof: rfl

中文:
定理 线性映射.vecEmpty_apply
  条件: (m : M)
  结论: (线性映射.vecEmpty : M ->ₗ[R] 有限集 0 -> M₃) m = ![]
  证明: rfl
-/
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M ->ₗ[R] Fin 0 -> M₃) m = ![] :=
  rfl

/--
Definition of `LinearMap.vecCons` / `LinearMap.vecCons` 的定义

English:
definition LinearMap.vecCons
  signature: {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂)
  body: Fin.consLinearEquiv R (fun _ : Fin n.succ => M₂) ∘ₗ f.prod g

@[simp]

中文:
定义 线性映射.vecCons
  签名: {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] 有限集 n -> M₂)
  定义体: Fin.consLinearEquiv R (fun _ : Fin n.succ => M₂) ∘ₗ f.prod g

@[simp]

Depends on / 依赖: Fin.consLinearEquiv, consLinearEquiv, f.prod, n.succ
-/
def LinearMap.vecCons {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) : M ->ₗ[R] Fin n.succ -> M₂ :=
  Fin.consLinearEquiv R (fun _ : Fin n.succ => M₂) ∘ₗ f.prod g

@[simp]
/--
theorem `LinearMap.vecCons_apply` / 定理 `LinearMap.vecCons_apply`

English:
theorem LinearMap.vecCons_apply
  given: {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) (m : M)
  proof: rfl

中文:
定理 线性映射.vecCons_apply
  条件: {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] 有限集 n -> M₂) (m : M)
  证明: rfl
-/
theorem LinearMap.vecCons_apply {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl

variable (R) in
/--
To show a property `motive` of modules holds for arbitrary finite products of modules, it suffices
to show
1. `motive` is stable under isomorphism.
2. `motive` holds for the zero module.
3. `motive` holds for `M × N` if it holds for both `M` and `N`.

Since we need to apply `motive` to modules in `Type u` and in `Type (max u v)`, there is a second
`motive'` argument which is required to be equivalent to `motive` up to universe lifting by `equiv`.

See `Module.pi_induction'` for a version where `motive` assumes `AddCommGroup` instead.
-/
@[elab_as_elim]
/--
lemma `Module.pi_induction` / 引理 `Module.pi_induction`

English:
lemma Module.pi_induction
  statement: {ι : Type v} [Finite ι]
  proof: by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (

中文:
引理 模.pi_induction
  结论: {ι : 类型v} [有限 ι]
  证明: by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (

Depends on / 依赖: Fintype, Fintype.induction_empty_option, LinearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd, induction_empty_option, nonempty_fintype, piCongrLeft, piOptionEquivProd, revert
-/
lemma Module.pi_induction {ι : Type v} [Finite ι]
    (motive : forall (N : Type u) [AddCommMonoid N] [Module R N], Prop)
    (motive' : forall (N : Type (max u v)) [AddCommMonoid N] [Module R N], Prop)
    (equiv : forall {N : Type u} {N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') -> motive N -> motive' N')
    (equiv' : forall {N N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') -> motive' N -> motive' N')
    (unit : motive PUnit) (prod : forall {N : Type u} {N' : Type (max u v)} [AddCommMonoid N]
      [AddCommMonoid N'] [Module R N] [Module R N'], motive N -> motive' N' -> motive' (N × N'))
    (M : ι -> Type u) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
    (h : forall i, motive (M i)) : motive' (forall i, M i) := by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (hn _) (h _ fun i => hn i)

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/-- The empty bilinear map defeq to `Matrix.vecEmpty` -/
@[simps]
/--
Definition of `LinearMap.vecEmpty₂` / `LinearMap.vecEmpty₂` 的定义

English:
definition LinearMap.vecEmpty₂
  signature: : M ->ₗ[R] M₂ ->ₗ[R] Fin 0 -> M₃ where
  body: LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _

中文:
定义 线性映射.vecEmpty₂
  签名: : M ->ₗ[R] M₂ ->ₗ[R] 有限集 0 -> M₃ where
  定义体: LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _

Depends on / 依赖: LinearMap, LinearMap.vecEmpty, vecEmpty
-/
def LinearMap.vecEmpty₂ : M ->ₗ[R] M₂ ->ₗ[R] Fin 0 -> M₃ where
  toFun _ := LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _

/-- A bilinear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃` -/
@[simps]
/--
Definition of `LinearMap.vecCons₂` / `LinearMap.vecCons₂` 的定义

English:
definition LinearMap.vecCons₂
  signature: {n} (f : M ->ₗ[R] M₂ ->ₗ[R] M₃) (g : M ->ₗ[R] M₂ ->ₗ[R] Fin n -> M₃)
  body: LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]

中文:
定义 线性映射.vecCons₂
  签名: {n} (f : M ->ₗ[R] M₂ ->ₗ[R] M₃) (g : M ->ₗ[R] M₂ ->ₗ[R] 有限集 n -> M₃)
  定义体: LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]

Depends on / 依赖: LinearMap, LinearMap.vecCons, vecCons
-/
def LinearMap.vecCons₂ {n} (f : M ->ₗ[R] M₂ ->ₗ[R] M₃) (g : M ->ₗ[R] M₂ ->ₗ[R] Fin n -> M₃) :
    M ->ₗ[R] M₂ ->ₗ[R] Fin n.succ -> M₃ where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]

end CommSemiring

/-- A variant of `Module.pi_induction` that assumes `AddCommGroup` instead of `AddCommMonoid`. -/
@[elab_as_elim]
/--
lemma `Module.pi_induction'` / 引理 `Module.pi_induction'`

English:
lemma Module.pi_induction'
  statement: {ι : Type v} [Finite ι] (R : Type*) [Ring R]
  proof: by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (

中文:
引理 模.pi_induction'
  结论: {ι : 类型v} [有限 ι] (R : 类型) [环 R]
  证明: by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (

Depends on / 依赖: Fintype, Fintype.induction_empty_option, LinearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd, induction_empty_option, nonempty_fintype, piCongrLeft, piOptionEquivProd, revert
-/
lemma Module.pi_induction' {ι : Type v} [Finite ι] (R : Type*) [Ring R]
    (motive : forall (N : Type u) [AddCommGroup N] [Module R N], Prop)
    (motive' : forall (N : Type (max u v)) [AddCommGroup N] [Module R N], Prop)
    (equiv : forall {N : Type u} {N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') -> motive N -> motive' N')
    (equiv' : forall {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') -> motive' N -> motive' N')
    (unit : motive PUnit) (prod : forall {N : Type u} {N' : Type (max u v)} [AddCommGroup N]
      [AddCommGroup N'] [Module R N] [Module R N'], motive N -> motive' N' -> motive' (N × N'))
    (M : ι -> Type u) [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]
    (h : forall i, motive (M i)) : motive' (forall i, M i) := by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM => equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i => hM _)
    (fun M _ _ _ => equiv default unit) (fun α _ h M _ _ hn => ?_) ι
exact equiv' (LinearEquiv.piOptionEquivProd R).symm prod (hn _) (h _ fun i => hn i)

end Fin
