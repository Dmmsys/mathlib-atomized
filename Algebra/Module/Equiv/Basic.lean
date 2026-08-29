/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod

/-!
# Further results on (semi)linear equivalences.
-/

@[expose] public section

open Function

variable {R : Type*} {R₂ : Type*}
variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

section AddCommMonoid

namespace LinearEquiv

variable [Semiring R] [Semiring S] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]

section RestrictScalars

variable (R)
variable [Module R M] [Module R M₂] [Module S M] [Module S M₂]
  [LinearMap.CompatibleSMul M M₂ R S]

/-- If `M` and `M₂` are both `R`-semimodules and `S`-semimodules and `R`-semimodule structures
are defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear
equivalence from `M` to `M₂` is also an `R`-linear equivalence.

See also `LinearMap.restrictScalars`. -/
@[simps!, simps toLinearMap]
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : M ≃ₗ[S] M₂)
  body: f.toLinearMap.restrictScalars R
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

中文:
定义 restrictScalars
  签名: (f : M ≃ₗ[S] M₂)
  定义体: f.toLinearMap.restrictScalars R
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

Depends on / 依赖: f.toLinearMap.restrictScalars, restrictScalars, toLinearMap
-/
def restrictScalars (f : M ≃ₗ[S] M₂) : M ≃ₗ[R] M₂ where
  toLinearMap := f.toLinearMap.restrictScalars R
  invFun := f.symm
  left_inv := f.left_inv
  right_inv := f.right_inv

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun _ _ h =>
  ext (LinearEquiv.congr_fun h :)

@[simp]

中文:
定理 restrictScalars_injective
  证明: fun _ _ h =>
  ext (LinearEquiv.congr_fun h :)

@[simp]
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (M ≃ₗ[S] M₂) -> M ≃ₗ[R] M₂) := fun _ _ h =>
  ext (LinearEquiv.congr_fun h :)

@[simp]
/--
theorem `restrictScalars_inj` / 定理 `restrictScalars_inj`

English:
theorem restrictScalars_inj
  given: (f g : M ≃ₗ[S] M₂)
  proof: (restrictScalars_injective R).eq_iff

中文:
定理 restrictScalars_inj
  条件: (f g : M ≃ₗ[S] M₂)
  证明: (restrictScalars_injective R).eq_iff

Depends on / 依赖: eq_iff, restrictScalars_injective
-/
theorem restrictScalars_inj (f g : M ≃ₗ[S] M₂) :
    f.restrictScalars R = g.restrictScalars R ↔ f = g :=
  (restrictScalars_injective R).eq_iff

end RestrictScalars

/--
theorem `_root_.Module.End.isUnit_iff` / 定理 `_root_.Module.End.isUnit_iff`

English:
theorem _root_.Module.End.isUnit_iff
  given: [Module R M] (f : Module.End R M)
  proof: ⟨fun h =>
Function.bijective_iff_has_inverse.mpr
      ⟨h.unit.inv,
        ⟨Module.End.isUnit_inv_apply_apply_of_isUnit h,
        Module.End.isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H =>
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, Lin

中文:
定理 _root_.模.End.isUnit_iff
  条件: [模 R M] (f : 模.End R M)
  证明: ⟨fun h =>
Function.bijective_iff_has_inverse.mpr
      ⟨h.unit.inv,
        ⟨Module.End.isUnit_inv_apply_apply_of_isUnit h,
        Module.End.isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H =>
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, Lin

Depends on / 依赖: Equiv.ofBijective, Function, Function.bijective_iff_has_inverse.mpr, LinearMap, LinearMap.ext, Module, Module.End.isUnit_apply_inv_apply_of_isUnit, Module.End.isUnit_inv_apply_apply_of_isUnit, bijective_iff_has_inverse, e.left_inv, e.right_inv, e.symm, h.unit.inv, isUnit_apply_inv_apply_of_isUnit, isUnit_inv_apply_apply_of_isUnit, left_inv, ofBijective, right_inv
-/
theorem _root_.Module.End.isUnit_iff [Module R M] (f : Module.End R M) :
    IsUnit f ↔ Function.Bijective f :=
  ⟨fun h =>
Function.bijective_iff_has_inverse.mpr
      ⟨h.unit.inv,
        ⟨Module.End.isUnit_inv_apply_apply_of_isUnit h,
        Module.End.isUnit_apply_inv_apply_of_isUnit h⟩⟩,
    fun H =>
    let e : M ≃ₗ[R] M := { f, Equiv.ofBijective f H with }
    ⟨⟨_, e.symm, LinearMap.ext e.right_inv, LinearMap.ext e.left_inv⟩, rfl⟩⟩

section Automorphisms

variable [Module R M]

/--
Instance `automorphismGroup` / 实例 `automorphismGroup`

English:
instance automorphismGroup
  signature: : Group (M ≃ₗ[R] M) where
  body: g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
inv_mul_cancel f := ext f.left_inv

中文:
实例 automorphismGroup
  签名: : 群 (M ≃ₗ[R] M) where
  定义体: g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
inv_mul_cancel f := ext f.left_inv

Depends on / 依赖: g.trans
-/
instance automorphismGroup : Group (M ≃ₗ[R] M) where
  mul f g := g.trans f
  one := LinearEquiv.refl R M
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
inv_mul_cancel f := ext f.left_inv

/--
lemma `one_eq_refl` / 引理 `one_eq_refl`

English:
lemma one_eq_refl
  statement: (1 : M ≃ₗ[R] M) = refl R M
  proof: rfl

中文:
引理 one_eq_refl
  结论: (1 : M ≃ₗ[R] M) = refl R M
  证明: rfl
-/
lemma one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M := rfl
/--
lemma `mul_eq_trans` / 引理 `mul_eq_trans`

English:
lemma mul_eq_trans
  given: (f g : M ≃ₗ[R] M)
  statement: f * g = g.trans f
  proof: rfl

@[simp]

中文:
引理 mul_eq_trans
  条件: (f g : M ≃ₗ[R] M)
  结论: f * g = g.trans f
  证明: rfl

@[simp]
-/
lemma mul_eq_trans (f g : M ≃ₗ[R] M) : f * g = g.trans f := rfl

@[simp]
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ↑(1 : M ≃ₗ[R] M) = id
  proof: rfl

中文:
引理 coe_one
  结论: ↑(1 : M ≃ₗ[R] M) = id
  证明: rfl
-/
lemma coe_one : ↑(1 : M ≃ₗ[R] M) = id := rfl

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (f : M ≃ₗ[R] M)
  statement: ⇑f⁻¹ = ⇑f.symm
  proof: rfl

@[simp]

中文:
引理 coe_inv
  条件: (f : M ≃ₗ[R] M)
  结论: ⇑f⁻¹ = ⇑f.symm
  证明: rfl

@[simp]
-/
@[simp] lemma coe_inv (f : M ≃ₗ[R] M) : ⇑f⁻¹ = ⇑f.symm := rfl

@[simp]
/--
lemma `coe_toLinearMap_one` / 引理 `coe_toLinearMap_one`

English:
lemma coe_toLinearMap_one
  statement: (↑(1 : M ≃ₗ[R] M) : M ->ₗ[R] M) = LinearMap.id
  proof: rfl

@[simp]

中文:
引理 coe_toLinearMap_one
  结论: (↑(1 : M ≃ₗ[R] M) : M ->ₗ[R] M) = 线性映射.id
  证明: rfl

@[simp]
-/
lemma coe_toLinearMap_one : (↑(1 : M ≃ₗ[R] M) : M ->ₗ[R] M) = LinearMap.id := rfl

@[simp]
/--
lemma `coe_toLinearMap_mul` / 引理 `coe_toLinearMap_mul`

English:
lemma coe_toLinearMap_mul
  given: {e₁ e₂ : M ≃ₗ[R] M}
  proof: rfl

中文:
引理 coe_toLinearMap_mul
  条件: {e₁ e₂ : M ≃ₗ[R] M}
  证明: rfl
-/
lemma coe_toLinearMap_mul {e₁ e₂ : M ≃ₗ[R] M} :
    (↑(e₁ * e₂) : M ->ₗ[R] M) = (e₁ : M ->ₗ[R] M) * (e₂ : M ->ₗ[R] M) :=
  rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (e : M ≃ₗ[R] M) (n : Nat)
  statement: ⇑(e ^ n) = e^[n]
  proof: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

中文:
定理 coe_pow
  条件: (e : M ≃ₗ[R] M) (n : 自然数)
  结论: ⇑(e ^ n) = e^[n]
  证明: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

Depends on / 依赖: hom_coe_pow
-/
theorem coe_pow (e : M ≃ₗ[R] M) (n : Nat) : ⇑(e ^ n) = e^[n] := hom_coe_pow _ rfl (fun _ _ => rfl) _ _

/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: (e : M ≃ₗ[R] M) (n : Nat) (m : M)
  statement: (e ^ n) m = e^[n] m
  proof: congr_fun (coe_pow e n) m

中文:
定理 pow_apply
  条件: (e : M ≃ₗ[R] M) (n : 自然数) (m : M)
  结论: (e ^ n) m = e^[n] m
  证明: congr_fun (coe_pow e n) m

Depends on / 依赖: coe_pow, congr_fun
-/
theorem pow_apply (e : M ≃ₗ[R] M) (n : Nat) (m : M) : (e ^ n) m = e^[n] m := congr_fun (coe_pow e n) m

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
引理 mul_apply
  条件: (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
@[simp] lemma mul_apply (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
@[simps]
/--
Definition of `automorphismGroup.toLinearMapMonoidHom` / `automorphismGroup.toLinearMapMonoidHom` 的定义

English:
definition automorphismGroup.toLinearMapMonoidHom
  signature: : (M ≃ₗ[R] M) ->* M ->ₗ[R] M where
  body: e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 automorphismGroup.toLinearMapMonoidHom
  签名: : (M ≃ₗ[R] M) ->* M ->ₗ[R] M where
  定义体: e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: e.toLinearMap, toLinearMap
-/
def automorphismGroup.toLinearMapMonoidHom : (M ≃ₗ[R] M) ->* M ->ₗ[R] M where
  toFun e := e.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Instance `applyDistribMulAction` / 实例 `applyDistribMulAction`

English:
instance applyDistribMulAction
  signature: : DistribMulAction (M ≃ₗ[R] M) M where
  body: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 applyDistribMulAction
  签名: : 分配乘法作用 (M ≃ₗ[R] M) M where
  定义体: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
-/
instance applyDistribMulAction : DistribMulAction (M ≃ₗ[R] M) M where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (f : M ≃ₗ[R] M) (a : M)
  statement: f • a = f a
  proof: rfl

中文:
定理 smul_def
  条件: (f : M ≃ₗ[R] M) (a : M)
  结论: f • a = f a
  证明: rfl
-/
protected theorem smul_def (f : M ≃ₗ[R] M) (a : M) : f • a = f a :=
  rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (M ≃ₗ[R] M) M
  body: ⟨LinearEquiv.ext⟩

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (M ≃ₗ[R] M) M
  定义体: ⟨LinearEquiv.ext⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.ext
-/
instance apply_faithfulSMul : FaithfulSMul (M ≃ₗ[R] M) M :=
  ⟨LinearEquiv.ext⟩

/--
Instance `apply_smulCommClass` / 实例 `apply_smulCommClass`

English:
instance apply_smulCommClass
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: (e.map_smul_of_tower r m).symm

中文:
实例 apply_smulCommClass
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: (e.map_smul_of_tower r m).symm

Depends on / 依赖: e.map_smul_of_tower, map_smul_of_tower
-/
instance apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass S (M ≃ₗ[R] M) M where
  smul_comm r e m := (e.map_smul_of_tower r m).symm

/--
Instance `apply_smulCommClass'` / 实例 `apply_smulCommClass'`

English:
instance apply_smulCommClass'
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: SMulCommClass.symm _ _ _

中文:
实例 apply_smulCommClass'
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass (M ≃ₗ[R] M) S M :=
  SMulCommClass.symm _ _ _

end Automorphisms

section OfSubsingleton

variable (M M₂)
variable [Module R M] [Module R M₂] [Subsingleton M] [Subsingleton M₂]

/-- Any two modules that are subsingletons are isomorphic. -/
@[simps]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: : M ≃ₗ[R] M₂
  body: { (0 : M ->ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

@[simp]

中文:
定义 ofSubsingleton
  签名: : M ≃ₗ[R] M₂
  定义体: { (0 : M ->ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, invFun, left_inv, right_inv
-/
def ofSubsingleton : M ≃ₗ[R] M₂ :=
  { (0 : M ->ₗ[R] M₂) with
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ }

@[simp]
/--
theorem `ofSubsingleton_self` / 定理 `ofSubsingleton_self`

English:
theorem ofSubsingleton_self
  statement: ofSubsingleton M M = refl R M
  proof: by
  ext
  simp [eq_iff_true_of_subsingleton]

中文:
定理 ofSubsingleton_self
  结论: ofSubsingleton M M = refl R M
  证明: by
  ext
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem ofSubsingleton_self : ofSubsingleton M M = refl R M := by
  ext
  simp [eq_iff_true_of_subsingleton]

end OfSubsingleton

end LinearEquiv

namespace Module

/-- `g : R ≃+* S` is `R`-linear when the module structure on `S` is `Module.compHom S g` . -/
@[simps]
/--
Definition of `compHom.toLinearEquiv` / `compHom.toLinearEquiv` 的定义

English:
definition compHom.toLinearEquiv
  signature: {R S : Type*} [Semiring R] [Semiring S] (g : R ≃+* S)
  body: compHom S (↑g : R ->+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R ->+* S)
  { g with
    toFun := (g : R -> S)
    invFun := (g.symm : S -> R)
    map_smul' := g.map_mul }

中文:
定义 compHom.toLinearEquiv
  签名: {R S : 类型} [半环 R] [半环 S] (g : R ≃+* S)
  定义体: compHom S (↑g : R ->+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R ->+* S)
  { g with
    toFun := (g : R -> S)
    invFun := (g.symm : S -> R)
    map_smul' := g.map_mul }

Depends on / 依赖: compHom
-/
def compHom.toLinearEquiv {R S : Type*} [Semiring R] [Semiring S] (g : R ≃+* S) :
    haveI := compHom S (↑g : R ->+* S)
    R ≃ₗ[R] S :=
  letI := compHom S (↑g : R ->+* S)
  { g with
    toFun := (g : R -> S)
    invFun := (g.symm : S -> R)
    map_smul' := g.map_mul }

end Module

namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Group S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the group defines a linear equivalence.

This is a stronger version of `DistribMulAction.toAddEquiv`. -/
@[simps!]
/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (s : S)
  body: { toAddEquiv M s, DistribSMul.toLinearMap R M s with }

中文:
定义 toLinearEquiv
  签名: (s : S)
  定义体: { toAddEquiv M s, DistribSMul.toLinearMap R M s with }

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, toAddEquiv, toLinearMap
-/
def toLinearEquiv (s : S) : M ≃ₗ[R] M :=
  { toAddEquiv M s, DistribSMul.toLinearMap R M s with }

/-- Each element of the group defines a module automorphism.

This is a stronger version of `DistribMulAction.toAddAut`. -/
@[simps]
/--
Definition of `toModuleAut` / `toModuleAut` 的定义

English:
definition toModuleAut
  signature: : S ->* M ≃ₗ[R] M where
  body: toLinearEquiv R M
map_one' := LinearEquiv.ext one_smul _
map_mul' _ _ := LinearEquiv.ext mul_smul _ _

中文:
定义 toModuleAut
  签名: : S ->* M ≃ₗ[R] M where
  定义体: toLinearEquiv R M
map_one' := LinearEquiv.ext one_smul _
map_mul' _ _ := LinearEquiv.ext mul_smul _ _

Depends on / 依赖: toLinearEquiv
-/
def toModuleAut : S ->* M ≃ₗ[R] M where
  toFun := toLinearEquiv R M
map_one' := LinearEquiv.ext one_smul _
map_mul' _ _ := LinearEquiv.ext mul_smul _ _

end DistribMulAction

/--
theorem `LinearEquiv.smul_refl` / 定理 `LinearEquiv.smul_refl`

English:
theorem LinearEquiv.smul_refl
  statement: [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
  proof: SMulCommClass.symm R Sˣ M
    α • refl R M = DistribMulAction.toLinearEquiv R M α := rfl

中文:
定理 线性等价.smul_refl
  结论: [半环 R] [半环 S] [加法交换幺半群 M] [模 R M] [模 S M]
  证明: SMulCommClass.symm R Sˣ M
    α • refl R M = DistribMulAction.toLinearEquiv R M α := rfl

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
theorem LinearEquiv.smul_refl [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M] (α : Sˣ) :
    letI := SMulCommClass.symm R Sˣ M
    α • refl R M = DistribMulAction.toLinearEquiv R M α := rfl

namespace AddEquiv

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂]
variable (e : M ≃+ M₂)

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (h : forall (c : R) (x), e (c • x) = c • e x)
  body: { e with map_smul' := h }

@[simp]

中文:
定义 toLinearEquiv
  签名: (h : 对任意 (c : R) (x), e (c • x) = c • e x)
  定义体: { e with map_smul' := h }

@[simp]

Depends on / 依赖: map_smul
-/
def toLinearEquiv (h : forall (c : R) (x), e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
  { e with map_smul' := h }

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (h : forall (c : R) (x), e (c • x) = c • e x)
  statement: ⇑(e.toLinearEquiv h) = e
  proof: rfl

@[simp]

中文:
定理 coe_toLinearEquiv
  条件: (h : 对任意 (c : R) (x), e (c • x) = c • e x)
  结论: ⇑(e.toLinearEquiv h) = e
  证明: rfl

@[simp]
-/
theorem coe_toLinearEquiv (h : forall (c : R) (x), e (c • x) = c • e x) : ⇑(e.toLinearEquiv h) = e :=
  rfl

@[simp]
/--
theorem `coe_toLinearEquiv_symm` / 定理 `coe_toLinearEquiv_symm`

English:
theorem coe_toLinearEquiv_symm
  given: (h : forall (c : R) (x), e (c • x) = c • e x)
  proof: rfl

中文:
定理 coe_toLinearEquiv_symm
  条件: (h : 对任意 (c : R) (x), e (c • x) = c • e x)
  证明: rfl
-/
theorem coe_toLinearEquiv_symm (h : forall (c : R) (x), e (c • x) = c • e x) :
    ⇑(e.toLinearEquiv h).symm = e.symm :=
  rfl

/--
Definition of `toNatLinearEquiv` / `toNatLinearEquiv` 的定义

English:
definition toNatLinearEquiv
  signature: : M ≃ₗ[Nat] M₂
  body: e.toLinearEquiv fun c a => by rw [map_nsmul]

@[simp]

中文:
定义 to自然数LinearEquiv
  签名: : M ≃ₗ[自然数] M₂
  定义体: e.toLinearEquiv fun c a => by rw [map_nsmul]

@[simp]

Depends on / 依赖: e.toLinearEquiv, map_nsmul, toLinearEquiv
-/
def toNatLinearEquiv : M ≃ₗ[Nat] M₂ :=
  e.toLinearEquiv fun c a => by rw [map_nsmul]

@[simp]
/--
theorem `coe_toNatLinearEquiv` / 定理 `coe_toNatLinearEquiv`

English:
theorem coe_toNatLinearEquiv
  statement: ⇑e.toNatLinearEquiv = e
  proof: rfl

@[simp]

中文:
定理 coe_to自然数LinearEquiv
  结论: ⇑e.to自然数LinearEquiv = e
  证明: rfl

@[simp]
-/
theorem coe_toNatLinearEquiv : ⇑e.toNatLinearEquiv = e :=
  rfl

@[simp]
/--
theorem `coe_symm_toNatLinearEquiv` / 定理 `coe_symm_toNatLinearEquiv`

English:
theorem coe_symm_toNatLinearEquiv
  statement: ⇑e.toNatLinearEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_to自然数LinearEquiv
  结论: ⇑e.to自然数LinearEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toNatLinearEquiv : ⇑e.toNatLinearEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `toNatLinearEquiv_toAddEquiv` / 定理 `toNatLinearEquiv_toAddEquiv`

English:
theorem toNatLinearEquiv_toAddEquiv
  statement: ↑e.toNatLinearEquiv = e
  proof: rfl

@[simp]

中文:
定理 to自然数LinearEquiv_toAddEquiv
  结论: ↑e.to自然数LinearEquiv = e
  证明: rfl

@[simp]
-/
theorem toNatLinearEquiv_toAddEquiv : ↑e.toNatLinearEquiv = e :=
  rfl

@[simp]
/--
theorem `_root_.LinearEquiv.toAddEquiv_toNatLinearEquiv` / 定理 `_root_.LinearEquiv.toAddEquiv_toNatLinearEquiv`

English:
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv
  given: (e : M ≃ₗ[Nat] M₂)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 _root_.线性等价.toAddEquiv_to自然数LinearEquiv
  条件: (e : M ≃ₗ[自然数] M₂)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem _root_.LinearEquiv.toAddEquiv_toNatLinearEquiv (e : M ≃ₗ[Nat] M₂) :
    AddEquiv.toNatLinearEquiv ↑e = e :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toNatLinearEquiv_symm` / 定理 `toNatLinearEquiv_symm`

English:
theorem toNatLinearEquiv_symm
  statement: e.symm.toNatLinearEquiv = e.toNatLinearEquiv.symm
  proof: rfl

@[simp]

中文:
定理 to自然数LinearEquiv_symm
  结论: e.symm.to自然数LinearEquiv = e.to自然数LinearEquiv.symm
  证明: rfl

@[simp]
-/
theorem toNatLinearEquiv_symm : e.symm.toNatLinearEquiv = e.toNatLinearEquiv.symm :=
  rfl

@[simp]
/--
theorem `toNatLinearEquiv_refl` / 定理 `toNatLinearEquiv_refl`

English:
theorem toNatLinearEquiv_refl
  statement: (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl Nat M
  proof: rfl

@[simp]

中文:
定理 to自然数LinearEquiv_refl
  结论: (加法等价.refl M).to自然数LinearEquiv = 线性等价.refl 自然数 M
  证明: rfl

@[simp]
-/
theorem toNatLinearEquiv_refl : (AddEquiv.refl M).toNatLinearEquiv = LinearEquiv.refl Nat M :=
  rfl

@[simp]
/--
theorem `toNatLinearEquiv_trans` / 定理 `toNatLinearEquiv_trans`

English:
theorem toNatLinearEquiv_trans
  given: (e₂ : M₂ ≃+ M₃)
  proof: rfl

中文:
定理 to自然数LinearEquiv_trans
  条件: (e₂ : M₂ ≃+ M₃)
  证明: rfl
-/
theorem toNatLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toNatLinearEquiv = e.toNatLinearEquiv.trans e₂.toNatLinearEquiv :=
  rfl

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
-- See note [implicit instance arguments]
variable {modM : Module Int M} {modM₂ : Module Int M₂} {modM₃ : Module Int M₃} (e : M ≃+ M₂)

/--
Definition of `toIntLinearEquiv` / `toIntLinearEquiv` 的定义

English:
definition toIntLinearEquiv
  signature: : M ≃ₗ[Int] M₂
  body: by
  refine e.toLinearEquiv fun c a => ?_
  convert! e.toAddMonoidHom.map_zsmul c a using 1
  · exact congr(e $(int_smul_eq_zsmul ..))
  · exact int_smul_eq_zsmul ..

@[simp]

中文:
定义 to整数LinearEquiv
  签名: : M ≃ₗ[整数] M₂
  定义体: by
  refine e.toLinearEquiv fun c a => ?_
  convert! e.toAddMonoidHom.map_zsmul c a using 1
  · exact congr(e $(int_smul_eq_zsmul ..))
  · exact int_smul_eq_zsmul ..

@[simp]

Depends on / 依赖: convert, e.toAddMonoidHom.map_zsmul, e.toLinearEquiv, int_smul_eq_zsmul, map_zsmul, toAddMonoidHom, toLinearEquiv
-/
def toIntLinearEquiv : M ≃ₗ[Int] M₂ := by
  refine e.toLinearEquiv fun c a => ?_
  convert! e.toAddMonoidHom.map_zsmul c a using 1
  · exact congr(e $(int_smul_eq_zsmul ..))
  · exact int_smul_eq_zsmul ..

@[simp]
/--
theorem `coe_toIntLinearEquiv` / 定理 `coe_toIntLinearEquiv`

English:
theorem coe_toIntLinearEquiv
  statement: ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)) = e
  proof: rfl

@[simp]

中文:
定理 coe_to整数LinearEquiv
  结论: ⇑(e.to整数LinearEquiv (modM := modM) (modM₂ := modM₂)) = e
  证明: rfl

@[simp]
-/
theorem coe_toIntLinearEquiv : ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)) = e := rfl

@[simp]
/--
theorem `coe_symm_toIntLinearEquiv` / 定理 `coe_symm_toIntLinearEquiv`

English:
theorem coe_symm_toIntLinearEquiv
  proof: rfl

@[simp]

中文:
定理 coe_symm_to整数LinearEquiv
  证明: rfl

@[simp]

Depends on / 依赖: e.symm
-/
theorem coe_symm_toIntLinearEquiv :
    ⇑(e.toIntLinearEquiv (modM := modM) (modM₂ := modM₂)).symm = e.symm :=
  rfl

@[simp]
/--
theorem `toIntLinearEquiv_toAddEquiv` / 定理 `toIntLinearEquiv_toAddEquiv`

English:
theorem toIntLinearEquiv_toAddEquiv
  statement: ↑e.toIntLinearEquiv = e
  proof: by
  ext
  rfl

@[simp]

中文:
定理 to整数LinearEquiv_toAddEquiv
  结论: ↑e.to整数LinearEquiv = e
  证明: by
  ext
  rfl

@[simp]
-/
theorem toIntLinearEquiv_toAddEquiv : ↑e.toIntLinearEquiv = e := by
  ext
  rfl

@[simp]
/--
theorem `_root_.LinearEquiv.toAddEquiv_toIntLinearEquiv` / 定理 `_root_.LinearEquiv.toAddEquiv_toIntLinearEquiv`

English:
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv
  given: (e : M ≃ₗ[Int] M₂)
  proof: DFunLike.coe_injective rfl

@[simp]

中文:
定理 _root_.线性等价.toAddEquiv_to整数LinearEquiv
  条件: (e : M ≃ₗ[整数] M₂)
  证明: DFunLike.coe_injective rfl

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem _root_.LinearEquiv.toAddEquiv_toIntLinearEquiv (e : M ≃ₗ[Int] M₂) :
    AddEquiv.toIntLinearEquiv (e : M ≃+ M₂) = e :=
  DFunLike.coe_injective rfl

@[simp]
/--
theorem `toIntLinearEquiv_symm` / 定理 `toIntLinearEquiv_symm`

English:
theorem toIntLinearEquiv_symm
  proof: rfl

@[simp]

中文:
定理 to整数LinearEquiv_symm
  证明: rfl

@[simp]

Depends on / 依赖: e.toIntLinearEquiv.symm, toIntLinearEquiv
-/
theorem toIntLinearEquiv_symm :
    e.symm.toIntLinearEquiv (modM := modM₂) (modM₂ := modM) = e.toIntLinearEquiv.symm := rfl

@[simp]
/--
theorem `toIntLinearEquiv_refl` / 定理 `toIntLinearEquiv_refl`

English:
theorem toIntLinearEquiv_refl
  statement: (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl Int M
  proof: rfl

@[simp]

中文:
定理 to整数LinearEquiv_refl
  结论: (加法等价.refl M).to整数LinearEquiv = 线性等价.refl 整数 M
  证明: rfl

@[simp]
-/
theorem toIntLinearEquiv_refl : (AddEquiv.refl M).toIntLinearEquiv = LinearEquiv.refl Int M :=
  rfl

@[simp]
/--
theorem `toIntLinearEquiv_trans` / 定理 `toIntLinearEquiv_trans`

English:
theorem toIntLinearEquiv_trans
  given: (e₂ : M₂ ≃+ M₃)
  proof: rfl

中文:
定理 to整数LinearEquiv_trans
  条件: (e₂ : M₂ ≃+ M₃)
  证明: rfl
-/
theorem toIntLinearEquiv_trans (e₂ : M₂ ≃+ M₃) :
    (e.trans e₂).toIntLinearEquiv (modM := modM) (modM₂ := modM₃) =
      (e.toIntLinearEquiv (modM₂ := modM₂)).trans e₂.toIntLinearEquiv :=
  rfl

end AddCommGroup

end AddEquiv

namespace LinearMap

/--
Definition of `piApply` / `piApply` 的定义

English:
definition piApply
  signature: {V : M -> Type*} [CommSemiring R] [forall x, AddCommMonoid (V x)] [forall x, Module R (V x)]
  body: { toFun s x := e x (s x)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp]

中文:
定义 piApply
  签名: {V : M -> 类型} [交换半环 R] [对任意 x, 加法交换幺半群 (V x)] [对任意 x, 模 R (V x)]
  定义体: { toFun s x := e x (s x)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp]

Depends on / 依赖: intros, map_add, map_smul
-/
def piApply {V : M -> Type*} [CommSemiring R] [forall x, AddCommMonoid (V x)] [forall x, Module R (V x)] :
    (Π x : M, V x ->ₗ[R] R) ->ₗ[R] (Π x : M, V x) ->ₗ[R] M -> R where
  toFun e :=
    { toFun s x := e x (s x)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

@[simp]
/--
theorem `piApply_apply` / 定理 `piApply_apply`

English:
theorem piApply_apply
  statement: {V : M -> Type*}
  proof: rfl

@[simp]

中文:
定理 piApply_apply
  结论: {V : M -> 类型}
  证明: rfl

@[simp]
-/
theorem piApply_apply {V : M -> Type*}
    [CommSemiring R] [forall x, AddCommMonoid (V x)] [forall x, Module R (V x)]
    (e : Π x : M, V x ->ₗ[R] R) (s : Π x : M, V x) :
    piApply e s = fun x => e x (s x) :=
  rfl

@[simp]
/--
theorem `piApply_apply_apply` / 定理 `piApply_apply_apply`

English:
theorem piApply_apply_apply
  statement: {V : M -> Type*}
  proof: rfl

中文:
定理 piApply_apply_apply
  结论: {V : M -> 类型}
  证明: rfl
-/
theorem piApply_apply_apply {V : M -> Type*}
    [CommSemiring R] [forall x, AddCommMonoid (V x)] [forall x, Module R (V x)]
    (e : Π x : M, V x ->ₗ[R] R) (s : Π x : M, V x) (x : M) :
    piApply e s x = e x (s x) :=
  rfl

variable (R S M)
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This is an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
/--
Definition of `ringLmapEquivSelf` / `ringLmapEquivSelf` 的定义

English:
definition ringLmapEquivSelf
  signature: [Module S M] [SMulCommClass R S M]
  body: { applyₗ' S (1 : R) with
    toFun := fun f => f 1
    invFun := smulRight (1 : R ->ₗ[R] R)
    left_inv := fun f => by
      ext
      simp only [coe_smulRight, Module.End.one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x => by simp }

中文:
定义 ringLmapEquivSelf
  签名: [模 S M] [标量交换类 R S M]
  定义体: { applyₗ' S (1 : R) with
    toFun := fun f => f 1
    invFun := smulRight (1 : R ->ₗ[R] R)
    left_inv := fun f => by
      ext
      simp only [coe_smulRight, Module.End.one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x => by simp }

Depends on / 依赖: Module, Module.End.one_apply, coe_smulRight, invFun, left_inv, map_smul, mul_one, one_apply, right_inv, smulRight, smul_eq_mul
-/
def ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R ->ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with
    toFun := fun f => f 1
    invFun := smulRight (1 : R ->ₗ[R] R)
    left_inv := fun f => by
      ext
      simp only [coe_smulRight, Module.End.one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x => by simp }

end LinearMap

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
/--
Definition of `addMonoidHomLequivNat` / `addMonoidHomLequivNat` 的定义

English:
definition addMonoidHomLequivNat
  signature: {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
  body: AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 addMonoidHomLequiv自然数
  签名: {A B : 类型} (R : 类型) [半环 R] [加法交换幺半群 A]
  定义体: AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toNatLinearMap, toNatLinearMap
-/
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A ->+ B) ≃ₗ[R] A ->ₗ[Nat] B where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
/--
Definition of `addMonoidHomLequivInt` / `addMonoidHomLequivInt` 的定义

English:
definition addMonoidHomLequivInt
  signature: {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
  body: AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 addMonoidHomLequiv整数
  签名: {A B : 类型} (R : 类型) [半环 R] [加法交换群 A] [加法交换群 B]
  定义体: AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toIntLinearMap, toIntLinearMap
-/
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A ->+ B) ≃ₗ[R] A ->ₗ[Int] B where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Definition of `addMonoidEndRingEquivInt` / `addMonoidEndRingEquivInt` 的定义

English:
definition addMonoidEndRingEquivInt
  signature: (A : Type*) [AddCommGroup A]
  body: { addMonoidHomLequivInt (B := A) Int with
    map_mul' := fun _ _ => rfl }

中文:
定义 addMonoidEndRingEquiv整数
  签名: (A : 类型) [加法交换群 A]
  定义体: { addMonoidHomLequivInt (B := A) Int with
    map_mul' := fun _ _ => rfl }
-/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End Int A :=
  { addMonoidHomLequivInt (B := A) Int with
    map_mul' := fun _ _ => rfl }

namespace LinearEquiv

section AddCommMonoid

section Subsingleton

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

section Module

variable [Subsingleton M] [Subsingleton M₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ≃ₛₗ[σ₁₂] M₂)
  body: ⟨{ (0 : M ->ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

中文:
实例 :
  签名: 零 (M ≃ₛₗ[σ₁₂] M₂)
  定义体: ⟨{ (0 : M ->ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, invFun, left_inv, right_inv
-/
instance : Zero (M ≃ₛₗ[σ₁₂] M₂) :=
  ⟨{ (0 : M ->ₛₗ[σ₁₂] M₂) with
      toFun := 0
      invFun := 0
      right_inv := Subsingleton.elim _
      left_inv := Subsingleton.elim _ }⟩

-- Even though these are implied by `Subsingleton.elim` via the `Unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
@[simp]
/--
theorem `zero_symm` / 定理 `zero_symm`

English:
theorem zero_symm
  statement: (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0
  proof: rfl

@[simp]

中文:
定理 zero_symm
  结论: (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0
  证明: rfl

@[simp]
-/
theorem zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 :=
  rfl

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0
  证明: rfl
-/
theorem coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x : M)
  statement: (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (x : M)
  结论: (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0
  证明: rfl
-/
theorem zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (M ≃ₛₗ[σ₁₂] M₂)
  body: toLinearMap_injective (Subsingleton.elim _ _)
  default := 0

中文:
实例 :
  签名: 唯一 (M ≃ₛₗ[σ₁₂] M₂)
  定义体: toLinearMap_injective (Subsingleton.elim _ _)
  default := 0

Depends on / 依赖: Subsingleton, Subsingleton.elim, toLinearMap_injective
-/
instance : Unique (M ≃ₛₗ[σ₁₂] M₂) where
  uniq _ := toLinearMap_injective (Subsingleton.elim _ _)
  default := 0

end Module

/--
Instance `uniqueOfSubsingleton` / 实例 `uniqueOfSubsingleton`

English:
instance uniqueOfSubsingleton
  signature: [Subsingleton R] [Subsingleton R₂]
  body: by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance

中文:
实例 uniqueOfSubsingleton
  签名: [子单例 R] [子单例 R₂]
  定义体: by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance

Depends on / 依赖: Module, Module.subsingleton, infer_instance, subsingleton
-/
instance uniqueOfSubsingleton [Subsingleton R] [Subsingleton R₂] : Unique (M ≃ₛₗ[σ₁₂] M₂) := by
  haveI := Module.subsingleton R M
  haveI := Module.subsingleton R₂ M₂
  infer_instance

end Subsingleton

section Uncurry

variable [Semiring R]
variable [AddCommMonoid M] [Module R M]
variable (V V₂ R M)

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: : (V × V₂ -> M) ≃ₗ[R] V -> V₂ -> M
  body: { Equiv.curry _ _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]

中文:
定义 curry
  签名: : (V × V₂ -> M) ≃ₗ[R] V -> V₂ -> M
  定义体: { Equiv.curry _ _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
-/
protected def curry : (V × V₂ -> M) ≃ₗ[R] V -> V₂ -> M :=
  { Equiv.curry _ _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
/--
theorem `coe_curry` / 定理 `coe_curry`

English:
theorem coe_curry
  statement: ⇑(LinearEquiv.curry R M V V₂) = curry
  proof: rfl

@[simp]

中文:
定理 coe_curry
  结论: ⇑(线性等价.curry R M V V₂) = curry
  证明: rfl

@[simp]
-/
theorem coe_curry : ⇑(LinearEquiv.curry R M V V₂) = curry :=
  rfl

@[simp]
/--
theorem `coe_curry_symm` / 定理 `coe_curry_symm`

English:
theorem coe_curry_symm
  statement: ⇑(LinearEquiv.curry R M V V₂).symm = uncurry
  proof: rfl

中文:
定理 coe_curry_symm
  结论: ⇑(线性等价.curry R M V V₂).symm = uncurry
  证明: rfl
-/
theorem coe_curry_symm : ⇑(LinearEquiv.curry R M V V₂).symm = uncurry :=
  rfl

end Uncurry

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₁] M)


/--
Definition of `ofLinearMap` / `ofLinearMap` 的定义

English:
definition ofLinearMap
  signature: (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  body: f
  invFun := g
  left_inv := LinearMap.ext_iff.1 h₂
  right_inv := LinearMap.ext_iff.1 h₁

@[simp low]

中文:
定义 ofLinearMap
  签名: (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  定义体: f
  invFun := g
  left_inv := LinearMap.ext_iff.1 h₂
  right_inv := LinearMap.ext_iff.1 h₁

@[simp low]
-/
def ofLinearMap (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂ where
  __ := f
  invFun := g
  left_inv := LinearMap.ext_iff.1 h₂
  right_inv := LinearMap.ext_iff.1 h₁

@[simp low]
/--
theorem `coe_ofLinearMap` / 定理 `coe_ofLinearMap`

English:
theorem coe_ofLinearMap
  given: (h₁ h₂)
  statement: ⇑(ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f
  proof: rfl

@[simp low]

中文:
定理 coe_ofLinearMap
  条件: (h₁ h₂)
  结论: ⇑(ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f
  证明: rfl

@[simp low]
-/
theorem coe_ofLinearMap (h₁ h₂) : ⇑(ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[simp low]
/--
theorem `symm_ofLinearMap` / 定理 `symm_ofLinearMap`

English:
theorem symm_ofLinearMap
  given: (h₁ h₂)
  proof: rfl

中文:
定理 symm_ofLinearMap
  条件: (h₁ h₂)
  证明: rfl
-/
theorem symm_ofLinearMap (h₁ h₂) :
    (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = (ofLinearMap g f h₂ h₁) :=
  rfl

/-- If a linear map has an inverse, it is a linear equivalence. -/
@[deprecated ofLinearMap (since := "2026-06-23")]
/--
Definition of `ofLinear` / `ofLinear` 的定义

English:
abbreviation ofLinear
  signature: (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  body: ofLinearMap f g h₁ h₂

@[deprecated coe_ofLinearMap (since := "2026-06-23")]

中文:
缩写 ofLinear
  签名: (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
  定义体: ofLinearMap f g h₁ h₂

@[deprecated coe_ofLinearMap (since := "2026-06-23")]

Depends on / 依赖: ofLinearMap
-/
abbrev ofLinear (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) : M ≃ₛₗ[σ₁₂] M₂ := ofLinearMap f g h₁ h₂

@[deprecated coe_ofLinearMap (since := "2026-06-23")]
/--
theorem `ofLinear_apply` / 定理 `ofLinear_apply`

English:
theorem ofLinear_apply
  given: {h₁ h₂} (x : M)
  statement: (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x
  proof: rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `coe_ofLinearMap`"
  (since := "2026-06-23")]

中文:
定理 ofLinear_apply
  条件: {h₁ h₂} (x : M)
  结论: (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x
  证明: rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `coe_ofLinearMap`"
  (since := "2026-06-23")]
-/
theorem ofLinear_apply {h₁ h₂} (x : M) : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) x = f x :=
  rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `coe_ofLinearMap`"
  (since := "2026-06-23")]
/--
theorem `ofLinear_symm_apply` / 定理 `ofLinear_symm_apply`

English:
theorem ofLinear_symm_apply
  given: {h₁ h₂} (x : M₂)
  proof: rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `toLinearMap_ofLinearMap`"
  (since := "2026-06-23")]

中文:
定理 ofLinear_symm_apply
  条件: {h₁ h₂} (x : M₂)
  证明: rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `toLinearMap_ofLinearMap`"
  (since := "2026-06-23")]
-/
theorem ofLinear_symm_apply {h₁ h₂} (x : M₂) :
    (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm x = g x :=
  rfl

@[deprecated "Follows from simp lemmas `symm_ofLinearMap` and `toLinearMap_ofLinearMap`"
  (since := "2026-06-23")]
/--
theorem `ofLinear_symm_toLinearMap` / 定理 `ofLinear_symm_toLinearMap`

English:
theorem ofLinear_symm_toLinearMap
  given: {h₁ h₂}
  statement: (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g
  proof: rfl

@[simp]

中文:
定理 ofLinear_symm_toLinearMap
  条件: {h₁ h₂}
  结论: (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g
  证明: rfl

@[simp]
-/
theorem ofLinear_symm_toLinearMap {h₁ h₂} : (ofLinear f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂).symm = g := rfl

@[simp]
/--
theorem `toLinearMap_ofLinearMap` / 定理 `toLinearMap_ofLinearMap`

English:
theorem toLinearMap_ofLinearMap
  given: (h₁ h₂)
  statement: (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f
  proof: rfl

@[deprecated (since := "2026-08-04")] alias ofLinear_toLinearMap := toLinearMap_ofLinearMap

中文:
定理 toLinearMap_ofLinearMap
  条件: (h₁ h₂)
  结论: (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f
  证明: rfl

@[deprecated (since := "2026-08-04")] alias ofLinear_toLinearMap := toLinearMap_ofLinearMap
-/
theorem toLinearMap_ofLinearMap (h₁ h₂) : (ofLinearMap f g h₁ h₂ : M ≃ₛₗ[σ₁₂] M₂) = f := rfl

@[deprecated (since := "2026-08-04")] alias ofLinear_toLinearMap := toLinearMap_ofLinearMap

end

end AddCommMonoid

section Neg

variable (R) [Semiring R] [AddCommGroup M] [Module R M]

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : M ≃ₗ[R] M
  body: { Equiv.neg M, (-LinearMap.id : M ->ₗ[R] M) with }

中文:
定义 neg
  签名: : M ≃ₗ[R] M
  定义体: { Equiv.neg M, (-LinearMap.id : M ->ₗ[R] M) with }

Depends on / 依赖: Equiv.neg, LinearMap, LinearMap.id
-/
def neg : M ≃ₗ[R] M :=
  { Equiv.neg M, (-LinearMap.id : M ->ₗ[R] M) with }

variable {R}

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  statement: ⇑(neg R : M ≃ₗ[R] M) = -id
  proof: rfl

中文:
定理 coe_neg
  结论: ⇑(neg R : M ≃ₗ[R] M) = -id
  证明: rfl
-/
theorem coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (x : M)
  statement: neg R x = -x
  proof: by simp

@[simp]

中文:
定理 neg_apply
  条件: (x : M)
  结论: neg R x = -x
  证明: by simp

@[simp]
-/
theorem neg_apply (x : M) : neg R x = -x := by simp

@[simp]
/--
theorem `symm_neg` / 定理 `symm_neg`

English:
theorem symm_neg
  statement: (neg R : M ≃ₗ[R] M).symm = neg R
  proof: rfl

中文:
定理 symm_neg
  结论: (neg R : M ≃ₗ[R] M).symm = neg R
  证明: rfl
-/
theorem symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R :=
  rfl

end Neg

section Semiring

open LinearMap

section Semilinear

variable {R₁ R₂ R₁' R₂' : Type*} {M₁ M₂ M₁' M₂' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₁'] [Semiring R₂']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₁'] [AddCommMonoid M₂']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₁' M₁'] [Module R₂' M₂']
variable {σ₁₂ : R₁ ->+* R₂} {σ₂₁ : R₂ ->+* R₁} {σ₁'₂' : R₁' ->+* R₂'} {σ₂'₁' : R₂' ->+* R₁'}
variable {σ₁₁' : R₁ ->+* R₁'} {σ₂₂' : R₂ ->+* R₂'}
variable {σ₂₁' : R₂ ->+* R₁'} {σ₁₂' : R₁ ->+* R₂'}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']

/--
Definition of `arrowCongrAddEquiv` / `arrowCongrAddEquiv` 的定义

English:
definition arrowCongrAddEquiv
  signature: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  body: (e₂.comp f).comp e₁.symm.toLinearMap
  invFun f := (e₂.symm.comp f).comp e₁.toLinearMap
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_a

中文:
定义 arrowCongrAddEquiv
  签名: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  定义体: (e₂.comp f).comp e₁.symm.toLinearMap
  invFun f := (e₂.symm.comp f).comp e₁.toLinearMap
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_a
-/
@[simps] def arrowCongrAddEquiv (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ ->ₛₗ[σ₁₁'] M₁') ≃+ (M₂ ->ₛₗ[σ₂₂'] M₂') where
  toFun f := (e₂.comp f).comp e₁.symm.toLinearMap
  invFun f := (e₂.symm.comp f).comp e₁.toLinearMap
  left_inv f := by
    ext x
    simp only [symm_apply_apply, Function.comp_apply, coe_comp, coe_coe]
  right_inv f := by
    ext x
    simp only [Function.comp_apply, apply_symm_apply, coe_comp, coe_coe]
  map_add' f g := by
    ext x
    simp only [map_add, add_apply, Function.comp_apply, coe_comp, coe_coe]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `conjRingEquiv` / `conjRingEquiv` 的定义

English:
definition conjRingEquiv
  signature: (e : M₁ ≃ₛₗ[σ₁₂] M₂)
  body: arrowCongrAddEquiv e e
  map_mul' _ _ := by ext; simp [arrowCongrAddEquiv]

中文:
定义 conjRingEquiv
  签名: (e : M₁ ≃ₛₗ[σ₁₂] M₂)
  定义体: arrowCongrAddEquiv e e
  map_mul' _ _ := by ext; simp [arrowCongrAddEquiv]
-/
@[simps!] def conjRingEquiv (e : M₁ ≃ₛₗ[σ₁₂] M₂) : Module.End R₁ M₁ ≃+* Module.End R₂ M₂ where
  __ := arrowCongrAddEquiv e e
  map_mul' _ _ := by ext; simp [arrowCongrAddEquiv]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `domMulActCongrRight` / `domMulActCongrRight` 的定义

English:
definition domMulActCongrRight
  signature: [Semiring S] [Module S M₁]
  body: arrowCongrAddEquiv (.refl ..) e₂
  map_smul' := DomMulAct.mk.forall_congr_right.mp fun _ _ => by ext; simp

中文:
定义 domMulActCongrRight
  签名: [半环 S] [模 S M₁]
  定义体: arrowCongrAddEquiv (.refl ..) e₂
  map_smul' := DomMulAct.mk.forall_congr_right.mp fun _ _ => by ext; simp
-/
@[simps] def domMulActCongrRight [Semiring S] [Module S M₁]
    [SMulCommClass R₁ S M₁] [RingHomCompTriple σ₁₂' σ₂'₁' σ₁₁']
    (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') : (M₁ ->ₛₗ[σ₁₁'] M₁') ≃ₗ[Sᵈᵐᵃ] (M₁ ->ₛₗ[σ₁₂'] M₂') where
  __ := arrowCongrAddEquiv (.refl ..) e₂
  map_smul' := DomMulAct.mk.forall_congr_right.mp fun _ _ => by ext; simp

end Semilinear

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

open LinearMap

/--
Definition of `smulOfUnit` / `smulOfUnit` 的定义

English:
definition smulOfUnit
  signature: (a : Rˣ)
  body: DistribMulAction.toLinearEquiv R M a

中文:
定义 smulOfUnit
  签名: (a : Rˣ)
  定义体: DistribMulAction.toLinearEquiv R M a

Depends on / 依赖: DistribMulAction, DistribMulAction.toLinearEquiv, toLinearEquiv
-/
def smulOfUnit (a : Rˣ) : M ≃ₗ[R] M :=
  DistribMulAction.toLinearEquiv R M a

section arrowCongr

-- Difference from above: `R₁` and `R₂` are commutative
/-!
The modules for `arrowCongr` and its lemmas below are related via the semilinearities
```
M₁ ←⎯⎯⎯σ₁₂⎯⎯⎯→ M₂ ←⎯⎯⎯σ₂₃⎯⎯⎯→ M₃
⏐ ⏐ ⏐
σ₁₁' σ₂₂' σ₃₃'
↓ ↓ ↓
M₁' ←⎯⎯σ₁'₂'⎯⎯→ M₂' ←⎯⎯σ₂'₃'⎯⎯→ M₃
⏐ ⏐
σ₁'₁'' σ₂'₂''
↓ ↓
M₁''←⎯σ₁''₂''⎯→ M₂''
```
where the horizontal direction corresponds to the `≃ₛₗ`s, and is needed for `arrowCongr_trans`,
while the vertical direction corresponds to the `→ₛₗ`s, and is needed `arrowCongr_comp`.

`Rᵢ` is not necessarily commutative, but `Rᵢ'` and `Rᵢ''` are.
-/
variable {R₁ R₂ R₃ R₁' R₂' R₃' R₁'' R₂'' : Type*} {M₁ M₂ M₃ M₁' M₂' M₃' M₁'' M₂'' : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]
variable [CommSemiring R₁'] [CommSemiring R₂'] [CommSemiring R₃']
variable [CommSemiring R₁''] [CommSemiring R₂'']
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid M₁'] [AddCommMonoid M₂'] [AddCommMonoid M₃']
variable [AddCommMonoid M₁''] [AddCommMonoid M₂'']
variable [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
variable [Module R₁' M₁'] [Module R₂' M₂'] [Module R₃' M₃']
variable [Module R₁'' M₁''] [Module R₂'' M₂'']
-- horizontal edges and closures
variable {σ₁₂ : R₁ ->+* R₂} {σ₂₁ : R₂ ->+* R₁}
variable {σ₂₃ : R₂ ->+* R₃} {σ₃₂ : R₃ ->+* R₂}
variable {σ₁₃ : R₁ ->+* R₃} {σ₃₁ : R₃ ->+* R₁}
variable {σ₁'₂' : R₁' ->+* R₂'} {σ₂'₁' : R₂' ->+* R₁'}
variable {σ₂'₃' : R₂' ->+* R₃'} {σ₃'₂' : R₃' ->+* R₂'}
variable {σ₁'₃' : R₁' ->+* R₃'} {σ₃'₁' : R₃' ->+* R₁'}
-- vertical edges and closures
variable {σ₁''₂'' : R₁'' ->+* R₂''} {σ₂''₁'' : R₂'' ->+* R₁''}
variable {σ₁₁' : R₁ ->+* R₁'} {σ₂₂' : R₂ ->+* R₂'} {σ₃₃' : R₃ ->+* R₃'}
variable {σ₁'₁'' : R₁' ->+* R₁''} {σ₂'₂'' : R₂' ->+* R₂''}
variable {σ₁₁'' : R₁ ->+* R₁''} {σ₂₂'' : R₂ ->+* R₂''}
-- diagonals
variable {σ₂₁' : R₂ ->+* R₁'} {σ₁₂' : R₁ ->+* R₂'}
variable {σ₃₂' : R₃ ->+* R₂'} {σ₂₃' : R₂ ->+* R₃'}
variable {σ₃₁' : R₃ ->+* R₁'} {σ₁₃' : R₁ ->+* R₃'}
variable {σ₂'₁'' : R₂' ->+* R₁''} {σ₁'₂'' : R₁' ->+* R₂''}
variable {σ₂₁'' : R₂ ->+* R₁''} {σ₁₂'' : R₁ ->+* R₂''}
variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₁'₂' σ₂'₁'] [RingHomInvPair σ₂'₁' σ₁'₂']
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₂'₃' σ₃'₂'] [RingHomInvPair σ₃'₂' σ₂'₃']
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
variable [RingHomInvPair σ₁'₃' σ₃'₁'] [RingHomInvPair σ₃'₁' σ₁'₃']
variable [RingHomInvPair σ₁''₂'' σ₂''₁''] [RingHomInvPair σ₂''₁'' σ₁''₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₁'' σ₁₁''] [RingHomCompTriple σ₂₂' σ₂'₂'' σ₂₂'']
variable [RingHomCompTriple σ₁₁' σ₁'₂' σ₁₂'] [RingHomCompTriple σ₂₁ σ₁₂' σ₂₂']
variable [RingHomCompTriple σ₂₂' σ₂'₁' σ₂₁'] [RingHomCompTriple σ₁₂ σ₂₁' σ₁₁']
variable [RingHomCompTriple σ₁₁' σ₁'₃' σ₁₃'] [RingHomCompTriple σ₃₁ σ₁₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₁' σ₃₁'] [RingHomCompTriple σ₁₃ σ₃₁' σ₁₁']
variable [RingHomCompTriple σ₂₂' σ₂'₃' σ₂₃'] [RingHomCompTriple σ₃₂ σ₂₃' σ₃₃']
variable [RingHomCompTriple σ₃₃' σ₃'₂' σ₃₂'] [RingHomCompTriple σ₂₃ σ₃₂' σ₂₂']
variable [RingHomCompTriple σ₁₁'' σ₁''₂'' σ₁₂''] [RingHomCompTriple σ₂₁ σ₁₂'' σ₂₂'']
variable [RingHomCompTriple σ₂₂'' σ₂''₁'' σ₂₁''] [RingHomCompTriple σ₁₂ σ₂₁'' σ₁₁'']
variable [RingHomCompTriple σ₁'₁'' σ₁''₂'' σ₁'₂''] [RingHomCompTriple σ₂'₁' σ₁'₂'' σ₂'₂'']
variable [RingHomCompTriple σ₂'₂'' σ₂''₁'' σ₂'₁''] [RingHomCompTriple σ₁'₂' σ₂'₁'' σ₁'₁'']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable [RingHomCompTriple σ₁'₂' σ₂'₃' σ₁'₃'] [RingHomCompTriple σ₃'₂' σ₂'₁' σ₃'₁']

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  body: arrowCongrAddEquiv e₁ e₂
  map_smul' c f := by ext; simp [arrowCongrAddEquiv, map_smulₛₗ]

@[simp]

中文:
定义 arrowCongr
  签名: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  定义体: arrowCongrAddEquiv e₁ e₂
  map_smul' c f := by ext; simp [arrowCongrAddEquiv, map_smulₛₗ]

@[simp]

Depends on / 依赖: arrowCongrAddEquiv
-/
def arrowCongr (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') :
    (M₁ ->ₛₗ[σ₁₁'] M₁') ≃ₛₗ[σ₁'₂'] (M₂ ->ₛₗ[σ₂₂'] M₂') where
  __ := arrowCongrAddEquiv e₁ e₂
  map_smul' c f := by ext; simp [arrowCongrAddEquiv, map_smulₛₗ]

@[simp]
/--
theorem `arrowCongr_apply` / 定理 `arrowCongr_apply`

English:
theorem arrowCongr_apply
  statement: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ ->ₛₗ[σ₁₁'] M₁')
  proof: rfl

@[simp]

中文:
定理 arrowCongr_apply
  结论: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ ->ₛₗ[σ₁₁'] M₁')
  证明: rfl

@[simp]
-/
theorem arrowCongr_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₁ ->ₛₗ[σ₁₁'] M₁')
    (x : M₂) : arrowCongr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/--
theorem `arrowCongr_symm_apply` / 定理 `arrowCongr_symm_apply`

English:
theorem arrowCongr_symm_apply
  statement: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₂ ->ₛₗ[σ₂₂'] M₂')
  proof: rfl

中文:
定理 arrowCongr_symm_apply
  结论: (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₂ ->ₛₗ[σ₂₂'] M₂')
  证明: rfl
-/
theorem arrowCongr_symm_apply (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : M₂ ->ₛₗ[σ₂₂'] M₂')
    (x : M₁) : (arrowCongr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

/--
theorem `arrowCongr_comp` / 定理 `arrowCongr_comp`

English:
theorem arrowCongr_comp
  proof: by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]

中文:
定理 arrowCongr_comp
  证明: by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, arrowCongr_apply, comp_apply, symm_apply_apply
-/
theorem arrowCongr_comp
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₃ : M₁'' ≃ₛₗ[σ₁''₂''] M₂'')
    (f : M₁ ->ₛₗ[σ₁₁'] M₁') (g : M₁' ->ₛₗ[σ₁'₁''] M₁'') :
    arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [symm_apply_apply, arrowCongr_apply, LinearMap.comp_apply]

/--
theorem `arrowCongr_trans` / 定理 `arrowCongr_trans`

English:
theorem arrowCongr_trans
  proof: rfl

中文:
定理 arrowCongr_trans
  证明: rfl
-/
theorem arrowCongr_trans
    (e₁ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₁' : M₁' ≃ₛₗ[σ₁'₂'] M₂')
    (e₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₂' : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    ((arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂' : (M₂ ->ₛₗ[σ₂₂'] M₂') ≃ₛₗ[σ₂'₃'] _)) =
      arrowCongr (e₁.trans e₂) (e₁'.trans e₂') :=
  rfl

-- TODO: upgrade to AlgEquiv (but this file currently cannot import AlgEquiv)
/--
Definition of `conj` / `conj` 的定义

English:
definition conj
  signature: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  body: arrowCongr e e

中文:
定义 conj
  签名: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  定义体: arrowCongr e e

Depends on / 依赖: arrowCongr
-/
def conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : Module.End R₁' M₁' ≃ₛₗ[σ₁'₂'] Module.End R₂' M₂' :=
  arrowCongr e e

/--
theorem `conj_apply` / 定理 `conj_apply`

English:
theorem conj_apply
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁')
  proof: rfl

中文:
定理 conj_apply
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : 模.End R₁' M₁')
  证明: rfl
-/
theorem conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.conj f = ((↑e : M₁' ->ₛₗ[σ₁'₂'] M₂').comp f).comp (e.symm : M₂' ->ₛₗ[σ₂'₁'] M₁') :=
  rfl

-- Note this has lower `simp` priority for performance reasons, so that we rewrite as
-- `e.conj LinearMap.id x => LinearMap.id x` => `x` rather than
-- `e.conj LinearMap.id x => e (LinearMap.id (e.symm x)) => e (e.symm x) => x`.
@[simp 900]
/--
theorem `conj_apply_apply` / 定理 `conj_apply_apply`

English:
theorem conj_apply_apply
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂')
  proof: rfl

中文:
定理 conj_apply_apply
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : 模.End R₁' M₁') (x : M₂')
  证明: rfl
-/
theorem conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') (x : M₂') :
    e.conj f x = e (f (e.symm x)) :=
  rfl

/--
theorem `symm_conj_apply` / 定理 `symm_conj_apply`

English:
theorem symm_conj_apply
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂')
  proof: rfl

中文:
定理 symm_conj_apply
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : 模.End R₂' M₂')
  证明: rfl
-/
theorem symm_conj_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.symm.conj f = ((↑e.symm : M₂' ->ₛₗ[σ₂'₁'] M₁').comp f).comp (e : M₁' ->ₛₗ[σ₁'₂'] M₂') :=
  rfl

/--
theorem `conj_comp` / 定理 `conj_comp`

English:
theorem conj_comp
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : Module.End R₁' M₁')
  proof: arrowCongr_comp e e e f g

中文:
定理 conj_comp
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : 模.End R₁' M₁')
  证明: arrowCongr_comp e e e f g

Depends on / 依赖: arrowCongr_comp
-/
theorem conj_comp (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f g : Module.End R₁' M₁') :
    e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
  arrowCongr_comp e e e f g

/--
theorem `conj_trans` / 定理 `conj_trans`

English:
theorem conj_trans
  given: (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃')
  proof: rfl

中文:
定理 conj_trans
  条件: (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃')
  证明: rfl
-/
theorem conj_trans (e₁ : M₁' ≃ₛₗ[σ₁'₂'] M₂') (e₂ : M₂' ≃ₛₗ[σ₂'₃'] M₃') :
    e₁.conj.trans e₂.conj = (e₁.trans e₂).conj :=
  rfl

/--
lemma `conj_conj_symm` / 引理 `conj_conj_symm`

English:
lemma conj_conj_symm
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂')
  proof: by ext; simp

中文:
引理 conj_conj_symm
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : 模.End R₂' M₂')
  证明: by ext; simp
-/
@[simp] lemma conj_conj_symm (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₂' M₂') :
    e.conj (e.symm.conj f) = f := by ext; simp

/--
lemma `conj_symm_conj` / 引理 `conj_symm_conj`

English:
lemma conj_symm_conj
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁')
  proof: by ext; simp

@[simp]

中文:
引理 conj_symm_conj
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : 模.End R₁' M₁')
  证明: by ext; simp

@[simp]
-/
@[simp] lemma conj_symm_conj (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') (f : Module.End R₁' M₁') :
    e.symm.conj (e.conj f) = f := by ext; simp

@[simp]
/--
theorem `conj_id` / 定理 `conj_id`

English:
theorem conj_id
  given: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  statement: e.conj LinearMap.id = LinearMap.id
  proof: by ext; simp

@[simp]

中文:
定理 conj_id
  条件: (e : M₁' ≃ₛₗ[σ₁'₂'] M₂')
  结论: e.conj 线性映射.id = 线性映射.id
  证明: by ext; simp

@[simp]
-/
theorem conj_id (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') : e.conj LinearMap.id = LinearMap.id := by ext; simp

@[simp]
/--
theorem `conj_refl` / 定理 `conj_refl`

English:
theorem conj_refl
  given: (f : Module.End R M)
  statement: (refl R M).conj f = f
  proof: rfl

中文:
定理 conj_refl
  条件: (f : 模.End R M)
  结论: (refl R M).conj f = f
  证明: rfl
-/
theorem conj_refl (f : Module.End R M) : (refl R M).conj f = f := rfl

end arrowCongr

/--
Definition of `congrRight` / `congrRight` 的定义

English:
definition congrRight
  signature: (f : M₂ ≃ₗ[R] M₃)
  body: arrowCongr (LinearEquiv.refl R M) f

中文:
定义 congrRight
  签名: (f : M₂ ≃ₗ[R] M₃)
  定义体: arrowCongr (LinearEquiv.refl R M) f

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, arrowCongr
-/
def congrRight (f : M₂ ≃ₗ[R] M₃) : (M ->ₗ[R] M₂) ≃ₗ[R] M ->ₗ[R] M₃ :=
  arrowCongr (LinearEquiv.refl R M) f

variable (M) in
/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
  body: e.arrowCongrAddEquiv (.refl ..)
  map_smul' _ _ := rfl

中文:
定义 congrLeft
  签名: {R} (S) [半环 R] [半环 S] [模 R M₂] [模 R M₃] [模 R M]
  定义体: e.arrowCongrAddEquiv (.refl ..)
  map_smul' _ _ := rfl
-/
@[simps] def congrLeft {R} (S) [Semiring R] [Semiring S] [Module R M₂] [Module R M₃] [Module R M]
    [Module S M] [SMulCommClass R S M] (e : M₂ ≃ₗ[R] M₃) : (M₂ ->ₗ[R] M) ≃ₗ[S] (M₃ ->ₗ[R] M) where
  __ := e.arrowCongrAddEquiv (.refl ..)
  map_smul' _ _ := rfl

end CommSemiring

section Field

variable [Field K] [AddCommGroup M] [Module K M]
variable (K) (M)

open LinearMap

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps!]
/--
Definition of `smulOfNeZero` / `smulOfNeZero` 的定义

English:
definition smulOfNeZero
  signature: (a : K) (ha : a != 0)
  body: smulOfUnit Units.mk0 a ha

中文:
定义 smulOfNeZero
  签名: (a : K) (ha : a != 0)
  定义体: smulOfUnit Units.mk0 a ha

Depends on / 依赖: Units.mk0, smulOfUnit
-/
def smulOfNeZero (a : K) (ha : a != 0) : M ≃ₗ[K] M :=
smulOfUnit Units.mk0 a ha

end Field

end LinearEquiv

namespace Equiv

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (e : M ≃ M₂) (h : IsLinearMap R (e : M -> M₂))
  body: { e, h.mk' e with }

中文:
定义 toLinearEquiv
  签名: (e : M ≃ M₂) (h : 是线性映射 R (e : M -> M₂))
  定义体: { e, h.mk' e with }

Depends on / 依赖: h.mk
-/
def toLinearEquiv (e : M ≃ M₂) (h : IsLinearMap R (e : M -> M₂)) : M ≃ₗ[R] M₂ :=
  { e, h.mk' e with }

end Equiv

section FunLeft

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable {m n p : Type*}

namespace LinearMap

/--
Definition of `funLeft` / `funLeft` 的定义

English:
definition funLeft
  signature: (f : m -> n)
  body: (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 funLeft
  签名: (f : m -> n)
  定义体: (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
-/
def funLeft (f : m -> n) : (n -> M) ->ₗ[R] m -> M where
  toFun := (· ∘ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `funLeft_apply` / 定理 `funLeft_apply`

English:
theorem funLeft_apply
  given: (f : m -> n) (g : n -> M) (i : m)
  statement: funLeft R M f g i = g (f i)
  proof: rfl

@[simp]

中文:
定理 funLeft_apply
  条件: (f : m -> n) (g : n -> M) (i : m)
  结论: funLeft R M f g i = g (f i)
  证明: rfl

@[simp]
-/
theorem funLeft_apply (f : m -> n) (g : n -> M) (i : m) : funLeft R M f g i = g (f i) :=
  rfl

@[simp]
/--
theorem `funLeft_id` / 定理 `funLeft_id`

English:
theorem funLeft_id
  given: (g : n -> M)
  statement: funLeft R M _root_.id g = g
  proof: rfl

中文:
定理 funLeft_id
  条件: (g : n -> M)
  结论: funLeft R M _root_.id g = g
  证明: rfl
-/
theorem funLeft_id (g : n -> M) : funLeft R M _root_.id g = g :=
  rfl

/--
theorem `funLeft_comp` / 定理 `funLeft_comp`

English:
theorem funLeft_comp
  given: (f₁ : n -> p) (f₂ : m -> n)
  proof: rfl

中文:
定理 funLeft_comp
  条件: (f₁ : n -> p) (f₂ : m -> n)
  证明: rfl
-/
theorem funLeft_comp (f₁ : n -> p) (f₂ : m -> n) :
    funLeft R M (f₁ ∘ f₂) = (funLeft R M f₂).comp (funLeft R M f₁) :=
  rfl

/--
theorem `funLeft_surjective_of_injective` / 定理 `funLeft_surjective_of_injective`

English:
theorem funLeft_surjective_of_injective
  given: (f : m -> n) (hf : Injective f)
  proof: hf.surjective_comp_right

中文:
定理 funLeft_surjective_of_injective
  条件: (f : m -> n) (hf : 单射 f)
  证明: hf.surjective_comp_right

Depends on / 依赖: hf.surjective_comp_right, surjective_comp_right
-/
theorem funLeft_surjective_of_injective (f : m -> n) (hf : Injective f) :
    Surjective (funLeft R M f) :=
  hf.surjective_comp_right

/--
theorem `funLeft_injective_of_surjective` / 定理 `funLeft_injective_of_surjective`

English:
theorem funLeft_injective_of_surjective
  given: (f : m -> n) (hf : Surjective f)
  proof: hf.injective_comp_right

中文:
定理 funLeft_injective_of_surjective
  条件: (f : m -> n) (hf : 满射 f)
  证明: hf.injective_comp_right

Depends on / 依赖: hf.injective_comp_right, injective_comp_right
-/
theorem funLeft_injective_of_surjective (f : m -> n) (hf : Surjective f) :
    Injective (funLeft R M f) :=
  hf.injective_comp_right

end LinearMap

namespace LinearEquiv

open LinearMap

/--
Definition of `funCongrLeft` / `funCongrLeft` 的定义

English:
definition funCongrLeft
  signature: (e : m ≃ n)
  body: LinearEquiv.ofLinearMap (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, Linear

中文:
定义 funCongrLeft
  签名: (e : m ≃ n)
  定义体: LinearEquiv.ofLinearMap (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, Linear

Depends on / 依赖: Equiv.self_comp_symm, Equiv.symm_comp_self, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.ext, LinearMap.funLeft_id, e.symm, funLeft, funLeft_comp, funLeft_id, id_apply, ofLinearMap, self_comp_symm, symm_comp_self
-/
def funCongrLeft (e : m ≃ n) : (n -> M) ≃ₗ[R] m -> M :=
  LinearEquiv.ofLinearMap (funLeft R M e) (funLeft R M e.symm)
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.symm_comp_self, LinearMap.funLeft_id])
    (LinearMap.ext fun x =>
      funext fun i => by rw [id_apply, ← funLeft_comp, Equiv.self_comp_symm, LinearMap.funLeft_id])

@[simp]
/--
theorem `funCongrLeft_apply` / 定理 `funCongrLeft_apply`

English:
theorem funCongrLeft_apply
  given: (e : m ≃ n) (x : n -> M)
  statement: funCongrLeft R M e x = funLeft R M e x
  proof: rfl

@[simp]

中文:
定理 funCongrLeft_apply
  条件: (e : m ≃ n) (x : n -> M)
  结论: funCongrLeft R M e x = funLeft R M e x
  证明: rfl

@[simp]
-/
theorem funCongrLeft_apply (e : m ≃ n) (x : n -> M) : funCongrLeft R M e x = funLeft R M e x :=
  rfl

@[simp]
/--
theorem `funCongrLeft_id` / 定理 `funCongrLeft_id`

English:
theorem funCongrLeft_id
  statement: funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n -> M)
  proof: rfl

@[simp]

中文:
定理 funCongrLeft_id
  结论: funCongrLeft R M (等价.refl n) = 线性等价.refl R (n -> M)
  证明: rfl

@[simp]
-/
theorem funCongrLeft_id : funCongrLeft R M (Equiv.refl n) = LinearEquiv.refl R (n -> M) :=
  rfl

@[simp]
/--
theorem `funCongrLeft_comp` / 定理 `funCongrLeft_comp`

English:
theorem funCongrLeft_comp
  given: (e₁ : m ≃ n) (e₂ : n ≃ p)
  proof: rfl

@[simp]

中文:
定理 funCongrLeft_comp
  条件: (e₁ : m ≃ n) (e₂ : n ≃ p)
  证明: rfl

@[simp]
-/
theorem funCongrLeft_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
    funCongrLeft R M (Equiv.trans e₁ e₂) =
      LinearEquiv.trans (funCongrLeft R M e₂) (funCongrLeft R M e₁) :=
  rfl

@[simp]
/--
theorem `funCongrLeft_symm` / 定理 `funCongrLeft_symm`

English:
theorem funCongrLeft_symm
  given: (e : m ≃ n)
  statement: (funCongrLeft R M e).symm = funCongrLeft R M e.symm
  proof: rfl

中文:
定理 funCongrLeft_symm
  条件: (e : m ≃ n)
  结论: (funCongrLeft R M e).symm = funCongrLeft R M e.symm
  证明: rfl
-/
theorem funCongrLeft_symm (e : m ≃ n) : (funCongrLeft R M e).symm = funCongrLeft R M e.symm :=
  rfl

end LinearEquiv

end FunLeft

section Pi

namespace LinearEquiv

/-- The product over `S ⊕ T` of a family of modules is isomorphic to the product of
(the product over `S`) and (the product over `T`).

This is `Equiv.sumPiEquivProdPi` as a `LinearEquiv`.
-/
@[simps -fullyApplied +simpRhs]
/--
Definition of `sumPiEquivProdPi` / `sumPiEquivProdPi` 的定义

English:
definition sumPiEquivProdPi
  signature: (R : Type*) [Semiring R] (S T : Type*) (A : S oplus T -> Type*)
  body: Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 sumPiEquivProdPi
  签名: (R : 类型) [半环 R] (S T : 类型) (A : S oplus T -> 类型)
  定义体: Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Equiv.sumPiEquivProdPi, sumPiEquivProdPi
-/
def sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*) (A : S oplus T -> Type*)
    [forall st, AddCommMonoid (A st)] [forall st, Module R (A st)] :
    (Π (st : S oplus T), A st) ≃ₗ[R] (Π (s : S), A (.inl s)) × (Π (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The product `Π t : α, f t` of a family of modules is linearly isomorphic to the module
`f ⬝` when `α` only contains `⬝`.

This is `Equiv.piUnique` as a `LinearEquiv`.
-/
@[simps -fullyApplied]
/--
Definition of `piUnique` / `piUnique` 的定义

English:
definition piUnique
  signature: {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*)
  body: Equiv.piUnique _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 piUnique
  签名: {α : 类型} [唯一 α] (R : 类型) [半环 R] (f : α -> 类型)
  定义体: Equiv.piUnique _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Equiv.piUnique, piUnique
-/
def piUnique {α : Type*} [Unique α] (R : Type*) [Semiring R] (f : α -> Type*)
    [forall x, AddCommMonoid (f x)] [forall x, Module R (f x)] : (Π t : α, f t) ≃ₗ[R] f default where
  __ := Equiv.piUnique _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LinearEquiv

end Pi

namespace Units
variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

variable (R A) in
/--
Definition of `mulLeftLinearEquiv` / `mulLeftLinearEquiv` 的定义

English:
definition mulLeftLinearEquiv
  signature: : Aˣ ->* A ≃ₗ[R] A where
  body: { __ := mulLeft a
      __ := LinearMap.mulLeft R (a : A) }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

中文:
定义 mulLeftLinearEquiv
  签名: : Aˣ ->* A ≃ₗ[R] A where
  定义体: { __ := mulLeft a
      __ := LinearMap.mulLeft R (a : A) }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

Depends on / 依赖: LinearMap, LinearMap.mulLeft, map_mul, map_one, mulLeft, mul_assoc
-/
def mulLeftLinearEquiv : Aˣ ->* A ≃ₗ[R] A where
  toFun a :=
    { __ := mulLeft a
      __ := LinearMap.mulLeft R (a : A) }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

variable (R) in
/--
lemma `mulLeftLinearEquiv_apply` / 引理 `mulLeftLinearEquiv_apply`

English:
lemma mulLeftLinearEquiv_apply
  given: (a : Aˣ) (x : A)
  proof: rfl

中文:
引理 mulLeftLinearEquiv_apply
  条件: (a : Aˣ) (x : A)
  证明: rfl
-/
@[simp] lemma mulLeftLinearEquiv_apply (a : Aˣ) (x : A) :
    a.mulLeftLinearEquiv R A x = a * x := rfl

variable (R) in
/--
lemma `symm_mulLeftLinearEquiv_apply` / 引理 `symm_mulLeftLinearEquiv_apply`

English:
lemma symm_mulLeftLinearEquiv_apply
  given: (a : Aˣ) (x : A)
  proof: rfl

中文:
引理 symm_mulLeftLinearEquiv_apply
  条件: (a : Aˣ) (x : A)
  证明: rfl
-/
lemma symm_mulLeftLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulLeftLinearEquiv R A).symm x = a⁻¹ * x := rfl

/--
lemma `symm_mulLeftLinearEquiv` / 引理 `symm_mulLeftLinearEquiv`

English:
lemma symm_mulLeftLinearEquiv
  given: (a : Aˣ)
  proof: rfl

中文:
引理 symm_mulLeftLinearEquiv
  条件: (a : Aˣ)
  证明: rfl
-/
@[simp] lemma symm_mulLeftLinearEquiv (a : Aˣ) :
    (a.mulLeftLinearEquiv R A).symm = a⁻¹.mulLeftLinearEquiv R A := rfl

/--
lemma `mulLeftLinearEquiv_trans_mulLeftLinearEquiv` / 引理 `mulLeftLinearEquiv_trans_mulLeftLinearEquiv`

English:
lemma mulLeftLinearEquiv_trans_mulLeftLinearEquiv
  given: (a b : Aˣ)
  proof: map_mul _ _ _

中文:
引理 mulLeftLinearEquiv_trans_mulLeftLinearEquiv
  条件: (a b : Aˣ)
  证明: map_mul _ _ _

Depends on / 依赖: map_mul
-/
lemma mulLeftLinearEquiv_trans_mulLeftLinearEquiv (a b : Aˣ) :
    (a.mulLeftLinearEquiv R A).trans (b.mulLeftLinearEquiv R A) =
.symm (b * a).mulLeftLinearEquiv R A := map_mul _ _ _

/--
lemma `mulLeftLinearEquiv_mul_apply` / 引理 `mulLeftLinearEquiv_mul_apply`

English:
lemma mulLeftLinearEquiv_mul_apply
  given: (u v : Aˣ) (x : A)
  proof: by simp

中文:
引理 mulLeftLinearEquiv_mul_apply
  条件: (u v : Aˣ) (x : A)
  证明: by simp
-/
lemma mulLeftLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    mulLeftLinearEquiv R A (u * v) x =
      mulLeftLinearEquiv R A u (mulLeftLinearEquiv R A v x) := by simp

/--
lemma `toLinearMap_mulLeftLinearEquiv` / 引理 `toLinearMap_mulLeftLinearEquiv`

English:
lemma toLinearMap_mulLeftLinearEquiv
  given: (u : Aˣ)
  proof: rfl

中文:
引理 toLinearMap_mulLeftLinearEquiv
  条件: (u : Aˣ)
  证明: rfl
-/
@[simp] lemma toLinearMap_mulLeftLinearEquiv (u : Aˣ) :
    (mulLeftLinearEquiv R A u).toLinearMap = LinearMap.mulLeft R (u : A) := rfl

/--
lemma `toEquiv_mulLeftLinearEquiv` / 引理 `toEquiv_mulLeftLinearEquiv`

English:
lemma toEquiv_mulLeftLinearEquiv
  given: (u : Aˣ)
  proof: rfl

中文:
引理 toEquiv_mulLeftLinearEquiv
  条件: (u : Aˣ)
  证明: rfl
-/
@[simp] lemma toEquiv_mulLeftLinearEquiv (u : Aˣ) :
    (mulLeftLinearEquiv R A u).toEquiv = u.mulLeft := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/--
Definition of `mulRightLinearEquiv` / `mulRightLinearEquiv` 的定义

English:
definition mulRightLinearEquiv
  signature: (a : Aˣ)
  body: mulRight a
  __ := LinearMap.mulRight R (a : A)

中文:
定义 mulRightLinearEquiv
  签名: (a : Aˣ)
  定义体: mulRight a
  __ := LinearMap.mulRight R (a : A)

Depends on / 依赖: mulRight
-/
def mulRightLinearEquiv (a : Aˣ) : A ≃ₗ[R] A where
  __ := mulRight a
  __ := LinearMap.mulRight R (a : A)

variable (R) in
/--
lemma `mulRightLinearEquiv_apply` / 引理 `mulRightLinearEquiv_apply`

English:
lemma mulRightLinearEquiv_apply
  given: (a : Aˣ) (x : A)
  proof: rfl

中文:
引理 mulRightLinearEquiv_apply
  条件: (a : Aˣ) (x : A)
  证明: rfl
-/
@[simp] lemma mulRightLinearEquiv_apply (a : Aˣ) (x : A) :
    a.mulRightLinearEquiv R x = x * a := rfl

variable (R) in
/--
lemma `symm_mulRightLinearEquiv_apply` / 引理 `symm_mulRightLinearEquiv_apply`

English:
lemma symm_mulRightLinearEquiv_apply
  given: (a : Aˣ) (x : A)
  proof: rfl

中文:
引理 symm_mulRightLinearEquiv_apply
  条件: (a : Aˣ) (x : A)
  证明: rfl
-/
lemma symm_mulRightLinearEquiv_apply (a : Aˣ) (x : A) :
    (a.mulRightLinearEquiv R).symm x = x * a⁻¹ := rfl

/--
lemma `symm_mulRightLinearEquiv` / 引理 `symm_mulRightLinearEquiv`

English:
lemma symm_mulRightLinearEquiv
  given: (a : Aˣ)
  proof: rfl

中文:
引理 symm_mulRightLinearEquiv
  条件: (a : Aˣ)
  证明: rfl
-/
@[simp] lemma symm_mulRightLinearEquiv (a : Aˣ) :
    (a.mulRightLinearEquiv R).symm = a⁻¹.mulRightLinearEquiv R := rfl

/--
lemma `mulRightLinearEquiv_trans_mulRightLinearEquiv` / 引理 `mulRightLinearEquiv_trans_mulRightLinearEquiv`

English:
lemma mulRightLinearEquiv_trans_mulRightLinearEquiv
  given: (a b : Aˣ)
  proof: by ext; simp [mul_assoc]

中文:
引理 mulRightLinearEquiv_trans_mulRightLinearEquiv
  条件: (a b : Aˣ)
  证明: by ext; simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulRightLinearEquiv_trans_mulRightLinearEquiv (a b : Aˣ) :
    (a.mulRightLinearEquiv R).trans (b.mulRightLinearEquiv R) =
      (a * b).mulRightLinearEquiv R := by ext; simp [mul_assoc]

/--
lemma `mulRightLinearEquiv_mul_apply` / 引理 `mulRightLinearEquiv_mul_apply`

English:
lemma mulRightLinearEquiv_mul_apply
  given: (u v : Aˣ) (x : A)
  proof: by simp [mul_assoc]

中文:
引理 mulRightLinearEquiv_mul_apply
  条件: (u v : Aˣ) (x : A)
  证明: by simp [mul_assoc]

Depends on / 依赖: mul_assoc
-/
lemma mulRightLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    mulRightLinearEquiv R (u * v) x =
      mulRightLinearEquiv R v (mulRightLinearEquiv R u x) := by simp [mul_assoc]

/--
lemma `toLinearMap_mulRightLinearEquiv` / 引理 `toLinearMap_mulRightLinearEquiv`

English:
lemma toLinearMap_mulRightLinearEquiv
  given: (u : Aˣ)
  proof: rfl

中文:
引理 toLinearMap_mulRightLinearEquiv
  条件: (u : Aˣ)
  证明: rfl
-/
@[simp] lemma toLinearMap_mulRightLinearEquiv (u : Aˣ) :
    (mulRightLinearEquiv R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl

/--
lemma `toEquiv_mulRightLinearEquiv` / 引理 `toEquiv_mulRightLinearEquiv`

English:
lemma toEquiv_mulRightLinearEquiv
  given: (u : Aˣ)
  proof: rfl

中文:
引理 toEquiv_mulRightLinearEquiv
  条件: (u : Aˣ)
  证明: rfl
-/
@[simp] lemma toEquiv_mulRightLinearEquiv (u : Aˣ) :
    (mulRightLinearEquiv R u).toEquiv = u.mulRight := rfl

end mulRight
end Units

end AddCommMonoid
