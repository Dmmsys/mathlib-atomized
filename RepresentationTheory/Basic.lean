/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * `Representation`
  * `Representation.directSum`
  * `Representation.prod`
  * `Representation.tprod`
  * `Representation.linHom`
  * `Representation.dual`
  * `Representation.free`

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`. We use the abbreviation `Representation` for this hom space.

The theorem `asAlgebraHom_def` constructs a module over the group `k`-algebra of `G` (implemented
as `k[G]`) corresponding to a representation. If `ρ : Representation k G V`, this
module can be accessed via `ρ.asModule`. Conversely, given a `k[G]`-module `M`,
`M.ofModule` is the associated representation seen as a homomorphism.
-/

@[expose] public section

open MonoidAlgebra
open LinearMap Module

section

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/--
Definition of `Representation` / `Representation` 的定义

English:
abbreviation Representation
  body: G ->* V ->ₗ[k] V

中文:
缩写 Representation
  定义体: G ->* V ->ₗ[k] V
-/
abbrev Representation :=
  G ->* V ->ₗ[k] V

end

namespace Representation

section trivial

variable (k G V : Type*) [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Representation k G V
  body: 1

中文:
定义 trivial
  签名: : Representation k G V
  定义体: 1
-/
def trivial : Representation k G V :=
  1

variable {G V}

@[simp]
/--
theorem `trivial_apply` / 定理 `trivial_apply`

English:
theorem trivial_apply
  given: (g : G) (v : V)
  statement: trivial k G V g v = v
  proof: rfl

中文:
定理 trivial_apply
  条件: (g : G) (v : V)
  结论: trivial k G V g v = v
  证明: rfl
-/
theorem trivial_apply (g : G) (v : V) : trivial k G V g v = v :=
  rfl

variable {k}

/--
Definition of `IsTrivial` / `IsTrivial` 的定义

English:
class IsTrivial
  parameters: (ρ : Representation k G V)
  axioms and operations (1):
    - out : forall g, ρ g = LinearMap.id  [default: by aesop]

中文:
类 IsTrivial
  参数: (ρ : Representation k G V)
  公理与运算 (1 个):
    - out : 对任意 g, ρ g = LinearMap.id  [默认: by aesop]
-/
class IsTrivial (ρ : Representation k G V) : Prop where
  out : forall g, ρ g = LinearMap.id := by aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTrivial (trivial k G V)

中文:
实例 :
  签名: IsTrivial (trivial k G V)
-/
instance : IsTrivial (trivial k G V) where

@[simp]
/--
theorem `isTrivial_def` / 定理 `isTrivial_def`

English:
theorem isTrivial_def
  given: (ρ : Representation k G V) [IsTrivial ρ] (g : G)
  proof: IsTrivial.out g

中文:
定理 isTrivial_def
  条件: (ρ : Representation k G V) [IsTrivial ρ] (g : G)
  证明: IsTrivial.out g

Depends on / 依赖: IsTrivial, IsTrivial.out
-/
theorem isTrivial_def (ρ : Representation k G V) [IsTrivial ρ] (g : G) :
    ρ g = LinearMap.id := IsTrivial.out g

/--
theorem `isTrivial_apply` / 定理 `isTrivial_apply`

English:
theorem isTrivial_apply
  given: (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V)
  proof: congr($(isTrivial_def ρ g) x)

中文:
定理 isTrivial_apply
  条件: (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V)
  证明: congr($(isTrivial_def ρ g) x)

Depends on / 依赖: isTrivial_def
-/
theorem isTrivial_apply (ρ : Representation k G V) [IsTrivial ρ] (g : G) (x : V) :
    ρ g x = x := congr($(isTrivial_def ρ g) x)

end trivial

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

@[simp]
/--
theorem `inv_self_apply` / 定理 `inv_self_apply`

English:
theorem inv_self_apply
  given: (g : G) (x : V)
  proof: by
  simp [← Module.End.mul_apply, ← map_mul]

@[simp]

中文:
定理 inv_self_apply
  条件: (g : G) (x : V)
  证明: by
  simp [← Module.End.mul_apply, ← map_mul]

@[simp]

Depends on / 依赖: Module, Module.End.mul_apply, map_mul, mul_apply
-/
theorem inv_self_apply (g : G) (x : V) :
    ρ g⁻¹ (ρ g x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]

@[simp]
/--
theorem `self_inv_apply` / 定理 `self_inv_apply`

English:
theorem self_inv_apply
  given: (g : G) (x : V)
  proof: by
  simp [← Module.End.mul_apply, ← map_mul]

中文:
定理 self_inv_apply
  条件: (g : G) (x : V)
  证明: by
  simp [← Module.End.mul_apply, ← map_mul]

Depends on / 依赖: Module, Module.End.mul_apply, map_mul, mul_apply
-/
theorem self_inv_apply (g : G) (x : V) :
    ρ g (ρ g⁻¹ x) = x := by
  simp [← Module.End.mul_apply, ← map_mul]

/--
lemma `inv_apply_eq_iff` / 引理 `inv_apply_eq_iff`

English:
lemma inv_apply_eq_iff
  given: {g : G} {x y : V}
  proof: by
  constructor <;> rintro rfl <;> simp

中文:
引理 inv_apply_eq_iff
  条件: {g : G} {x y : V}
  证明: by
  constructor <;> rintro rfl <;> simp
-/
lemma inv_apply_eq_iff {g : G} {x y : V} :
    ρ g⁻¹ x = y ↔ x = ρ g y := by
  constructor <;> rintro rfl <;> simp

/--
lemma `apply_bijective` / 引理 `apply_bijective`

English:
lemma apply_bijective
  given: (g : G)
  proof: Equiv.bijective ⟨ρ g, ρ g⁻¹, inv_self_apply ρ g, self_inv_apply ρ g⟩

中文:
引理 apply_bijective
  条件: (g : G)
  证明: Equiv.bijective ⟨ρ g, ρ g⁻¹, inv_self_apply ρ g, self_inv_apply ρ g⟩

Depends on / 依赖: Equiv.bijective, bijective, inv_self_apply, self_inv_apply
-/
lemma apply_bijective (g : G) :
    Function.Bijective (ρ g) :=
  Equiv.bijective ⟨ρ g, ρ g⁻¹, inv_self_apply ρ g, self_inv_apply ρ g⟩

end Group

section MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/--
Definition of `asAlgebraHom` / `asAlgebraHom` 的定义

English:
definition asAlgebraHom
  signature: : k[G] ->ₐ[k] Module.End k V
  body: lift k _ G ρ

中文:
定义 asAlgebraHom
  签名: : k[G] ->ₐ[k] Module.End k V
  定义体: lift k _ G ρ
-/
noncomputable def asAlgebraHom : k[G] ->ₐ[k] Module.End k V := lift k _ G ρ

/--
theorem `asAlgebraHom_def` / 定理 `asAlgebraHom_def`

English:
theorem asAlgebraHom_def
  statement: asAlgebraHom ρ = lift k _ G ρ
  proof: rfl

@[simp]

中文:
定理 asAlgebraHom_def
  结论: asAlgebraHom ρ = lift k _ G ρ
  证明: rfl

@[simp]
-/
theorem asAlgebraHom_def : asAlgebraHom ρ = lift k _ G ρ := rfl

@[simp]
/--
theorem `asAlgebraHom_single` / 定理 `asAlgebraHom_single`

English:
theorem asAlgebraHom_single
  given: (g : G) (r : k)
  proof: by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

中文:
定理 asAlgebraHom_single
  条件: (g : G) (r : k)
  证明: by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.lift_single, asAlgebraHom_def, lift_single
-/
theorem asAlgebraHom_single (g : G) (r : k) :
    asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

/--
theorem `asAlgebraHom_single_one` / 定理 `asAlgebraHom_single_one`

English:
theorem asAlgebraHom_single_one
  given: (g : G)
  statement: asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g
  proof: by simp

中文:
定理 asAlgebraHom_single_one
  条件: (g : G)
  结论: asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g
  证明: by simp
-/
theorem asAlgebraHom_single_one (g : G) : asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g := by simp

/--
theorem `asAlgebraHom_of` / 定理 `asAlgebraHom_of`

English:
theorem asAlgebraHom_of
  given: (g : G)
  statement: asAlgebraHom ρ (of k G g) = ρ g
  proof: by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

中文:
定理 asAlgebraHom_of
  条件: (g : G)
  结论: asAlgebraHom ρ (of k G g) = ρ g
  证明: by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.of_apply, asAlgebraHom_single, of_apply, one_smul
-/
theorem asAlgebraHom_of (g : G) : asAlgebraHom ρ (of k G g) = ρ g := by
  simp only [MonoidAlgebra.of_apply, asAlgebraHom_single, one_smul]

section

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
/-- If `ρ : Representation k G V`, then `ρ.asModule` is a type synonym for `V`,
which we equip with an instance `Module k[G] ρ.asModule`.

You should use `asModuleEquiv : ρ.asModule ≃+ V` to translate terms.
-/
@[nolint unusedArguments]
/--
Definition of `asModule` / `asModule` 的定义

English:
definition asModule
  signature: (_ : Representation k G V)
  body: V
deriving AddCommMonoid, Module k

中文:
定义 asModule
  签名: (_ : Representation k G V)
  定义体: V
deriving AddCommMonoid, Module k
-/
def asModule (_ : Representation k G V) := V
deriving AddCommMonoid, Module k

instance (ρ : Representation k G V) : Inhabited ρ.asModule where
  default := 0

/--
Definition of `asModuleEquiv` / `asModuleEquiv` 的定义

English:
definition asModuleEquiv
  signature: (ρ : Representation k G V)
  body: LinearEquiv.refl _ _

中文:
定义 asModuleEquiv
  签名: (ρ : Representation k G V)
  定义体: LinearEquiv.refl _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def asModuleEquiv (ρ : Representation k G V) : ρ.asModule ≃ₗ[k] V :=
  LinearEquiv.refl _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: k V] (ρ
  body: .equiv ρ.asModuleEquiv.symm

中文:
实例 [Module.Finite
  签名: k V] (ρ
  定义体: .equiv ρ.asModuleEquiv.symm

Depends on / 依赖: asModuleEquiv, asModuleEquiv.symm
-/
instance [Module.Finite k V] (ρ : Representation k G V) : Module.Finite k ρ.asModule :=
  .equiv ρ.asModuleEquiv.symm

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module k[G] ρ.asModule
  body: Module.compHom V (asAlgebraHom ρ).toRingHom

@[simp]

中文:
实例 :
  签名: Module k[G] ρ.asModule
  定义体: Module.compHom V (asAlgebraHom ρ).toRingHom

@[simp]

Depends on / 依赖: Module, Module.compHom, asAlgebraHom, compHom, toRingHom
-/
noncomputable instance : Module k[G] ρ.asModule :=
  Module.compHom V (asAlgebraHom ρ).toRingHom

@[simp]
/--
theorem `asModuleEquiv_map_smul` / 定理 `asModuleEquiv_map_smul`

English:
theorem asModuleEquiv_map_smul
  given: (r : k[G]) (x : ρ.asModule)
  proof: rfl

中文:
定理 asModuleEquiv_map_smul
  条件: (r : k[G]) (x : ρ.asModule)
  证明: rfl
-/
theorem asModuleEquiv_map_smul (r : k[G]) (x : ρ.asModule) :
    ρ.asModuleEquiv (r • x) = ρ.asAlgebraHom r (ρ.asModuleEquiv x) :=
  rfl

/--
theorem `asModuleEquiv_symm_map_smul` / 定理 `asModuleEquiv_symm_map_smul`

English:
theorem asModuleEquiv_symm_map_smul
  given: (r : k) (x : V)
  proof: by
  rw [LinearEquiv.symm_apply_eq]
  simp

@[simp]

中文:
定理 asModuleEquiv_symm_map_smul
  条件: (r : k) (x : V)
  证明: by
  rw [LinearEquiv.symm_apply_eq]
  simp

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem asModuleEquiv_symm_map_smul (r : k) (x : V) :
    ρ.asModuleEquiv.symm (r • x) = algebraMap k k[G] r • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

@[simp]
/--
theorem `asModuleEquiv_symm_map_rho` / 定理 `asModuleEquiv_symm_map_rho`

English:
theorem asModuleEquiv_symm_map_rho
  given: (g : G) (x : V)
  proof: by
  rw [LinearEquiv.symm_apply_eq]
  simp

中文:
定理 asModuleEquiv_symm_map_rho
  条件: (g : G) (x : V)
  证明: by
  rw [LinearEquiv.symm_apply_eq]
  simp

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem asModuleEquiv_symm_map_rho (g : G) (x : V) :
    ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm x := by
  rw [LinearEquiv.symm_apply_eq]
  simp

/--
Definition of `ofModule'` / `ofModule'` 的定义

English:
definition ofModule'
  signature: (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M]
  body: (MonoidAlgebra.lift k (M ->ₗ[k] M) G).symm (Algebra.lsmul k k M)

中文:
定义 ofModule'
  签名: (M : 类型) [AddCommMonoid M] [Module k M] [Module k[G] M]
  定义体: (MonoidAlgebra.lift k (M ->ₗ[k] M) G).symm (Algebra.lsmul k k M)

Depends on / 依赖: Algebra, Algebra.lsmul, MonoidAlgebra, MonoidAlgebra.lift
-/
noncomputable def ofModule' (M : Type*) [AddCommMonoid M] [Module k M] [Module k[G] M]
    [IsScalarTower k k[G] M] : Representation k G M :=
  (MonoidAlgebra.lift k (M ->ₗ[k] M) G).symm (Algebra.lsmul k k M)

section

variable (M : Type*) [AddCommMonoid M] [Module k[G] M]

/--
Definition of `ofModule` / `ofModule` 的定义

English:
definition ofModule
  signature: : Representation k G (RestrictScalars k k[G] M)
  body: (MonoidAlgebra.lift k _ G).symm (RestrictScalars.lsmul k k[G] M)

中文:
定义 ofModule
  签名: : Representation k G (RestrictScalars k k[G] M)
  定义体: (MonoidAlgebra.lift k _ G).symm (RestrictScalars.lsmul k k[G] M)

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.lift, RestrictScalars, RestrictScalars.lsmul
-/
noncomputable def ofModule : Representation k G (RestrictScalars k k[G] M) :=
  (MonoidAlgebra.lift k _ G).symm (RestrictScalars.lsmul k k[G] M)

/-!
## `ofModule` and `asModule` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

See `Rep.equivalenceModuleMonoidAlgebra` for the full statement.

Starting with `ρ : Representation k G V`, converting to a module and back again
we have a `Representation k G (restrictScalars k k[G] ρ.asModule)`.
To compare these, we use the composition of `restrictScalarsAddEquiv` and `ρ.asModuleEquiv`.

Similarly, starting with `Module k[G] M`,
after we convert to a representation and back to a module,
we have `Module k[G] (restrictScalars k k[G] M)`.
-/


set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofModule_asAlgebraHom_apply_apply` / 定理 `ofModule_asAlgebraHom_apply_apply`

English:
theorem ofModule_asAlgebraHom_apply_apply
  statement: (r : k[G])
  proof: by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul

中文:
定理 ofModule_asAlgebraHom_apply_apply
  结论: (r : k[G])
  证明: by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.smul_apply, MonoidAlgebra, MonoidAlgebra.induction_on, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply, Representation, Representation.asAlgebraHom_single, Representation.ofModule, RestrictScalars, RestrictScalars.addEquiv_symm_map_smul_smul, RestrictScalars.lsmul_apply_apply, addEquiv_symm_map_smul_smul, add_apply, add_smul, asAlgebraHom_single, induction_on, lift_symm_apply, lsmul_apply_apply
-/
theorem ofModule_asAlgebraHom_apply_apply (r : k[G])
    (m : RestrictScalars k k[G] M) :
    ((ofModule M).asAlgebraHom r) m =
      (RestrictScalars.addEquiv _ _ _).symm (r • RestrictScalars.addEquiv _ _ _ m) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single, Representation.ofModule,
      RestrictScalars.lsmul_apply_apply]
  · intro f g fw gw
    simp only [fw, gw, map_add, add_smul, LinearMap.add_apply]
  · intro r f w
    simp only [w, map_smul, LinearMap.smul_apply, RestrictScalars.addEquiv_symm_map_smul_smul]

@[simp]
/--
theorem `ofModule_asModule_act` / 定理 `ofModule_asModule_act`

English:
theorem ofModule_asModule_act
  given: (g : G) (x : RestrictScalars k k[G] ρ.asModule)
  proof: by
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp

中文:
定理 ofModule_asModule_act
  条件: (g : G) (x : RestrictScalars k k[G] ρ.asModule)
  证明: by
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp

Depends on / 依赖: RestrictScalars, RestrictScalars.lsmul_apply_apply, lsmul_apply_apply, ofModule
-/
theorem ofModule_asModule_act (g : G) (x : RestrictScalars k k[G] ρ.asModule) :
    ofModule ρ.asModule g x =
      (RestrictScalars.addEquiv _ _ _).symm
        (ρ.asModuleEquiv.symm (ρ g (ρ.asModuleEquiv (RestrictScalars.addEquiv _ _ _ x)))) := by
  dsimp [ofModule, RestrictScalars.lsmul_apply_apply]
  simp

/--
theorem `smul_ofModule_asModule` / 定理 `smul_ofModule_asModule`

English:
theorem smul_ofModule_asModule
  given: (r : k[G]) (m : (ofModule M).asModule)
  proof: by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

中文:
定理 smul_ofModule_asModule
  条件: (r : k[G]) (m : (ofModule M).asModule)
  证明: by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

Depends on / 依赖: AddEquiv, AddEquiv.apply_symm_apply, apply_symm_apply, ofModule_asAlgebraHom_apply_apply
-/
theorem smul_ofModule_asModule (r : k[G]) (m : (ofModule M).asModule) :
    (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (r • m)) =
      r • (RestrictScalars.addEquiv k _ _) ((ofModule M).asModuleEquiv (G := G) m) := by
  dsimp
  simp only [AddEquiv.apply_symm_apply, ofModule_asAlgebraHom_apply_apply]

end

@[simp]
/--
lemma `single_smul` / 引理 `single_smul`

English:
lemma single_smul
  given: (t : k) (g : G) (v : ρ.asModule)
  proof: by
  rw [← LinearMap.smul_apply]; rw [← asAlgebraHom_single]; rw [← asModuleEquiv_map_smul]
  rfl

中文:
引理 single_smul
  条件: (t : k) (g : G) (v : ρ.asModule)
  证明: by
  rw [← LinearMap.smul_apply]; rw [← asAlgebraHom_single]; rw [← asModuleEquiv_map_smul]
  rfl

Depends on / 依赖: LinearMap, LinearMap.smul_apply, asAlgebraHom_single, asModuleEquiv_map_smul, smul_apply
-/
lemma single_smul (t : k) (g : G) (v : ρ.asModule) :
    MonoidAlgebra.single (g : G) t • v = t • ρ g (ρ.asModuleEquiv v) := by
  rw [← LinearMap.smul_apply]; rw [← asAlgebraHom_single]; rw [← asModuleEquiv_map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower k k[G] ρ.asModule
  body: by
    revert t
    apply x.induction_on
    · simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc]; rw [smul_eq_mul]; rw [hy (t * s)]; rw [← smul_eq_mul]; rw [smul_assoc]
      aesop

中文:
实例 :
  签名: IsScalarTower k k[G] ρ.asModule
  定义体: by
    revert t
    apply x.induction_on
    · simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc]; rw [smul_eq_mul]; rw [hy (t * s)]; rw [← smul_eq_mul]; rw [smul_assoc]
      aesop

Depends on / 依赖: add_smul, induction_on, revert, smul_assoc, smul_eq_mul, x.induction_on
-/
instance : IsScalarTower k k[G] ρ.asModule where
  smul_assoc t x v := by
    revert t
    apply x.induction_on
    · simp
    · intro y z hy hz
      simp [add_smul, hy, hz]
    · intro s y hy t
      rw [← smul_assoc]; rw [smul_eq_mul]; rw [hy (t * s)]; rw [← smul_eq_mul]; rw [smul_assoc]
      aesop

end MonoidAlgebra

section Norm

variable {k G V : Type*} [Semiring k] [Group G] [Fintype G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V)

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : Module.End k V
  body: ∑ g : G, ρ g

@[simp]

中文:
定义 norm
  签名: : Module.End k V
  定义体: ∑ g : G, ρ g

@[simp]
-/
def norm : Module.End k V := ∑ g : G, ρ g

@[simp]
/--
lemma `norm_comp_self` / 引理 `norm_comp_self`

English:
lemma norm_comp_self
  given: (g : G)
  statement: norm ρ ∘ₗ ρ g = norm ρ
  proof: by
  ext
simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ by simp

@[simp]

中文:
引理 norm_comp_self
  条件: (g : G)
  结论: norm ρ ∘ₗ ρ g = norm ρ
  证明: by
  ext
simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ by simp

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_bijective, Group.mulRight_bijective, mulRight_bijective, sum_bijective
-/
lemma norm_comp_self (g : G) : norm ρ ∘ₗ ρ g = norm ρ := by
  ext
simpa [norm] using Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _ by simp

@[simp]
/--
lemma `norm_self_apply` / 引理 `norm_self_apply`

English:
lemma norm_self_apply
  given: (g : G) (x : V)
  statement: norm ρ (ρ g x) = norm ρ x
  proof: LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]

中文:
引理 norm_self_apply
  条件: (g : G) (x : V)
  结论: norm ρ (ρ g x) = norm ρ x
  证明: LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, norm_comp_self
-/
lemma norm_self_apply (g : G) (x : V) : norm ρ (ρ g x) = norm ρ x :=
  LinearMap.ext_iff.1 (norm_comp_self _ _) x

@[simp]
/--
lemma `self_comp_norm` / 引理 `self_comp_norm`

English:
lemma self_comp_norm
  given: (g : G)
  statement: ρ g ∘ₗ norm ρ = norm ρ
  proof: by
  ext
simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ by simp

@[simp]

中文:
引理 self_comp_norm
  条件: (g : G)
  结论: ρ g ∘ₗ norm ρ = norm ρ
  证明: by
  ext
simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ by simp

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_bijective, Group.mulLeft_bijective, mulLeft_bijective, sum_bijective
-/
lemma self_comp_norm (g : G) : ρ g ∘ₗ norm ρ = norm ρ := by
  ext
simpa [norm] using Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ by simp

@[simp]
/--
lemma `self_norm_apply` / 引理 `self_norm_apply`

English:
lemma self_norm_apply
  given: (g : G) (x : V)
  statement: ρ g (norm ρ x) = norm ρ x
  proof: LinearMap.ext_iff.1 (self_comp_norm _ _) x

中文:
引理 self_norm_apply
  条件: (g : G) (x : V)
  结论: ρ g (norm ρ x) = norm ρ x
  证明: LinearMap.ext_iff.1 (self_comp_norm _ _) x

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, self_comp_norm
-/
lemma self_norm_apply (g : G) (x : V) : ρ g (norm ρ x) = norm ρ x :=
  LinearMap.ext_iff.1 (self_comp_norm _ _) x

end Norm

section Subrepresentation

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
@[simps]
/--
Definition of `subrepresentation` / `subrepresentation` 的定义

English:
definition subrepresentation
  signature: (W : Submodule k V) (le_comap : forall g, W <= W.comap (ρ g))
  body: (ρ g).restrict le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 subrepresentation
  签名: (W : Submodule k V) (le_comap : 对任意 g, W <= W.comap (ρ g))
  定义体: (ρ g).restrict le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

Depends on / 依赖: le_comap, restrict
-/
def subrepresentation (W : Submodule k V) (le_comap : forall g, W <= W.comap (ρ g)) :
    Representation k G W where
toFun g := (ρ g).restrict le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Subrepresentation

section Quotient

variable {k G V : Type*} [Ring k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
@[simps]
/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: (W : Submodule k V) (le_comap : forall g, W <= W.comap (ρ g))
  body: Submodule.mapQ _ _ (ρ g) le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

中文:
定义 quotient
  签名: (W : Submodule k V) (le_comap : 对任意 g, W <= W.comap (ρ g))
  定义体: Submodule.mapQ _ _ (ρ g) le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

Depends on / 依赖: Submodule, Submodule.mapQ, le_comap
-/
def quotient (W : Submodule k V) (le_comap : forall g, W <= W.comap (ρ g)) :
    Representation k G (V ⧸ W) where
toFun g := Submodule.mapQ _ _ (ρ g) le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Quotient

section OfQuotient

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G)

/--
lemma `apply_eq_of_coe_eq` / 引理 `apply_eq_of_coe_eq`

English:
lemma apply_eq_of_coe_eq
  given: [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h)
  proof: by
  ext x
  apply (ρ.apply_bijective g⁻¹).1
  simpa [← Module.End.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

中文:
引理 apply_eq_of_coe_eq
  条件: [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h)
  证明: by
  ext x
  apply (ρ.apply_bijective g⁻¹).1
  simpa [← Module.End.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

Depends on / 依赖: Module, Module.End.mul_apply, QuotientGroup, QuotientGroup.eq, S.subtype, apply_bijective, isTrivial_def, map_mul, mul_apply, subtype
-/
lemma apply_eq_of_coe_eq [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    ρ g = ρ h := by
  ext x
  apply (ρ.apply_bijective g⁻¹).1
  simpa [← Module.End.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

variable [S.Normal]

/--
Definition of `ofQuotient` / `ofQuotient` 的定义

English:
definition ofQuotient
  signature: [IsTrivial (ρ.comp S.subtype)]
  body: (QuotientGroup.con S).lift ρ by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    change ρ (_ * z.unop) _ = _
    exact congr($(apply_eq_of_coe_eq ρ S _ _ (by simp_all)) w)

@[simp]

中文:
定义 ofQuotient
  签名: [IsTrivial (ρ.comp S.subtype)]
  定义体: (QuotientGroup.con S).lift ρ by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    change ρ (_ * z.unop) _ = _
    exact congr($(apply_eq_of_coe_eq ρ S _ _ (by simp_all)) w)

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.con, TwoSidedIdeal, TwoSidedIdeal.mul_mem_left, apply_eq_of_coe_eq, mul_mem_left, z.unop
-/
def ofQuotient [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
(QuotientGroup.con S).lift ρ by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    change ρ (_ * z.unop) _ = _
    exact congr($(apply_eq_of_coe_eq ρ S _ _ (by simp_all)) w)

@[simp]
/--
lemma `ofQuotient_coe_apply` / 引理 `ofQuotient_coe_apply`

English:
lemma ofQuotient_coe_apply
  given: [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V)
  proof: rfl

中文:
引理 ofQuotient_coe_apply
  条件: [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V)
  证明: rfl
-/
lemma ofQuotient_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotient ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

end OfQuotient

section AddCommGroup

variable {k G V : Type*} [Ring k] [Monoid G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup ρ.asModule
  body: inferInstanceAs AddCommGroup V

中文:
实例 :
  签名: AddCommGroup ρ.asModule
  定义体: inferInstanceAs AddCommGroup V

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup ρ.asModule := inferInstanceAs AddCommGroup V

/--
lemma `apply_sub_id_partialSum_eq` / 引理 `apply_sub_id_partialSum_eq`

English:
lemma apply_sub_id_partialSum_eq
  given: (n : Nat) (g : G) (x : V)
  proof: by
  induction n with
  | zero => simp [Fin.partialSum]
  | succ n h =>
    have : Fin.init (fun (j : Fin (n + 2)) => ρ (g ^ (j : Nat)) x) =
      fun (j : Fin (n + 1)) => ρ (g ^ (j : Nat)) x := by ext; simp [Fin.init]
    rw [← Fin.succ_eq_last_succ.2 rfl]; rw [Fin.partialSum_succ]; rw [← Fin.parti

中文:
引理 apply_sub_id_partialSum_eq
  条件: (n : 自然数) (g : G) (x : V)
  证明: by
  induction n with
  | zero => simp [Fin.partialSum]
  | succ n h =>
    have : Fin.init (fun (j : Fin (n + 2)) => ρ (g ^ (j : Nat)) x) =
      fun (j : Fin (n + 1)) => ρ (g ^ (j : Nat)) x := by ext; simp [Fin.init]
    rw [← Fin.succ_eq_last_succ.2 rfl]; rw [Fin.partialSum_succ]; rw [← Fin.parti

Depends on / 依赖: Fin.last, partialSum
-/
lemma apply_sub_id_partialSum_eq (n : Nat) (g : G) (x : V) :
    (ρ g - LinearMap.id (R := k) (M := V)) ((Fin.last _).partialSum
      (fun (j : Fin (n + 1)) => ρ (g ^ (j : Nat)) x)) = ρ (g ^ (n + 1)) x - x := by
  induction n with
  | zero => simp [Fin.partialSum]
  | succ n h =>
    have : Fin.init (fun (j : Fin (n + 2)) => ρ (g ^ (j : Nat)) x) =
      fun (j : Fin (n + 1)) => ρ (g ^ (j : Nat)) x := by ext; simp [Fin.init]
    rw [← Fin.succ_eq_last_succ.2 rfl]; rw [Fin.partialSum_succ]; rw [← Fin.partialSum_init]; rw [map_add]; rw [this]; rw [h]
    simp [pow_succ']

end AddCommGroup

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

/--
Definition of `ofMulAction` / `ofMulAction` 的定义

English:
definition ofMulAction
  signature: : Representation k G k[H] where
  body: (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
    (coeffLinearEquiv k).toLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

中文:
定义 ofMulAction
  签名: : Representation k G k[H] where
  定义体: (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
    (coeffLinearEquiv k).toLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

Depends on / 依赖: Finsupp, Finsupp.lmapDomain, coeffLinearEquiv, lmapDomain, symm.toLinearMap, toLinearMap
-/
noncomputable def ofMulAction : Representation k G k[H] where
  toFun g := (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
    (coeffLinearEquiv k).toLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

/--
Definition of `leftRegular` / `leftRegular` 的定义

English:
abbreviation leftRegular
  body: ofMulAction k G G

中文:
缩写 leftRegular
  定义体: ofMulAction k G G

Depends on / 依赖: ofMulAction
-/
noncomputable abbrev leftRegular := ofMulAction k G G

/--
Definition of `diagonal` / `diagonal` 的定义

English:
abbreviation diagonal
  signature: (n : Nat)
  body: ofMulAction k G (Fin n -> G)

中文:
缩写 diagonal
  签名: (n : 自然数)
  定义体: ofMulAction k G (Fin n -> G)

Depends on / 依赖: ofMulAction
-/
noncomputable abbrev diagonal (n : Nat) := ofMulAction k G (Fin n -> G)

variable {k G H}

/--
theorem `ofMulAction_def` / 定理 `ofMulAction_def`

English:
theorem ofMulAction_def
  given: (g : G)
  proof: rfl

@[simp]

中文:
定理 ofMulAction_def
  条件: (g : G)
  证明: rfl

@[simp]
-/
theorem ofMulAction_def (g : G) :
    ofMulAction k G H g = (coeffLinearEquiv k).symm.toLinearMap ∘ₗ Finsupp.lmapDomain k k (g • ·) ∘ₗ
      (coeffLinearEquiv k).toLinearMap := rfl

@[simp]
/--
theorem `ofMulAction_single` / 定理 `ofMulAction_single`

English:
theorem ofMulAction_single
  given: (g : G) (x : H) (r : k)
  proof: by simp [ofMulAction_def]

中文:
定理 ofMulAction_single
  条件: (g : G) (x : H) (r : k)
  证明: by simp [ofMulAction_def]

Depends on / 依赖: ofMulAction_def
-/
theorem ofMulAction_single (g : G) (x : H) (r : k) :
    ofMulAction k G H g (single x r) = single (g • x) r := by simp [ofMulAction_def]

end MulAction
section DistribMulAction

variable (k G A : Type*) [Semiring k] [Monoid G] [AddCommMonoid A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]

/--
Definition of `ofDistribMulAction` / `ofDistribMulAction` 的定义

English:
definition ofDistribMulAction
  signature: : Representation k G A where
  body: fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

中文:
定义 ofDistribMulAction
  签名: : Representation k G A where
  定义体: fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _
-/
def ofDistribMulAction : Representation k G A where
  toFun := fun m =>
    { DistribMulAction.toAddMonoidEnd G A m with
      map_smul' := smul_comm _ }
  map_one' := by ext; exact one_smul _ _
  map_mul' := by intros; ext; exact mul_smul _ _ _

variable {k G A}

/--
theorem `ofDistribMulAction_apply_apply` / 定理 `ofDistribMulAction_apply_apply`

English:
theorem ofDistribMulAction_apply_apply
  given: (g : G) (a : A)
  proof: rfl

@[simp]

中文:
定理 ofDistribMulAction_apply_apply
  条件: (g : G) (a : A)
  证明: rfl

@[simp]
-/
@[simp] theorem ofDistribMulAction_apply_apply (g : G) (a : A) :
    ofDistribMulAction k G A g a = g • a := rfl

@[simp]
/--
theorem `norm_ofDistribMulAction_eq` / 定理 `norm_ofDistribMulAction_eq`

English:
theorem norm_ofDistribMulAction_eq
  statement: {G : Type*} [Group G] [Fintype G]
  proof: by
  simp [norm]

中文:
定理 norm_ofDistribMulAction_eq
  结论: {G : 类型} [Group G] [Fintype G]
  证明: by
  simp [norm]
-/
theorem norm_ofDistribMulAction_eq {G : Type*} [Group G] [Fintype G]
    [DistribMulAction G A] [SMulCommClass G k A] (x : A) :
    (ofDistribMulAction k G A).norm x = ∑ g : G, g • x := by
  simp [norm]

end DistribMulAction
section MulDistribMulAction
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/--
Definition of `ofMulDistribMulAction` / `ofMulDistribMulAction` 的定义

English:
definition ofMulDistribMulAction
  signature: : Representation Int M (Additive G)
  body: (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) ->* _).comp
    ((monoidEndToAdditive G : _ ->* _).comp (MulDistribMulAction.toMonoidEnd M G))

中文:
定义 ofMulDistribMulAction
  签名: : Representation 整数 M (Additive G)
  定义体: (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) ->* _).comp
    ((monoidEndToAdditive G : _ ->* _).comp (MulDistribMulAction.toMonoidEnd M G))

Depends on / 依赖: AddMonoid, AddMonoid.End, Additive, MulDistribMulAction, MulDistribMulAction.toMonoidEnd, addMonoidEndRingEquivInt, monoidEndToAdditive, toMonoidEnd
-/
def ofMulDistribMulAction : Representation Int M (Additive G) :=
  (addMonoidEndRingEquivInt (Additive G) : AddMonoid.End (Additive G) ->* _).comp
    ((monoidEndToAdditive G : _ ->* _).comp (MulDistribMulAction.toMonoidEnd M G))

/--
theorem `ofMulDistribMulAction_apply_apply` / 定理 `ofMulDistribMulAction_apply_apply`

English:
theorem ofMulDistribMulAction_apply_apply
  given: (g : M) (a : Additive G)
  proof: rfl

@[simp]

中文:
定理 ofMulDistribMulAction_apply_apply
  条件: (g : M) (a : Additive G)
  证明: rfl

@[simp]
-/
@[simp] theorem ofMulDistribMulAction_apply_apply (g : M) (a : Additive G) :
    ofMulDistribMulAction M G g a = Additive.ofMul (g • a.toMul) := rfl

@[simp]
/--
theorem `norm_ofMulDistribMulAction_eq` / 定理 `norm_ofMulDistribMulAction_eq`

English:
theorem norm_ofMulDistribMulAction_eq
  statement: {G M : Type} [Group G] [Fintype G]
  proof: by
  simp [norm]

中文:
定理 norm_ofMulDistribMulAction_eq
  结论: {G M : Type} [Group G] [Fintype G]
  证明: by
  simp [norm]
-/
theorem norm_ofMulDistribMulAction_eq {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] (x : Additive M) :
    Additive.toMul ((ofMulDistribMulAction G M).norm x) =
      ∏ g : G, g • Additive.toMul x := by
  simp [norm]

end MulDistribMulAction
section Group

section

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)
@[simp]
/--
theorem `coeff_ofMulAction` / 定理 `coeff_ofMulAction`

English:
theorem coeff_ofMulAction
  given: {H : Type*} [MulAction G H] (g : G) (f : k[H]) (h : H)
  proof: by
  conv_lhs => rw [← smul_inv_smul g h]
  set h' := g⁻¹ • h
  have hg : Function.Injective (g • · : H -> H) := by
    intro h₁ h₂
    simp
  simp [ofMulAction_def, Finsupp.mapDomain_apply, hg]

@[deprecated (since := "2026-06-18")] alias ofMulAction_apply := coeff_ofMulAction

中文:
定理 coeff_ofMulAction
  条件: {H : 类型} [MulAction G H] (g : G) (f : k[H]) (h : H)
  证明: by
  conv_lhs => rw [← smul_inv_smul g h]
  set h' := g⁻¹ • h
  have hg : Function.Injective (g • · : H -> H) := by
    intro h₁ h₂
    simp
  simp [ofMulAction_def, Finsupp.mapDomain_apply, hg]

@[deprecated (since := "2026-06-18")] alias ofMulAction_apply := coeff_ofMulAction

Depends on / 依赖: Finsupp, Finsupp.mapDomain_apply, Function, Function.Injective, Injective, conv_lhs, mapDomain_apply, ofMulAction_def, smul_inv_smul
-/
theorem coeff_ofMulAction {H : Type*} [MulAction G H] (g : G) (f : k[H]) (h : H) :
    (ofMulAction k G H g f).coeff h = f.coeff (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  set h' := g⁻¹ • h
  have hg : Function.Injective (g • · : H -> H) := by
    intro h₁ h₂
    simp
  simp [ofMulAction_def, Finsupp.mapDomain_apply, hg]

@[deprecated (since := "2026-06-18")] alias ofMulAction_apply := coeff_ofMulAction

-- Noncomputable since `MonoidAlgebra.instMul` is now noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HMul k[G] (ofMulAction k G G).asModule k[G]
  body: x * (ofMulAction k G G).asModuleEquiv y

中文:
实例 :
  签名: HMul k[G] (ofMulAction k G G).asModule k[G]
  定义体: x * (ofMulAction k G G).asModuleEquiv y

Depends on / 依赖: asModuleEquiv, ofMulAction
-/
noncomputable instance : HMul k[G] (ofMulAction k G G).asModule k[G] where
  hMul x y := x * (ofMulAction k G G).asModuleEquiv y

end

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

@[simp]
/--
lemma `asAlgebraHom_ofMulAction_smul_eq_mul` / 引理 `asAlgebraHom_ofMulAction_smul_eq_mul`

English:
lemma asAlgebraHom_ofMulAction_smul_eq_mul
  given: (x y : k[G])
  proof: by
  induction x using induction_on with
  | of g => ext; simp [MonoidAlgebra.coeff_single_mul_apply]
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul r x hx => simp [← hx]

@[deprecated (since := "2026-06-18")]
alias ofMulAction_self_smul_eq_mul := asAlgebraHom_ofMulAction_smul_eq_mul

中文:
引理 asAlgebraHom_ofMulAction_smul_eq_mul
  条件: (x y : k[G])
  证明: by
  induction x using induction_on with
  | of g => ext; simp [MonoidAlgebra.coeff_single_mul_apply]
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul r x hx => simp [← hx]

@[deprecated (since := "2026-06-18")]
alias ofMulAction_self_smul_eq_mul := asAlgebraHom_ofMulAction_smul_eq_mul

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.coeff_single_mul_apply, add_mul, coeff_single_mul_apply, induction_on
-/
lemma asAlgebraHom_ofMulAction_smul_eq_mul (x y : k[G]) :
    (ofMulAction k G G).asAlgebraHom x y = x * y := by
  induction x using induction_on with
  | of g => ext; simp [MonoidAlgebra.coeff_single_mul_apply]
  | add x y hx hy => simp [hx, hy, add_mul]
  | smul r x hx => simp [← hx]

@[deprecated (since := "2026-06-18")]
alias ofMulAction_self_smul_eq_mul := asAlgebraHom_ofMulAction_smul_eq_mul

/-- If we equip `k[G]` with the `k`-linear `G`-representation induced by the left regular action of
`G` on itself, the resulting object is isomorphic as a `k[G]`-module to `k[G]` with its natural
`k[G]`-module structure. -/
@[simps]
/--
Definition of `ofMulActionSelfAsModuleEquiv` / `ofMulActionSelfAsModuleEquiv` 的定义

English:
definition ofMulActionSelfAsModuleEquiv
  signature: : (ofMulAction k G G).asModule ≃ₗ[k[G]] k[G] where
  body: (asModuleEquiv _).toAddEquiv
  map_smul' := by simp

中文:
定义 ofMulActionSelfAsModuleEquiv
  签名: : (ofMulAction k G G).asModule ≃ₗ[k[G]] k[G] where
  定义体: (asModuleEquiv _).toAddEquiv
  map_smul' := by simp

Depends on / 依赖: asModuleEquiv, toAddEquiv
-/
noncomputable def ofMulActionSelfAsModuleEquiv : (ofMulAction k G G).asModule ≃ₗ[k[G]] k[G] where
  toAddEquiv := (asModuleEquiv _).toAddEquiv
  map_smul' := by simp

/--
Definition of `asGroupHom` / `asGroupHom` 的定义

English:
definition asGroupHom
  signature: : G ->* Units (V ->ₗ[k] V)
  body: MonoidHom.toHomUnits ρ

中文:
定义 asGroupHom
  签名: : G ->* Units (V ->ₗ[k] V)
  定义体: MonoidHom.toHomUnits ρ

Depends on / 依赖: MonoidHom, MonoidHom.toHomUnits, toHomUnits
-/
def asGroupHom : G ->* Units (V ->ₗ[k] V) :=
  MonoidHom.toHomUnits ρ

/--
theorem `asGroupHom_apply` / 定理 `asGroupHom_apply`

English:
theorem asGroupHom_apply
  given: (g : G)
  statement: ↑(asGroupHom ρ g) = ρ g
  proof: by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

中文:
定理 asGroupHom_apply
  条件: (g : G)
  结论: ↑(asGroupHom ρ g) = ρ g
  证明: by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

Depends on / 依赖: MonoidHom, MonoidHom.coe_toHomUnits, asGroupHom, coe_toHomUnits
-/
theorem asGroupHom_apply (g : G) : ↑(asGroupHom ρ g) = ρ g := by
  simp only [asGroupHom, MonoidHom.coe_toHomUnits]

section Finite

variable [Fintype G]

open Finsupp

/--
lemma `leftRegular_norm_apply` / 引理 `leftRegular_norm_apply`

English:
lemma leftRegular_norm_apply
  proof: by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by simp) (by simp)

中文:
引理 leftRegular_norm_apply
  证明: by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by simp) (by simp)

Depends on / 依赖: Finset, Finset.sum_bijective, Group.mulRight_bijective, Representation, Representation.norm, mulRight_bijective, sum_bijective
-/
lemma leftRegular_norm_apply :
    (leftRegular k G).norm =
      (LinearMap.lsmul k _).flip ((leftRegular k G).norm (single 1 1)) ∘ₗ
      linearCombination _ (fun _ => 1) ∘ₗ (coeffLinearEquiv _).toLinearMap := by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by simp) (by simp)

/--
lemma `leftRegular_norm_eq_zero_iff` / 引理 `leftRegular_norm_eq_zero_iff`

English:
lemma leftRegular_norm_eq_zero_iff
  given: (x : k[G])
  proof: by
  rw [leftRegular_norm_apply]
  constructor
  · rw [MonoidAlgebra.ext_iff, Finsupp.ext_iff]
    intro h
    simpa [norm, Representation.norm] using h 1
  · intro h
    ext
    simp_all

中文:
引理 leftRegular_norm_eq_zero_iff
  条件: (x : k[G])
  证明: by
  rw [leftRegular_norm_apply]
  constructor
  · rw [MonoidAlgebra.ext_iff, Finsupp.ext_iff]
    intro h
    simpa [norm, Representation.norm] using h 1
  · intro h
    ext
    simp_all

Depends on / 依赖: Finsupp, Finsupp.ext_iff, MonoidAlgebra, MonoidAlgebra.ext_iff, Representation, Representation.norm, ext_iff, leftRegular_norm_apply
-/
lemma leftRegular_norm_eq_zero_iff (x : k[G]) :
    (leftRegular k G).norm x = 0 ↔ x.coeff.linearCombination k (fun _ => (1 : k)) = 0 := by
  rw [leftRegular_norm_apply]
  constructor
  · rw [MonoidAlgebra.ext_iff, Finsupp.ext_iff]
    intro h
    simpa [norm, Representation.norm] using h 1
  · intro h
    ext
    simp_all

/--
lemma `ker_leftRegular_norm_eq` / 引理 `ker_leftRegular_norm_eq`

English:
lemma ker_leftRegular_norm_eq
  proof: by
  ext
  exact leftRegular_norm_eq_zero_iff _

中文:
引理 ker_leftRegular_norm_eq
  证明: by
  ext
  exact leftRegular_norm_eq_zero_iff _

Depends on / 依赖: leftRegular_norm_eq_zero_iff
-/
lemma ker_leftRegular_norm_eq :
    LinearMap.ker (leftRegular k G).norm = LinearMap.ker
      (linearCombination k (fun _ => (1 : k)) ∘ₗ (coeffLinearEquiv _).toLinearMap) := by
  ext
  exact leftRegular_norm_eq_zero_iff _

end Finite
section Cyclic

/--
lemma `coeff_of_leftRegular_of_generator` / 引理 `coeff_of_leftRegular_of_generator`

English:
lemma coeff_of_leftRegular_of_generator
  statement: (g : G) (hg : forall x, x in Subgroup.zpowers g)
  proof: by
  rw [MonoidAlgebra.ext_iff]; rw [Finsupp.ext_iff] at hx
  rcases hg γ with ⟨i, rfl⟩
  induction i with
  | zero => simpa using hx g
  | succ n h =>
    simpa [← h, zpow_natCast, zpow_add_one, pow_mul_comm', pow_succ'] using (hx (g ^ (n + 1))).symm
  | pred n h =>
    simpa [zpow_sub, ← h, ← mul_

中文:
引理 coeff_of_leftRegular_of_generator
  结论: (g : G) (hg : 对任意 x, x in Subgroup.zpowers g)
  证明: by
  rw [MonoidAlgebra.ext_iff]; rw [Finsupp.ext_iff] at hx
  rcases hg γ with ⟨i, rfl⟩
  induction i with
  | zero => simpa using hx g
  | succ n h =>
    simpa [← h, zpow_natCast, zpow_add_one, pow_mul_comm', pow_succ'] using (hx (g ^ (n + 1))).symm
  | pred n h =>
    simpa [zpow_sub, ← h, ← mul_

Depends on / 依赖: Finsupp, Finsupp.ext_iff, MonoidAlgebra, MonoidAlgebra.ext_iff, ext_iff, mul_inv_rev, pow_mul_comm, pow_succ, zpow_add_one, zpow_natCast, zpow_sub
-/
lemma coeff_of_leftRegular_of_generator (g : G) (hg : forall x, x in Subgroup.zpowers g)
    (x : k[G]) (hx : leftRegular k G g x = x) (γ : G) :
    x.coeff γ = x.coeff g := by
  rw [MonoidAlgebra.ext_iff]; rw [Finsupp.ext_iff] at hx
  rcases hg γ with ⟨i, rfl⟩
  induction i with
  | zero => simpa using hx g
  | succ n h =>
    simpa [← h, zpow_natCast, zpow_add_one, pow_mul_comm', pow_succ'] using (hx (g ^ (n + 1))).symm
  | pred n h =>
    simpa [zpow_sub, ← h, ← mul_inv_rev, ← pow_mul_comm'] using hx (g ^ (-n : Int))

@[deprecated (since := "2026-06-18")]
alias apply_eq_of_leftRegular_eq_of_generator := coeff_of_leftRegular_of_generator

end Cyclic
end Group

section DirectSum

variable {k G : Type*} [Semiring k] [Monoid G]
variable {ι : Type*} {V : ι -> Type*}
variable [(i : ι) -> AddCommMonoid (V i)] [(i : ι) -> Module k (V i)]
variable (ρ : (i : ι) -> Representation k G (V i))

open DirectSum

/-- Given representations of `G` on a family `V i` indexed by `i`, there is a
natural representation of `G` on their direct sum `⨁ i, V i`.
-/
@[simps]
/--
Definition of `directSum` / `directSum` 的定义

English:
definition directSum
  signature: : Representation k G (⨁ i, V i) where
  body: DirectSum.lmap (fun _ => ρ _ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

中文:
定义 directSum
  签名: : Representation k G (⨁ i, V i) where
  定义体: DirectSum.lmap (fun _ => ρ _ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

Depends on / 依赖: DirectSum, DirectSum.lmap
-/
noncomputable def directSum : Representation k G (⨁ i, V i) where
  toFun g := DirectSum.lmap (fun _ => ρ _ g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

end DirectSum

section Prod

variable {k G V W : Type*} [Semiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/-- Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
product `V × W`.
-/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Representation k G (V × W) where
  body: (ρV g).prodMap (ρW g)
  map_one' := by simp
  map_mul' g h := by simp [prodMap_mul]

中文:
定义 prod
  签名: : Representation k G (V × W) where
  定义体: (ρV g).prodMap (ρW g)
  map_one' := by simp
  map_mul' g h := by simp [prodMap_mul]

Depends on / 依赖: prodMap
-/
noncomputable def prod : Representation k G (V × W) where
  toFun g := (ρV g).prodMap (ρW g)
  map_one' := by simp
  map_mul' g h := by simp [prodMap_mul]

end Prod

section TensorProduct

variable {k G V W : Type*} [CommSemiring k] [Monoid G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

open TensorProduct

/--
Definition of `tprod` / `tprod` 的定义

English:
definition tprod
  signature: : Representation k G (V otimes[k] W) where
  body: TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " otimes " ρW => tprod ρV ρW

@[simp]

中文:
定义 tprod
  签名: : Representation k G (V otimes[k] W) where
  定义体: TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " otimes " ρW => tprod ρV ρW

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.map
-/
noncomputable def tprod : Representation k G (V otimes[k] W) where
  toFun g := TensorProduct.map (ρV g) (ρW g)
  map_one' := by simp only [map_one, TensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, TensorProduct.map_mul]

local notation ρV " otimes " ρW => tprod ρV ρW

@[simp]
/--
theorem `tprod_apply` / 定理 `tprod_apply`

English:
theorem tprod_apply
  given: (g : G)
  statement: (ρV otimes ρW) g = TensorProduct.map (ρV g) (ρW g)
  proof: rfl

中文:
定理 tprod_apply
  条件: (g : G)
  结论: (ρV otimes ρW) g = TensorProduct.map (ρV g) (ρW g)
  证明: rfl
-/
theorem tprod_apply (g : G) : (ρV otimes ρW) g = TensorProduct.map (ρV g) (ρW g) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_tprod_one_asModule` / 定理 `smul_tprod_one_asModule`

English:
theorem smul_tprod_one_asModule
  given: (r : k[G]) (x : V) (y : W)
  proof: by
  change asAlgebraHom (ρV otimes 1) _ _ = asAlgebraHom ρV _ _ otimesₜ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorP

中文:
定理 smul_tprod_one_asModule
  条件: (r : k[G]) (x : V) (y : W)
  证明: by
  change asAlgebraHom (ρV otimes 1) _ _ = asAlgebraHom ρV _ _ otimesₜ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorP

Depends on / 依赖: Finsupp, Finsupp.sum, LinearMap, LinearMap.finsupp_sum_apply, LinearMap.smul_apply, Module, Module.End.one_apply, MonoidAlgebra, MonoidAlgebra.lift_apply, MonoidHom, MonoidHom.one_apply, TensorProduct, TensorProduct.map_tmul, TensorProduct.sum_tmul, asAlgebraHom, asAlgebraHom_def, finsupp_sum_apply, lift_apply, map_tmul, one_apply
-/
theorem smul_tprod_one_asModule (r : k[G]) (x : V) (y : W) :
    r • (show (ρV.tprod 1).asModule from x otimesₜ y) = (r • show ρV.asModule from x) otimesₜ y := by
  change asAlgebraHom (ρV otimes 1) _ _ = asAlgebraHom ρV _ _ otimesₜ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.sum_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_one_tprod_asModule` / 定理 `smul_one_tprod_asModule`

English:
theorem smul_one_tprod_asModule
  given: (r : k[G]) (x : V) (y : W)
  proof: by
  change asAlgebraHom (1 otimes ρW) _ _ = _ otimesₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorP

中文:
定理 smul_one_tprod_asModule
  条件: (r : k[G]) (x : V) (y : W)
  证明: by
  change asAlgebraHom (1 otimes ρW) _ _ = _ otimesₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorP

Depends on / 依赖: Finsupp, Finsupp.sum, LinearMap, LinearMap.finsupp_sum_apply, LinearMap.smul_apply, Module, Module.End.one_apply, MonoidAlgebra, MonoidAlgebra.lift_apply, MonoidHom, MonoidHom.one_apply, TensorProduct, TensorProduct.map_tmul, TensorProduct.tmul_smul, TensorProduct.tmul_sum, asAlgebraHom, asAlgebraHom_def, finsupp_sum_apply, lift_apply, map_tmul
-/
theorem smul_one_tprod_asModule (r : k[G]) (x : V) (y : W) :
    r • (show (1 otimes ρW).asModule from x otimesₜ y) = x otimesₜ (r • show ρW.asModule from y) := by
  change asAlgebraHom (1 otimes ρW) _ _ = _ otimesₜ asAlgebraHom ρW _ _
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_apply, tprod_apply, MonoidHom.one_apply,
    LinearMap.finsupp_sum_apply, LinearMap.smul_apply, TensorProduct.map_tmul, Module.End.one_apply]
  simp only [Finsupp.sum, TensorProduct.tmul_sum, TensorProduct.tmul_smul]

end TensorProduct

section LinearHom

variable {k G V W : Type*} [CommSemiring k] [Group G]
variable [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
variable (ρV : Representation k G V) (ρW : Representation k G W)

/--
Definition of `linHom` / `linHom` 的定义

English:
definition linHom
  signature: : Representation k G (V ->ₗ[k] W) where
  body: { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' := ext fun x => by simp [Module.End.one_eq_id]
  map_mul' g h := ext fun x => by simp [Module.End.mul_

中文:
定义 linHom
  签名: : Representation k G (V ->ₗ[k] W) where
  定义体: { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' := ext fun x => by simp [Module.End.one_eq_id]
  map_mul' g h := ext fun x => by simp [Module.End.mul_

Depends on / 依赖: Module, Module.End.mul_eq_comp, Module.End.one_eq_id, RingHom, RingHom.id_apply, add_comp, comp_add, comp_assoc, comp_smul, id_apply, map_add, map_mul, map_one, map_smul, mul_eq_comp, one_eq_id, simp_rw, smul_comp
-/
def linHom : Representation k G (V ->ₗ[k] W) where
  toFun g :=
    { toFun := fun f => ρW g ∘ₗ f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp_rw [add_comp, comp_add]
      map_smul' := fun r f => by simp_rw [RingHom.id_apply, smul_comp, comp_smul] }
  map_one' := ext fun x => by simp [Module.End.one_eq_id]
  map_mul' g h := ext fun x => by simp [Module.End.mul_eq_comp, comp_assoc]

@[simp]
/--
theorem `linHom_apply` / 定理 `linHom_apply`

English:
theorem linHom_apply
  given: (g : G) (f : V ->ₗ[k] W)
  statement: (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹
  proof: rfl

中文:
定理 linHom_apply
  条件: (g : G) (f : V ->ₗ[k] W)
  结论: (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹
  证明: rfl
-/
theorem linHom_apply (g : G) (f : V ->ₗ[k] W) : (linHom ρV ρW) g f = ρW g ∘ₗ f ∘ₗ ρV g⁻¹ :=
  rfl

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : Representation k G (Module.Dual k V) where
  body: { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' r f := by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]

中文:
定义 dual
  签名: : Representation k G (Module.Dual k V) where
  定义体: { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' r f := by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]

Depends on / 依赖: add_comp, map_add, map_mul, map_one, map_smul
-/
def dual : Representation k G (Module.Dual k V) where
  toFun g :=
    { toFun := fun f => f ∘ₗ ρV g⁻¹
      map_add' := fun f₁ f₂ => by simp only [add_comp]
      map_smul' r f := by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
/--
theorem `dual_apply` / 定理 `dual_apply`

English:
theorem dual_apply
  given: (g : G)
  statement: (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹)
  proof: rfl

中文:
定理 dual_apply
  条件: (g : G)
  结论: (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹)
  证明: rfl
-/
theorem dual_apply (g : G) : (dual ρV) g = Module.Dual.transpose (R := k) (ρV g⁻¹) :=
  rfl

/--
theorem `dualTensorHom_comm` / 定理 `dualTensorHom_comm`

English:
theorem dualTensorHom_comm
  given: (g : G)
  proof: by
  ext; simp [Module.Dual.transpose_apply]

中文:
定理 dualTensorHom_comm
  条件: (g : G)
  证明: by
  ext; simp [Module.Dual.transpose_apply]

Depends on / 依赖: Module, Module.Dual.transpose_apply, transpose_apply
-/
theorem dualTensorHom_comm (g : G) :
    dualTensorHom k V W ∘ₗ TensorProduct.map (ρV.dual g) (ρW g) =
      (linHom ρV ρW) g ∘ₗ dualTensorHom k V W := by
  ext; simp [Module.Dual.transpose_apply]

end LinearHom

section

variable {k G : Type*} [CommSemiring k] [Monoid G] {α A B : Type*}
  [AddCommMonoid A] [Module k A] (ρ : Representation k G A)
  [AddCommMonoid B] [Module k B] (τ : Representation k G B)

open Finsupp

/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
@[simps -isSimp]
/--
Definition of `finsupp` / `finsupp` 的定义

English:
definition finsupp
  signature: (α : Type*)
  body: lsum k fun i => (Finsupp.lsingle i).comp (ρ g)
  map_one' := lhom_ext (fun _ _ => by simp)
  map_mul' _ _ := lhom_ext (fun _ _ => by simp)

@[simp]

中文:
定义 finsupp
  签名: (α : 类型)
  定义体: lsum k fun i => (Finsupp.lsingle i).comp (ρ g)
  map_one' := lhom_ext (fun _ _ => by simp)
  map_mul' _ _ := lhom_ext (fun _ _ => by simp)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.lsingle, lsingle
-/
noncomputable def finsupp (α : Type*) :
    Representation k G (α ->₀ A) where
  toFun g := lsum k fun i => (Finsupp.lsingle i).comp (ρ g)
  map_one' := lhom_ext (fun _ _ => by simp)
  map_mul' _ _ := lhom_ext (fun _ _ => by simp)

@[simp]
/--
lemma `finsupp_single` / 引理 `finsupp_single`

English:
lemma finsupp_single
  given: (g : G) (x : α) (a : A)
  proof: by
  simp [finsupp_apply]

中文:
引理 finsupp_single
  条件: (g : G) (x : α) (a : A)
  证明: by
  simp [finsupp_apply]

Depends on / 依赖: finsupp_apply
-/
lemma finsupp_single (g : G) (x : α) (a : A) :
    ρ.finsupp α g (single x a) = single x (ρ g a) := by
  simp [finsupp_apply]

/--
Definition of `free` / `free` 的定义

English:
abbreviation free
  signature: (k G : Type*) [CommSemiring k] [Monoid G] (α : Type*)
  body: finsupp (leftRegular k G) α

中文:
缩写 free
  签名: (k G : 类型) [CommSemiring k] [Monoid G] (α : 类型)
  定义体: finsupp (leftRegular k G) α

Depends on / 依赖: finsupp, leftRegular
-/
noncomputable abbrev free (k G : Type*) [CommSemiring k] [Monoid G] (α : Type*) :
    Representation k G (α ->₀ k[G]) :=
  finsupp (leftRegular k G) α

noncomputable instance (k G : Type*) [CommRing k] [Monoid G] (α : Type*) :
    AddCommGroup (free k G α).asModule :=
inferInstanceAs AddCommGroup (α ->₀ k[G])

/--
lemma `free_single_single` / 引理 `free_single_single`

English:
lemma free_single_single
  given: (g h : G) (i : α) (r : k)
  proof: by
  simp

中文:
引理 free_single_single
  条件: (g h : G) (i : α) (r : k)
  证明: by
  simp
-/
lemma free_single_single (g h : G) (i : α) (r : k) :
    free k G α g (single i (single h r)) = .single i (single (g * h) r) := by
  simp

variable (k G) (α : Type*)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `finsuppLEquivFreeAsModule` / `finsuppLEquivFreeAsModule` 的定义

English:
definition finsuppLEquivFreeAsModule
  signature: : (α ->₀ k[G]) ≃ₗ[k[G]] (free k G α).asModule where
  body: (asModuleEquiv _).symm.toAddEquiv
  map_smul' x y := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply,
      (free k G α).asModuleEquiv.symm_apply_eq, asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply]
    induction x using MonoidAlgebra.induction_l

中文:
定义 finsuppLEquivFreeAsModule
  签名: : (α ->₀ k[G]) ≃ₗ[k[G]] (free k G α).asModule where
  定义体: (asModuleEquiv _).symm.toAddEquiv
  map_smul' x y := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply,
      (free k G α).asModuleEquiv.symm_apply_eq, asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply]
    induction x using MonoidAlgebra.induction_l

Depends on / 依赖: asModuleEquiv, symm.toAddEquiv, toAddEquiv
-/
noncomputable def finsuppLEquivFreeAsModule : (α ->₀ k[G]) ≃ₗ[k[G]] (free k G α).asModule where
  toAddEquiv := (asModuleEquiv _).symm.toAddEquiv
  map_smul' x y := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply,
      (free k G α).asModuleEquiv.symm_apply_eq, asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply]
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add => simp [*, add_smul]
    | single g a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add => simp [*]
    | single h y =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add => simp [*]
    | single i b => simp

/--
Definition of `freeAsModuleBasis` / `freeAsModuleBasis` 的定义

English:
definition freeAsModuleBasis
  signature: : Basis α k[G] (free k G α).asModule where
  body: (finsuppLEquivFreeAsModule k G α).symm

中文:
定义 freeAsModuleBasis
  签名: : Basis α k[G] (free k G α).asModule where
  定义体: (finsuppLEquivFreeAsModule k G α).symm

Depends on / 依赖: finsuppLEquivFreeAsModule
-/
noncomputable def freeAsModuleBasis : Basis α k[G] (free k G α).asModule where
  repr := (finsuppLEquivFreeAsModule k G α).symm

/--
theorem `free_asModule_free` / 定理 `free_asModule_free`

English:
theorem free_asModule_free
  statement: Module.Free k[G] (free k G α).asModule
  proof: Module.Free.of_basis (freeAsModuleBasis k G α)

中文:
定理 free_asModule_free
  结论: Module.Free k[G] (free k G α).asModule
  证明: Module.Free.of_basis (freeAsModuleBasis k G α)

Depends on / 依赖: Module, Module.Free.of_basis, freeAsModuleBasis, of_basis
-/
theorem free_asModule_free : Module.Free k[G] (free k G α).asModule :=
  Module.Free.of_basis (freeAsModuleBasis k G α)

end
end Representation
