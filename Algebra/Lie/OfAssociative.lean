/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

* `LieAlgebra.ofAssociativeAlgebra`
* `LieAlgebra.ofAssociativeAlgebraHom`
* `LieModule.toEnd`
* `LieAlgebra.ad`
* `LinearEquiv.lieConj`
* `AlgEquiv.toLieEquiv`

## Tags

lie algebra, ring commutator, adjoint action
-/

@[expose] public section


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ring A]

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[instance_reducible]
/--
Definition of `ofAssociativeRing` / `ofAssociativeRing` 的定义

English:
definition ofAssociativeRing
  signature: : LieRing A where
  body: by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_righ

中文:
定义 ofAssociativeRing
  签名: : LieRing A where
  定义体: by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_righ

Depends on / 依赖: Ring.lie_def, forall_const, left_distrib, leibniz_lie, lie_add, lie_def, lie_self, mul_assoc, mul_sub_left_distrib, mul_sub_right_distrib, right_distrib, sub_self
-/
def ofAssociativeRing : LieRing A where
  add_lie _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]; abel

/--
theorem `of_associative_ring_bracket` / 定理 `of_associative_ring_bracket`

English:
theorem of_associative_ring_bracket
  given: (x y : A)
  statement: ⁅x, y⁆ = x * y - y * x
  proof: rfl

@[simp]

中文:
定理 of_associative_ring_bracket
  条件: (x y : A)
  结论: ⁅x, y⁆ = x * y - y * x
  证明: rfl

@[simp]
-/
theorem of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  rfl

@[simp]
/--
theorem `lie_apply` / 定理 `lie_apply`

English:
theorem lie_apply
  given: {α : Type*} (f g : α -> A) (a : α)
  statement: ⁅f, g⁆ a = ⁅f a, g a⁆
  proof: rfl

中文:
定理 lie_apply
  条件: {α : 类型} (f g : α -> A) (a : α)
  结论: ⁅f, g⁆ a = ⁅f a, g a⁆
  证明: rfl
-/
theorem lie_apply {α : Type*} (f g : α -> A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ :=
  rfl

end LieRing

attribute [local instance 100] LieRing.ofAssociativeRing

section AssociativeModule

variable {M : Type w} [AddCommGroup M] [Module A M]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LieRingModule.ofAssociativeModule` / `LieRingModule.ofAssociativeModule` 的定义

English:
abbreviation LieRingModule.ofAssociativeModule
  signature: : LieRingModule A M where
  body: (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]

中文:
缩写 LieRingModule.ofAssociativeModule
  签名: : LieRingModule A M where
  定义体: (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]
-/
abbrev LieRingModule.ofAssociativeModule : LieRingModule A M where
  bracket := (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]

attribute [local instance] LieRingModule.ofAssociativeModule

/--
theorem `lie_eq_smul` / 定理 `lie_eq_smul`

English:
theorem lie_eq_smul
  given: (a : A) (m : M)
  statement: ⁅a, m⁆ = a • m
  proof: rfl

中文:
定理 lie_eq_smul
  条件: (a : A) (m : M)
  结论: ⁅a, m⁆ = a • m
  证明: rfl
-/
theorem lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m :=
  rfl

end AssociativeModule

section LieAlgebra

variable {R : Type u} [CommRing R] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
instance (priority := 100) LieAlgebra.ofAssociativeAlgebra : LieAlgebra R A where
  lie_smul t x y := by
    rw [LieRing.of_associative_ring_bracket]; rw [LieRing.of_associative_ring_bracket]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]; rw [smul_sub]

attribute [local instance] LieRingModule.ofAssociativeModule

section AssociativeRepresentation

variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/--
theorem `LieModule.ofAssociativeModule` / 定理 `LieModule.ofAssociativeModule`

English:
theorem LieModule.ofAssociativeModule
  statement: LieModule R A M where
  proof: smul_assoc
  lie_smul := smul_algebra_smul_comm

中文:
定理 LieModule.ofAssociativeModule
  结论: LieModule R A M where
  证明: smul_assoc
  lie_smul := smul_algebra_smul_comm

Depends on / 依赖: smul_assoc
-/
theorem LieModule.ofAssociativeModule : LieModule R A M where
  smul_lie := smul_assoc
  lie_smul := smul_algebra_smul_comm

/--
Instance `Module.End.instLieRingModule` / 实例 `Module.End.instLieRingModule`

English:
instance Module.End.instLieRingModule
  signature: : LieRingModule (Module.End R M) M
  body: LieRingModule.ofAssociativeModule

中文:
实例 Module.End.instLieRingModule
  签名: : LieRingModule (Module.End R M) M
  定义体: LieRingModule.ofAssociativeModule

Depends on / 依赖: LieRingModule, LieRingModule.ofAssociativeModule, ofAssociativeModule
-/
instance Module.End.instLieRingModule : LieRingModule (Module.End R M) M :=
  LieRingModule.ofAssociativeModule

/--
Instance `Module.End.instLieModule` / 实例 `Module.End.instLieModule`

English:
instance Module.End.instLieModule
  signature: : LieModule R (Module.End R M) M
  body: LieModule.ofAssociativeModule

中文:
实例 Module.End.instLieModule
  签名: : LieModule R (Module.End R M) M
  定义体: LieModule.ofAssociativeModule

Depends on / 依赖: LieModule, LieModule.ofAssociativeModule, ofAssociativeModule
-/
instance Module.End.instLieModule : LieModule R (Module.End R M) M :=
  LieModule.ofAssociativeModule

/--
lemma `Module.End.lie_apply` / 引理 `Module.End.lie_apply`

English:
lemma Module.End.lie_apply
  given: (f : Module.End R M) (m : M)
  statement: ⁅f, m⁆ = f m
  proof: rfl

中文:
引理 Module.End.lie_apply
  条件: (f : Module.End R M) (m : M)
  结论: ⁅f, m⁆ = f m
  证明: rfl
-/
@[simp] lemma Module.End.lie_apply (f : Module.End R M) (m : M) : ⁅f, m⁆ = f m := rfl

-- TODO: fix this
/--
theorem `Module.End.instLieRingModule_eq` / 定理 `Module.End.instLieRingModule_eq`

English:
theorem Module.End.instLieRingModule_eq
  proof: rfl

中文:
定理 Module.End.instLieRingModule_eq
  证明: rfl

Depends on / 依赖: Module, Module.End, lieRingSelfModule
-/
theorem Module.End.instLieRingModule_eq :
    LinearMap.instLieRingModule (L := Module.End R M) (M := M) (N := M) = lieRingSelfModule :=
  rfl

end AssociativeRepresentation

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]
variable (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toLieHom` / `toLieHom` 的定义

English:
definition toLieHom
  signature: : A ->ₗ⁅R⁆ B
  body: { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }

中文:
定义 toLieHom
  签名: : A ->ₗ⁅R⁆ B
  定义体: { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, f.toLinearMap, map_lie, of_associative_ring_bracket, toLinearMap
-/
def toLieHom : A ->ₗ⁅R⁆ B :=
  { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (A ->ₐ[R] B) (A ->ₗ⁅R⁆ B)
  body: ⟨toLieHom⟩

@[simp]

中文:
实例 :
  签名: Coe (A ->ₐ[R] B) (A ->ₗ⁅R⁆ B)
  定义体: ⟨toLieHom⟩

@[simp]

Depends on / 依赖: toLieHom
-/
instance : Coe (A ->ₐ[R] B) (A ->ₗ⁅R⁆ B) :=
  ⟨toLieHom⟩

@[simp]
/--
theorem `coe_toLieHom` / 定理 `coe_toLieHom`

English:
theorem coe_toLieHom
  statement: ((f : A ->ₗ⁅R⁆ B) : A -> B) = f
  proof: rfl

中文:
定理 coe_toLieHom
  结论: ((f : A ->ₗ⁅R⁆ B) : A -> B) = f
  证明: rfl
-/
theorem coe_toLieHom : ((f : A ->ₗ⁅R⁆ B) : A -> B) = f :=
  rfl

/--
theorem `toLieHom_apply` / 定理 `toLieHom_apply`

English:
theorem toLieHom_apply
  given: (x : A)
  statement: f.toLieHom x = f x
  proof: rfl

@[simp]

中文:
定理 toLieHom_apply
  条件: (x : A)
  结论: f.toLieHom x = f x
  证明: rfl

@[simp]
-/
theorem toLieHom_apply (x : A) : f.toLieHom x = f x :=
  rfl

@[simp]
/--
theorem `toLieHom_id` / 定理 `toLieHom_id`

English:
theorem toLieHom_id
  statement: (AlgHom.id R A : A ->ₗ⁅R⁆ A) = LieHom.id
  proof: rfl

@[simp]

中文:
定理 toLieHom_id
  结论: (AlgHom.id R A : A ->ₗ⁅R⁆ A) = LieHom.id
  证明: rfl

@[simp]
-/
theorem toLieHom_id : (AlgHom.id R A : A ->ₗ⁅R⁆ A) = LieHom.id :=
  rfl

@[simp]
/--
theorem `toLieHom_comp` / 定理 `toLieHom_comp`

English:
theorem toLieHom_comp
  statement: (g.comp f : A ->ₗ⁅R⁆ C) = (g : B ->ₗ⁅R⁆ C).comp (f : A ->ₗ⁅R⁆ B)
  proof: rfl

中文:
定理 toLieHom_comp
  结论: (g.comp f : A ->ₗ⁅R⁆ C) = (g : B ->ₗ⁅R⁆ C).comp (f : A ->ₗ⁅R⁆ B)
  证明: rfl
-/
theorem toLieHom_comp : (g.comp f : A ->ₗ⁅R⁆ C) = (g : B ->ₗ⁅R⁆ C).comp (f : A ->ₗ⁅R⁆ B) :=
  rfl

/--
theorem `toLieHom_injective` / 定理 `toLieHom_injective`

English:
theorem toLieHom_injective
  given: {f g : A ->ₐ[R] B} (h : (f : A ->ₗ⁅R⁆ B) = (g : A ->ₗ⁅R⁆ B))
  statement: f = g
  proof: by
  ext a; exact LieHom.congr_fun h a

中文:
定理 toLieHom_injective
  条件: {f g : A ->ₐ[R] B} (h : (f : A ->ₗ⁅R⁆ B) = (g : A ->ₗ⁅R⁆ B))
  结论: f = g
  证明: by
  ext a; exact LieHom.congr_fun h a

Depends on / 依赖: LieHom, LieHom.congr_fun, congr_fun
-/
theorem toLieHom_injective {f g : A ->ₐ[R] B} (h : (f : A ->ₗ⁅R⁆ B) = (g : A ->ₗ⁅R⁆ B)) : f = g := by
  ext a; exact LieHom.congr_fun h a

end AlgHom

end LieAlgebra

end OfAssociative

attribute [local instance 100] LieRing.ofAssociativeRing

section AdjointAction

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `LieModule.toModuleHom`. -/
@[simps]
/--
Definition of `LieModule.toEnd` / `LieModule.toEnd` 的定义

English:
definition LieModule.toEnd
  signature: : L ->ₗ⁅R⁆ Module.End R M where
  body: { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
  map_smul' t x := by ext m; apply smul_lie
  map_lie' {x y} := by ext m; apply lie_lie

中文:
定义 LieModule.toEnd
  签名: : L ->ₗ⁅R⁆ Module.End R M where
  定义体: { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
  map_smul' t x := by ext m; apply smul_lie
  map_lie' {x y} := by ext m; apply lie_lie

Depends on / 依赖: add_lie, lie_add, lie_lie, lie_smul, map_add, map_lie, map_smul, smul_lie
-/
def LieModule.toEnd : L ->ₗ⁅R⁆ Module.End R M where
  toFun x :=
    { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
  map_smul' t x := by ext m; apply smul_lie
  map_lie' {x y} := by ext m; apply lie_lie

/--
Definition of `LieAlgebra.ad` / `LieAlgebra.ad` 的定义

English:
definition LieAlgebra.ad
  signature: : L ->ₗ⁅R⁆ Module.End R L
  body: LieModule.toEnd R L L

@[simp]

中文:
定义 LieAlgebra.ad
  签名: : L ->ₗ⁅R⁆ Module.End R L
  定义体: LieModule.toEnd R L L

@[simp]

Depends on / 依赖: LieModule, LieModule.toEnd
-/
def LieAlgebra.ad : L ->ₗ⁅R⁆ Module.End R L :=
  LieModule.toEnd R L L

@[simp]
/--
theorem `LieAlgebra.ad_apply` / 定理 `LieAlgebra.ad_apply`

English:
theorem LieAlgebra.ad_apply
  given: (x y : L)
  statement: LieAlgebra.ad R L x y = ⁅x, y⁆
  proof: rfl

@[simp]

中文:
定理 LieAlgebra.ad_apply
  条件: (x y : L)
  结论: LieAlgebra.ad R L x y = ⁅x, y⁆
  证明: rfl

@[simp]
-/
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆ :=
  rfl

@[simp]
/--
theorem `LieModule.toEnd_module_end` / 定理 `LieModule.toEnd_module_end`

English:
theorem LieModule.toEnd_module_end
  proof: by ext g m; simp [lie_eq_smul]

中文:
定理 LieModule.toEnd_module_end
  证明: by ext g m; simp [lie_eq_smul]

Depends on / 依赖: lie_eq_smul
-/
theorem LieModule.toEnd_module_end :
    LieModule.toEnd R (Module.End R M) M = LieHom.id := by ext g m; simp [lie_eq_smul]

/--
theorem `LieSubalgebra.toEnd_eq` / 定理 `LieSubalgebra.toEnd_eq`

English:
theorem LieSubalgebra.toEnd_eq
  given: (K : LieSubalgebra R L) {x : K}
  proof: rfl

@[simp]

中文:
定理 LieSubalgebra.toEnd_eq
  条件: (K : LieSubalgebra R L) {x : K}
  证明: rfl

@[simp]
-/
theorem LieSubalgebra.toEnd_eq (K : LieSubalgebra R L) {x : K} :
    LieModule.toEnd R K M x = LieModule.toEnd R L M x :=
  rfl

@[simp]
/--
theorem `LieSubalgebra.toEnd_mk` / 定理 `LieSubalgebra.toEnd_mk`

English:
theorem LieSubalgebra.toEnd_mk
  given: (K : LieSubalgebra R L) {x : L} (hx : x in K)
  proof: rfl

中文:
定理 LieSubalgebra.toEnd_mk
  条件: (K : LieSubalgebra R L) {x : L} (hx : x in K)
  证明: rfl
-/
theorem LieSubalgebra.toEnd_mk (K : LieSubalgebra R L) {x : L} (hx : x in K) :
    LieModule.toEnd R K M ⟨x, hx⟩ = LieModule.toEnd R L M x :=
  rfl

section IsFaithful

open Function

namespace LieModule

/-- A Lie module is *faithful* if the associated map `L → End M` is injective. -/
@[mk_iff]
/--
Definition of `IsFaithful` / `IsFaithful` 的定义

English:
class IsFaithful
  parameters: : Prop where
  axioms and operations (2):
    - injective_toEnd : Injective toEnd R L M
    - @[simp]

中文:
类 IsFaithful
  参数: : 命题 where
  公理与运算 (2 个):
    - injective_toEnd : Injective toEnd R L M
    - @[simp]
-/
class IsFaithful : Prop where
injective_toEnd : Injective toEnd R L M

@[simp]
/--
lemma `toEnd_eq_iff` / 引理 `toEnd_eq_iff`

English:
lemma toEnd_eq_iff
  given: [IsFaithful R L M] {x y : L}
  proof: IsFaithful.injective_toEnd.eq_iff

中文:
引理 toEnd_eq_iff
  条件: [IsFaithful R L M] {x y : L}
  证明: IsFaithful.injective_toEnd.eq_iff

Depends on / 依赖: IsFaithful, IsFaithful.injective_toEnd.eq_iff, eq_iff, injective_toEnd
-/
lemma toEnd_eq_iff [IsFaithful R L M] {x y : L} :
    toEnd R L M x = toEnd R L M y ↔ x = y :=
  IsFaithful.injective_toEnd.eq_iff

variable {R L} in
/--
lemma `ext_of_isFaithful` / 引理 `ext_of_isFaithful`

English:
lemma ext_of_isFaithful
  given: [IsFaithful R L M] {x y : L} (h : forall m : M, ⁅x, m⁆ = ⁅y, m⁆)
  proof: (toEnd_eq_iff R L M).mp LinearMap.ext h

中文:
引理 ext_of_isFaithful
  条件: [IsFaithful R L M] {x y : L} (h : 对任意 m : M, ⁅x, m⁆ = ⁅y, m⁆)
  证明: (toEnd_eq_iff R L M).mp LinearMap.ext h

Depends on / 依赖: LinearMap, LinearMap.ext, toEnd_eq_iff
-/
lemma ext_of_isFaithful [IsFaithful R L M] {x y : L} (h : forall m : M, ⁅x, m⁆ = ⁅y, m⁆) :
    x = y :=
(toEnd_eq_iff R L M).mp LinearMap.ext h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `toEnd_eq_zero_iff` / 引理 `toEnd_eq_zero_iff`

English:
lemma toEnd_eq_zero_iff
  given: [IsFaithful R L M] {x : L}
  proof: by
  rw [← (toEnd R L M).toLinearMap.map_zero]
  exact toEnd_eq_iff R L M

中文:
引理 toEnd_eq_zero_iff
  条件: [IsFaithful R L M] {x : L}
  证明: by
  rw [← (toEnd R L M).toLinearMap.map_zero]
  exact toEnd_eq_iff R L M

Depends on / 依赖: map_zero, toEnd_eq_iff, toLinearMap, toLinearMap.map_zero
-/
lemma toEnd_eq_zero_iff [IsFaithful R L M] {x : L} :
    toEnd R L M x = 0 ↔ x = 0 := by
  rw [← (toEnd R L M).toLinearMap.map_zero]
  exact toEnd_eq_iff R L M

/--
lemma `isFaithful_iff'` / 引理 `isFaithful_iff'`

English:
lemma isFaithful_iff'
  statement: IsFaithful R L M ↔ forall x : L, (forall m : M, ⁅x, m⁆ = 0) -> x = 0
  proof: by
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x y hxy => ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m => ?_
    rw [sub_lie]; rw [sub_eq_zero]; rw [← toEnd_apply_apply R]; rw [← toEnd_apply_apply R]; rw [hxy]

中文:
引理 isFaithful_iff'
  结论: IsFaithful R L M ↔ 对任意 x : L, (对任意 m : M, ⁅x, m⁆ = 0) -> x = 0
  证明: by
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x y hxy => ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m => ?_
    rw [sub_lie]; rw [sub_eq_zero]; rw [← toEnd_apply_apply R]; rw [← toEnd_apply_apply R]; rw [hxy]

Depends on / 依赖: replace, sub_eq_zero, sub_lie, toEnd_apply_apply
-/
lemma isFaithful_iff' : IsFaithful R L M ↔ forall x : L, (forall m : M, ⁅x, m⁆ = 0) -> x = 0 := by
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x y hxy => ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m => ?_
    rw [sub_lie]; rw [sub_eq_zero]; rw [← toEnd_apply_apply R]; rw [← toEnd_apply_apply R]; rw [hxy]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFaithful
  signature: R L M] {L'
  body: by
  refine ⟨(?_ : Injective (toEnd R L M ∘ ((↑) : L' -> L)))⟩
  exact IsFaithful.injective_toEnd.comp Subtype.val_injective

中文:
实例 [IsFaithful
  签名: R L M] {L'
  定义体: by
  refine ⟨(?_ : Injective (toEnd R L M ∘ ((↑) : L' -> L)))⟩
  exact IsFaithful.injective_toEnd.comp Subtype.val_injective

Depends on / 依赖: Injective, IsFaithful, IsFaithful.injective_toEnd.comp, Subtype, Subtype.val_injective, injective_toEnd, val_injective
-/
instance [IsFaithful R L M] {L' : LieSubalgebra R L} :
    IsFaithful R L' M := by
  refine ⟨(?_ : Injective (toEnd R L M ∘ ((↑) : L' -> L)))⟩
  exact IsFaithful.injective_toEnd.comp Subtype.val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFaithful R (Module.End R M) M
  body: by simpa using injective_id

中文:
实例 :
  签名: IsFaithful R (Module.End R M) M
  定义体: by simpa using injective_id

Depends on / 依赖: injective_id
-/
instance : IsFaithful R (Module.End R M) M where
  injective_toEnd := by simpa using injective_id

end LieModule

end IsFaithful


section

open LieAlgebra LieModule

/--
lemma `LieSubmodule.coe_toEnd` / 引理 `LieSubmodule.coe_toEnd`

English:
lemma LieSubmodule.coe_toEnd
  given: (N : LieSubmodule R L M) (x : L) (y : N)
  proof: rfl

中文:
引理 LieSubmodule.coe_toEnd
  条件: (N : LieSubmodule R L M) (x : L) (y : N)
  证明: rfl
-/
lemma LieSubmodule.coe_toEnd (N : LieSubmodule R L M) (x : L) (y : N) :
    (toEnd R L N x y : M) = toEnd R L M x y := rfl

/--
lemma `LieSubmodule.coe_toEnd_pow` / 引理 `LieSubmodule.coe_toEnd_pow`

English:
lemma LieSubmodule.coe_toEnd_pow
  given: (N : LieSubmodule R L M) (x : L) (y : N) (n : Nat)
  proof: by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]

中文:
引理 LieSubmodule.coe_toEnd_pow
  条件: (N : LieSubmodule R L M) (x : L) (y : N) (n : 自然数)
  证明: by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_toEnd, Module, Module.End.mul_apply, coe_toEnd, generalizing, mul_apply, pow_succ
-/
lemma LieSubmodule.coe_toEnd_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : Nat) :
    ((toEnd R L N x ^ n) y : M) = (toEnd R L M x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]

/--
lemma `LieSubalgebra.coe_ad` / 引理 `LieSubalgebra.coe_ad`

English:
lemma LieSubalgebra.coe_ad
  given: (H : LieSubalgebra R L) (x y : H)
  proof: rfl

中文:
引理 LieSubalgebra.coe_ad
  条件: (H : LieSubalgebra R L) (x y : H)
  证明: rfl
-/
lemma LieSubalgebra.coe_ad (H : LieSubalgebra R L) (x y : H) :
    (ad R H x y : L) = ad R L x y := rfl

/--
lemma `LieSubalgebra.coe_ad_pow` / 引理 `LieSubalgebra.coe_ad_pow`

English:
lemma LieSubalgebra.coe_ad_pow
  given: (H : LieSubalgebra R L) (x y : H) (n : Nat)
  proof: LieSubmodule.coe_toEnd_pow R H L H.toLieSubmodule x y n

中文:
引理 LieSubalgebra.coe_ad_pow
  条件: (H : LieSubalgebra R L) (x y : H) (n : 自然数)
  证明: LieSubmodule.coe_toEnd_pow R H L H.toLieSubmodule x y n

Depends on / 依赖: H.toLieSubmodule, LieSubmodule, LieSubmodule.coe_toEnd_pow, coe_toEnd_pow, toLieSubmodule
-/
lemma LieSubalgebra.coe_ad_pow (H : LieSubalgebra R L) (x y : H) (n : Nat) :
    ((ad R H x ^ n) y : L) = (ad R L x ^ n) y :=
  LieSubmodule.coe_toEnd_pow R H L H.toLieSubmodule x y n

variable {L M}

local notation "φ" => LieModule.toEnd R L M

/--
lemma `LieModule.toEnd_lie` / 引理 `LieModule.toEnd_lie`

English:
lemma LieModule.toEnd_lie
  given: (x y : L) (z : M)
  proof: by
  simp

中文:
引理 LieModule.toEnd_lie
  条件: (x y : L) (z : M)
  证明: by
  simp
-/
lemma LieModule.toEnd_lie (x y : L) (z : M) :
    (φ x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆ := by
  simp

/--
lemma `LieAlgebra.ad_lie` / 引理 `LieAlgebra.ad_lie`

English:
lemma LieAlgebra.ad_lie
  given: (x y z : L)
  proof: toEnd_lie _ x y z

中文:
引理 LieAlgebra.ad_lie
  条件: (x y z : L)
  证明: toEnd_lie _ x y z

Depends on / 依赖: toEnd_lie
-/
lemma LieAlgebra.ad_lie (x y z : L) :
    (ad R L x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, ad R L x z⁆ :=
  toEnd_lie _ x y z

open Finset in
/--
lemma `LieModule.toEnd_pow_lie` / 引理 `LieModule.toEnd_pow_lie`

English:
lemma LieModule.toEnd_pow_lie
  given: (x y : L) (z : M) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => ⁅((ad R L x) ^ i) y]; rw [((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_co

中文:
引理 LieModule.toEnd_pow_lie
  条件: (x y : L) (z : M) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => ⁅((ad R L x) ^ i) y]; rw [((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_co

Depends on / 依赖: Finset, Finset.sum_antidiagonal_choose_succ_nsmul, Module, Module.End.mul_apply, Nat.choose_symm_of_eq_add, add_comm, add_left_cancel_iff, choose_symm_of_eq_add, hij.symm, map_nsmul, map_sum, mem_antidiagonal, mul_apply, nsmul_add, pow_succ, sum_add_distrib, sum_antidiagonal_choose_succ_nsmul, sum_congr, toEnd_lie
-/
lemma LieModule.toEnd_pow_lie (x y : L) (z : M) (n : Nat) :
    ((φ x) ^ n) ⁅y, z⁆ =
      ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((φ x) ^ ij.2) z⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => ⁅((ad R L x) ^ i) y]; rw [((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_comm]; rw [add_left_cancel_iff]; rw [sum_congr rfl]
    rintro ⟨i, j⟩ hij
    rw [mem_antidiagonal] at hij
    rw [Nat.choose_symm_of_eq_add hij.symm]

open Finset in
/--
lemma `LieAlgebra.ad_pow_lie` / 引理 `LieAlgebra.ad_pow_lie`

English:
lemma LieAlgebra.ad_pow_lie
  given: (x y z : L) (n : Nat)
  proof: toEnd_pow_lie _ x y z n

中文:
引理 LieAlgebra.ad_pow_lie
  条件: (x y z : L) (n : 自然数)
  证明: toEnd_pow_lie _ x y z n

Depends on / 依赖: toEnd_pow_lie
-/
lemma LieAlgebra.ad_pow_lie (x y z : L) (n : Nat) :
    ((ad R L x) ^ n) ⁅y, z⁆ =
      ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2) z⁆ :=
  toEnd_pow_lie _ x y z n

end

variable {R L M}

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  (f : M ->ₗ⁅R,L⁆ M₂) (k : Nat) (x : L)

/--
lemma `toEnd_pow_comp_lieHom` / 引理 `toEnd_pow_comp_lieHom`

English:
lemma toEnd_pow_comp_lieHom
  proof: by
  apply Module.End.commute_pow_left_of_commute
  ext
  simp

中文:
引理 toEnd_pow_comp_lieHom
  证明: by
  apply Module.End.commute_pow_left_of_commute
  ext
  simp

Depends on / 依赖: Module, Module.End.commute_pow_left_of_commute, commute_pow_left_of_commute
-/
lemma toEnd_pow_comp_lieHom :
    (toEnd R L M₂ x ^ k) ∘ₗ f = f ∘ₗ toEnd R L M x ^ k := by
  apply Module.End.commute_pow_left_of_commute
  ext
  simp

/--
lemma `toEnd_pow_apply_map` / 引理 `toEnd_pow_apply_map`

English:
lemma toEnd_pow_apply_map
  given: (m : M)
  proof: LinearMap.congr_fun (toEnd_pow_comp_lieHom f k x) m

中文:
引理 toEnd_pow_apply_map
  条件: (m : M)
  证明: LinearMap.congr_fun (toEnd_pow_comp_lieHom f k x) m

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, toEnd_pow_comp_lieHom
-/
lemma toEnd_pow_apply_map (m : M) :
    (toEnd R L M₂ x ^ k) (f m) = f ((toEnd R L M x ^ k) m) :=
  LinearMap.congr_fun (toEnd_pow_comp_lieHom f k x) m

end LieModule

namespace LieSubmodule

open LieModule Set

variable {N : LieSubmodule R L M} {x : L}

/--
theorem `coe_map_toEnd_le` / 定理 `coe_map_toEnd_le`

English:
theorem coe_map_toEnd_le
  proof: by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

中文:
定理 coe_map_toEnd_le
  证明: by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

Depends on / 依赖: N.lie_mem, lie_mem
-/
theorem coe_map_toEnd_le :
    (N : Submodule R M).map (LieModule.toEnd R L M x) <= N := by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

variable (N x)

/--
theorem `toEnd_comp_subtype_mem` / 定理 `toEnd_comp_subtype_mem`

English:
theorem toEnd_comp_subtype_mem
  given: (m : M) (hm : m in (N : Submodule R M))
  proof: by
  simpa using N.lie_mem hm

@[simp]

中文:
定理 toEnd_comp_subtype_mem
  条件: (m : M) (hm : m in (N : Submodule R M))
  证明: by
  simpa using N.lie_mem hm

@[simp]

Depends on / 依赖: N.lie_mem, lie_mem
-/
theorem toEnd_comp_subtype_mem (m : M) (hm : m in (N : Submodule R M)) :
    (toEnd R L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ in (N : Submodule R M) := by
  simpa using N.lie_mem hm

@[simp]
/--
theorem `toEnd_restrict_eq_toEnd` / 定理 `toEnd_restrict_eq_toEnd`

English:
theorem toEnd_restrict_eq_toEnd
  given: (h := N.toEnd_comp_subtype_mem x)
  proof: by
  rfl

中文:
定理 toEnd_restrict_eq_toEnd
  条件: (h := N.toEnd_comp_subtype_mem x)
  证明: by
  rfl

Depends on / 依赖: N.toEnd_comp_subtype_mem, toEnd_comp_subtype_mem
-/
theorem toEnd_restrict_eq_toEnd (h := N.toEnd_comp_subtype_mem x) :
    (toEnd R L M x).restrict h = toEnd R L N x := by
  rfl

/--
lemma `mapsTo_pow_toEnd_sub_algebraMap` / 引理 `mapsTo_pow_toEnd_sub_algebraMap`

English:
lemma mapsTo_pow_toEnd_sub_algebraMap
  given: {φ : R} {k : Nat} {x : L}
  proof: by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm => N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

中文:
引理 mapsTo_pow_toEnd_sub_algebraMap
  条件: {φ : R} {k : 自然数} {x : L}
  证明: by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm => N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

Depends on / 依赖: MapsTo, MapsTo.iterate, Module, Module.End.coe_pow, N.lie_mem, N.smul_mem, N.sub_mem, coe_pow, iterate, lie_mem, smul_mem, sub_mem
-/
lemma mapsTo_pow_toEnd_sub_algebraMap {φ : R} {k : Nat} {x : L} :
    MapsTo ((toEnd R L M x - algebraMap R (Module.End R M) φ) ^ k) N N := by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm => N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

end LieSubmodule

open LieAlgebra

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LieAlgebra.ad_eq_lmul_left_sub_lmul_right` / 定理 `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`

English:
theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right
  given: (A : Type v) [Ring A] [Algebra R A]
  proof: by
  ext a b; simp [LieRing.of_associative_ring_bracket]

中文:
定理 LieAlgebra.ad_eq_lmul_left_sub_lmul_right
  条件: (A : 类型v) [Ring A] [Algebra R A]
  证明: by
  ext a b; simp [LieRing.of_associative_ring_bracket]

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, of_associative_ring_bracket
-/
theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R A] :
    (ad R A : A -> Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight R := by
  ext a b; simp [LieRing.of_associative_ring_bracket]

/--
theorem `LieSubalgebra.ad_comp_incl_eq` / 定理 `LieSubalgebra.ad_comp_incl_eq`

English:
theorem LieSubalgebra.ad_comp_incl_eq
  given: (K : LieSubalgebra R L) (x : K)
  proof: by
  ext y
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]

中文:
定理 LieSubalgebra.ad_comp_incl_eq
  条件: (K : LieSubalgebra R L) (x : K)
  证明: by
  ext y
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, LieHom, LieHom.coe_toLinearMap, LieSubalgebra, LieSubalgebra.coe_bracket, LieSubalgebra.coe_incl, LinearMap, LinearMap.coe_comp, ad_apply, coe_bracket, coe_comp, coe_incl, coe_toLinearMap, comp_apply
-/
theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L ↑x).comp (K.incl : K ->ₗ[R] L) = (K.incl : K ->ₗ[R] L).comp (ad R K x) := by
  ext y
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]

end AdjointAction

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lieSubalgebraOfSubalgebra` / `lieSubalgebraOfSubalgebra` 的定义

English:
definition lieSubalgebraOfSubalgebra
  signature: (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
  body: { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ in A'; change x in A' at hx; change y in A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem (Subalgebra.

中文:
定义 lieSubalgebraOfSubalgebra
  签名: (R : 类型u) [CommRing R] (A : 类型v) [Ring A] [Algebra R A]
  定义体: { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ in A'; change x in A' at hx; change y in A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem (Subalgebra.

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, Subalgebra, Subalgebra.toSubmodule, Submodule, Submodule.sub_mem, lie_mem, mul_mem, of_associative_ring_bracket, sub_mem, toSubmodule
-/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
    (A' : Subalgebra R A) : LieSubalgebra R A :=
  { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ in A'; change x in A' at hx; change y in A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem (Subalgebra.toSubmodule A') hxy hyx }

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}
variable [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable (e : M₁ ≃ₗ[R] M₂)

/--
Definition of `lieConj` / `lieConj` 的定义

English:
definition lieConj
  signature: : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂
  body: { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, e.conj_comp,
          map_sub] }

@[simp]

中文:
定义 lieConj
  签名: : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂
  定义体: { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, e.conj_comp,
          map_sub] }

@[simp]

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, Module, Module.End.mul_eq_comp, conj_comp, e.conj, e.conj_comp, map_lie, map_sub, mul_eq_comp, of_associative_ring_bracket
-/
def lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, e.conj_comp,
          map_sub] }

@[simp]
/--
theorem `lieConj_apply` / 定理 `lieConj_apply`

English:
theorem lieConj_apply
  given: (f : Module.End R M₁)
  statement: e.lieConj f = e.conj f
  proof: rfl

@[simp]

中文:
定理 lieConj_apply
  条件: (f : Module.End R M₁)
  结论: e.lieConj f = e.conj f
  证明: rfl

@[simp]
-/
theorem lieConj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f :=
  rfl

@[simp]
/--
theorem `lieConj_symm` / 定理 `lieConj_symm`

English:
theorem lieConj_symm
  statement: e.lieConj.symm = e.symm.lieConj
  proof: rfl

中文:
定理 lieConj_symm
  结论: e.lieConj.symm = e.symm.lieConj
  证明: rfl
-/
theorem lieConj_symm : e.lieConj.symm = e.symm.lieConj :=
  rfl

end LinearEquiv

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}
variable [CommRing R] [Ring A₁] [Ring A₂] [Algebra R A₁] [Algebra R A₂]
variable (e : A₁ ≃ₐ[R] A₂)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toLieEquiv` / `toLieEquiv` 的定义

English:
definition toLieEquiv
  signature: : A₁ ≃ₗ⁅R⁆ A₂
  body: { e.toLinearEquiv with
    toFun := e.toFun
    map_lie' := fun {x y} => by
      have : e.toEquiv.toFun = e := rfl
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }

@[simp]

中文:
定义 toLieEquiv
  签名: : A₁ ≃ₗ⁅R⁆ A₂
  定义体: { e.toLinearEquiv with
    toFun := e.toFun
    map_lie' := fun {x y} => by
      have : e.toEquiv.toFun = e := rfl
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }

@[simp]

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, e.toEquiv.toFun, e.toFun, e.toLinearEquiv, map_lie, map_mul, map_sub, of_associative_ring_bracket, simp_rw, toEquiv, toLinearEquiv
-/
def toLieEquiv : A₁ ≃ₗ⁅R⁆ A₂ :=
  { e.toLinearEquiv with
    toFun := e.toFun
    map_lie' := fun {x y} => by
      have : e.toEquiv.toFun = e := rfl
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }

@[simp]
/--
theorem `toLieEquiv_apply` / 定理 `toLieEquiv_apply`

English:
theorem toLieEquiv_apply
  given: (x : A₁)
  statement: e.toLieEquiv x = e x
  proof: rfl

@[simp]

中文:
定理 toLieEquiv_apply
  条件: (x : A₁)
  结论: e.toLieEquiv x = e x
  证明: rfl

@[simp]
-/
theorem toLieEquiv_apply (x : A₁) : e.toLieEquiv x = e x :=
  rfl

@[simp]
/--
theorem `toLieEquiv_symm_apply` / 定理 `toLieEquiv_symm_apply`

English:
theorem toLieEquiv_symm_apply
  given: (x : A₂)
  statement: e.toLieEquiv.symm x = e.symm x
  proof: rfl

中文:
定理 toLieEquiv_symm_apply
  条件: (x : A₂)
  结论: e.toLieEquiv.symm x = e.symm x
  证明: rfl
-/
theorem toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x :=
  rfl

end AlgEquiv

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

open LieEquiv

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and an element `x : L`, the conjugate
of the endomorphism `ad(x)` of `L` by `e` is the endomorphism `ad(e x)` of `L'`. -/
@[simp]
/--
lemma `conj_ad_apply` / 引理 `conj_ad_apply`

English:
lemma conj_ad_apply
  given: (e : L ≃ₗ⁅R⁆ L') (x : L)
  statement: e.toLinearEquiv.conj (ad R L x) = ad R L' (e x)
  proof: by
  ext y'
  rw [LinearEquiv.conj_apply_apply]; rw [ad_apply]; rw [ad_apply]; rw [coe_toLinearEquiv]; rw [map_lie]; rw [← coe_toLinearEquiv]; rw [LinearEquiv.apply_symm_apply]

中文:
引理 conj_ad_apply
  条件: (e : L ≃ₗ⁅R⁆ L') (x : L)
  结论: e.toLinearEquiv.conj (ad R L x) = ad R L' (e x)
  证明: by
  ext y'
  rw [LinearEquiv.conj_apply_apply]; rw [ad_apply]; rw [ad_apply]; rw [coe_toLinearEquiv]; rw [map_lie]; rw [← coe_toLinearEquiv]; rw [LinearEquiv.apply_symm_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.conj_apply_apply, ad_apply, apply_symm_apply, coe_toLinearEquiv, conj_apply_apply, map_lie
-/
lemma conj_ad_apply (e : L ≃ₗ⁅R⁆ L') (x : L) : e.toLinearEquiv.conj (ad R L x) = ad R L' (e x) := by
  ext y'
  rw [LinearEquiv.conj_apply_apply]; rw [ad_apply]; rw [ad_apply]; rw [coe_toLinearEquiv]; rw [map_lie]; rw [← coe_toLinearEquiv]; rw [LinearEquiv.apply_symm_apply]

end LieAlgebra
