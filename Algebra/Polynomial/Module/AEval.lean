/-
Copyright (c) 2022 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Action of the polynomial ring on module induced by an algebra element.

Given an element `a` in an `R`-algebra `A` and an `A`-module `M` we define an
`R[X]`-module `Module.AEval R M a`, which is a type synonym of `M` with the
action of a polynomial `f` given by `f • m = Polynomial.aeval a f • m`.
In particular `X • m = a • m`.

In the special case that `A = M →ₗ[R] M` and `φ : M →ₗ[R] M`, the module `Module.AEval R M a` is
abbreviated `Module.AEval' φ`. In this module we have `X • m = ↑φ m`.
-/

@[expose] public section

open Set Function Polynomial

namespace Module
/--
Suppose `a` is an element of an `R`-algebra `A` and `M` is an `A`-module.
Loosely speaking, `Module.AEval R M a` is the `R[X]`-module with elements `m : M`,
where the action of a polynomial $f$ is given by $f • m = f(a) • m$.

More precisely, `Module.AEval R M a` has elements `Module.AEval.of R M a m` for `m : M`,
and the action of `f` is `f • (of R M a m) = of R M a ((aeval a f) • m)`.
-/
@[nolint unusedArguments]
/--
Definition of `AEval` / `AEval` 的定义

English:
definition AEval
  signature: (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  body: M
  deriving AddCommMonoid, Module R

中文:
定义 AEval
  签名: (R M : 类型) {A : 类型} [CommSemiring R] [Semiring A] [Algebra R A]
  定义体: M
  deriving AddCommMonoid, Module R
-/
def AEval (R M : Type*) {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : A) := M
  deriving AddCommMonoid, Module R

/--
Instance `AEval.instAddCommGroup` / 实例 `AEval.instAddCommGroup`

English:
instance AEval.instAddCommGroup
  signature: {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
  body: inferInstanceAs (AddCommGroup M)

中文:
实例 AEval.instAddCommGroup
  签名: {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
  定义体: inferInstanceAs (AddCommGroup M)

Depends on / 依赖: AddCommGroup
-/
instance AEval.instAddCommGroup {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
AddCommGroup AEval R M a := inferInstanceAs (AddCommGroup M)

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

namespace AEval

/--
Instance `instFiniteOrig` / 实例 `instFiniteOrig`

English:
instance instFiniteOrig
  signature: [Module.Finite R M]
  body: inferInstanceAs Module.Finite R M

中文:
实例 instFiniteOrig
  签名: [Module.Finite R M]
  定义体: inferInstanceAs Module.Finite R M

Depends on / 依赖: Finite, Module, Module.Finite
-/
instance instFiniteOrig [Module.Finite R M] : Module.Finite R AEval R M a :=
inferInstanceAs Module.Finite R M

/--
Instance `instModulePolynomial` / 实例 `instModulePolynomial`

English:
instance instModulePolynomial
  signature: : Module R[X] AEval R M a
  body: compHom M (aeval a).toRingHom

中文:
实例 instModulePolynomial
  签名: : Module R[X] AEval R M a
  定义体: compHom M (aeval a).toRingHom

Depends on / 依赖: compHom, toRingHom
-/
noncomputable instance instModulePolynomial : Module R[X] AEval R M a :=
  compHom M (aeval a).toRingHom

variable (R M)
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : M ≃ₗ[R] AEval R M a
  body: LinearEquiv.refl _ _

中文:
定义 of
  签名: : M ≃ₗ[R] AEval R M a
  定义体: LinearEquiv.refl _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl
-/
def of : M ≃ₗ[R] AEval R M a :=
  LinearEquiv.refl _ _

variable {R M}

/--
lemma `of_aeval_smul` / 引理 `of_aeval_smul`

English:
lemma of_aeval_smul
  given: (f : R[X]) (m : M)
  statement: of R M a (aeval a f • m) = f • of R M a m
  proof: rfl

中文:
引理 of_aeval_smul
  条件: (f : R[X]) (m : M)
  结论: of R M a (aeval a f • m) = f • of R M a m
  证明: rfl
-/
lemma of_aeval_smul (f : R[X]) (m : M) : of R M a (aeval a f • m) = f • of R M a m := rfl

/--
lemma `of_symm_smul` / 引理 `of_symm_smul`

English:
lemma of_symm_smul
  given: (f : R[X]) (m : AEval R M a)
  proof: rfl

中文:
引理 of_symm_smul
  条件: (f : R[X]) (m : AEval R M a)
  证明: rfl
-/
@[simp] lemma of_symm_smul (f : R[X]) (m : AEval R M a) :
    (of R M a).symm (f • m) = aeval a f • (of R M a).symm m := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `C_smul` / 引理 `C_smul`

English:
lemma C_smul
  given: (t : R) (m : AEval R M a)
  statement: C t • m = t • m
  proof: (of R M a).symm.injective by simp

中文:
引理 C_smul
  条件: (t : R) (m : AEval R M a)
  结论: C t • m = t • m
  证明: (of R M a).symm.injective by simp
-/
@[simp] lemma C_smul (t : R) (m : AEval R M a) : C t • m = t • m :=
(of R M a).symm.injective by simp

/--
lemma `X_smul_of` / 引理 `X_smul_of`

English:
lemma X_smul_of
  given: (m : M)
  statement: (X : R[X]) • (of R M a m) = of R M a (a • m)
  proof: by
  rw [← of_aeval_smul]; rw [aeval_X]

中文:
引理 X_smul_of
  条件: (m : M)
  结论: (X : R[X]) • (of R M a m) = of R M a (a • m)
  证明: by
  rw [← of_aeval_smul]; rw [aeval_X]

Depends on / 依赖: aeval_X, of_aeval_smul
-/
lemma X_smul_of (m : M) : (X : R[X]) • (of R M a m) = of R M a (a • m) := by
  rw [← of_aeval_smul]; rw [aeval_X]

/--
lemma `X_pow_smul_of` / 引理 `X_pow_smul_of`

English:
lemma X_pow_smul_of
  given: (m : M) (n : Nat)
  statement: (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m)
  proof: by
  rw [← of_aeval_smul]; rw [aeval_X_pow]

中文:
引理 X_pow_smul_of
  条件: (m : M) (n : 自然数)
  结论: (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m)
  证明: by
  rw [← of_aeval_smul]; rw [aeval_X_pow]

Depends on / 依赖: aeval_X_pow, of_aeval_smul
-/
lemma X_pow_smul_of (m : M) (n : Nat) : (X ^ n : R[X]) • (of R M a m) = of R M a (a ^ n • m) := by
  rw [← of_aeval_smul]; rw [aeval_X_pow]

/--
lemma `of_symm_X_smul` / 引理 `of_symm_X_smul`

English:
lemma of_symm_X_smul
  given: (m : AEval R M a)
  proof: by
  rw [of_symm_smul]; rw [aeval_X]

中文:
引理 of_symm_X_smul
  条件: (m : AEval R M a)
  证明: by
  rw [of_symm_smul]; rw [aeval_X]

Depends on / 依赖: aeval_X, of_symm_smul
-/
lemma of_symm_X_smul (m : AEval R M a) :
    (of R M a).symm ((X : R[X]) • m) = a • (of R M a).symm m := by
  rw [of_symm_smul]; rw [aeval_X]

/--
Instance `instIsScalarTowerOrigPolynomial` / 实例 `instIsScalarTowerOrigPolynomial`

English:
instance instIsScalarTowerOrigPolynomial
  signature: : IsScalarTower R R[X] AEval R M a where
  body: by
    apply (of R M a).symm.injective
    rw [of_symm_smul]; rw [map_smul]; rw [smul_assoc]; rw [map_smul]; rw [of_symm_smul]

中文:
实例 instIsScalarTowerOrigPolynomial
  签名: : IsScalarTower R R[X] AEval R M a where
  定义体: by
    apply (of R M a).symm.injective
    rw [of_symm_smul]; rw [map_smul]; rw [smul_assoc]; rw [map_smul]; rw [of_symm_smul]

Depends on / 依赖: injective, map_smul, of_symm_smul, smul_assoc, symm.injective
-/
instance instIsScalarTowerOrigPolynomial : IsScalarTower R R[X] AEval R M a where
  smul_assoc r f m := by
    apply (of R M a).symm.injective
    rw [of_symm_smul]; rw [map_smul]; rw [smul_assoc]; rw [map_smul]; rw [of_symm_smul]

/--
Instance `instFinitePolynomial` / 实例 `instFinitePolynomial`

English:
instance instFinitePolynomial
  signature: [Module.Finite R M]
  body: Finite.of_restrictScalars_finite R _ _

中文:
实例 instFinitePolynomial
  签名: [Module.Finite R M]
  定义体: Finite.of_restrictScalars_finite R _ _

Depends on / 依赖: Finite, Finite.of_restrictScalars_finite, of_restrictScalars_finite
-/
instance instFinitePolynomial [Module.Finite R M] : Module.Finite R[X] AEval R M a :=
  Finite.of_restrictScalars_finite R _ _

/--
Definition of `_root_.LinearMap.ofAEval` / `_root_.LinearMap.ofAEval` 的定义

English:
definition _root_.LinearMap.ofAEval
  signature: {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
  body: f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m => by simp [C_eq_algebraMap])
    (fun p q hp hq m => by simp_all [add_smul]) fun n k h m => by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h 

中文:
定义 _root_.LinearMap.ofAEval
  签名: {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
  定义体: f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m => by simp [C_eq_algebraMap])
    (fun p q hp hq m => by simp_all [add_smul]) fun n k h m => by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h 
-/
def _root_.LinearMap.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M ->ₗ[R] N) (hf : forall m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a ->ₗ[R[X]] N where
  __ := f ∘ₗ (of R M a).symm
  map_smul' p := p.induction_on (fun k m => by simp [C_eq_algebraMap])
    (fun p q hp hq m => by simp_all [add_smul]) fun n k h m => by
      simp_rw [RingHom.id_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h ⊢
      simp_rw [pow_succ, ← mul_assoc, mul_smul _ X, ← hf, ← of_symm_X_smul, ← h]

/--
Definition of `_root_.LinearEquiv.ofAEval` / `_root_.LinearEquiv.ofAEval` 的定义

English:
definition _root_.LinearEquiv.ofAEval
  signature: {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
  body: LinearMap.ofAEval a f hf
  invFun := (of R M a) ∘ f.symm
  left_inv x := by simp [LinearMap.ofAEval]
  right_inv x := by simp [LinearMap.ofAEval]

中文:
定义 _root_.LinearEquiv.ofAEval
  签名: {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
  定义体: LinearMap.ofAEval a f hf
  invFun := (of R M a) ∘ f.symm
  left_inv x := by simp [LinearMap.ofAEval]
  right_inv x := by simp [LinearMap.ofAEval]

Depends on / 依赖: LinearMap, LinearMap.ofAEval, ofAEval
-/
def _root_.LinearEquiv.ofAEval {N} [AddCommMonoid N] [Module R N] [Module R[X] N]
    [IsScalarTower R R[X] N] (f : M ≃ₗ[R] N) (hf : forall m : M, f (a • m) = (X : R[X]) • f m) :
    AEval R M a ≃ₗ[R[X]] N where
  __ := LinearMap.ofAEval a f hf
  invFun := (of R M a) ∘ f.symm
  left_inv x := by simp [LinearMap.ofAEval]
  right_inv x := by simp [LinearMap.ofAEval]

/--
lemma `annihilator_eq_ker_aeval` / 引理 `annihilator_eq_ker_aeval`

English:
lemma annihilator_eq_ker_aeval
  given: [FaithfulSMul A M]
  proof: by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

@[simp]

中文:
引理 annihilator_eq_ker_aeval
  条件: [FaithfulSMul A M]
  证明: by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

@[simp]

Depends on / 依赖: RingHom, RingHom.mem_ker, eq_of_smul_eq_smul, mem_annihilator, mem_ker, simp_rw
-/
lemma annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator R[X] (AEval R M a) = RingHom.ker (aeval a) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

@[simp]
/--
lemma `annihilator_top_eq_ker_aeval` / 引理 `annihilator_top_eq_ker_aeval`

English:
lemma annihilator_top_eq_ker_aeval
  given: [FaithfulSMul A M]
  proof: by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

中文:
引理 annihilator_top_eq_ker_aeval
  条件: [FaithfulSMul A M]
  证明: by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

Depends on / 依赖: RingHom, RingHom.mem_ker, Submodule, Submodule.mem_annihilator, Submodule.mem_top, eq_of_smul_eq_smul, forall_true_left, mem_annihilator, mem_ker, mem_top
-/
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule R[X] <| AEval R M a).annihilator = RingHom.ker (aeval a) := by
  ext p
  simp only [Submodule.mem_annihilator, Submodule.mem_top, forall_true_left, RingHom.mem_ker]
  change (forall m : M, aeval a p • m = 0) ↔ _
exact ⟨fun h => eq_of_smul_eq_smul (α := M) by simp [h], fun h => by simp [h]⟩

section Submodule

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapSubmodule` / `mapSubmodule` 的定义

English:
definition mapSubmodule
  signature: :
  body: { toAddSubmonoid := (p : Submodule R M).toAddSubmonoid.map (of R M a)
      smul_mem' := by
        rintro f - ⟨m : M, h : m in (p : Submodule R M), rfl⟩
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
   

中文:
定义 mapSubmodule
  签名: :
  定义体: { toAddSubmonoid := (p : Submodule R M).toAddSubmonoid.map (of R M a)
      smul_mem' := by
        rintro f - ⟨m : M, h : m in (p : Submodule R M), rfl⟩
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
   

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_map, AddSubmonoid.mem_toSubsemigroup, AddSubsemigroup, AddSubsemigroup.mem_carrier, Submodule, Submodule.mem_toAddSubmonoid, Submodule.orderIsoMapComap, X_smul_of, aeval_apply_smul_mem_of_le_comap, invFun, mem_carrier, mem_map, mem_toAddSubmonoid, mem_toSubsemigroup, of_aeval_smul, orderIsoMapComap, q.restrictScalars, q.smul_mem, restrictScalars
-/
noncomputable def mapSubmodule :
    (Algebra.lsmul R R M a).invtSubmodule ≃o Submodule R[X] (AEval R M a) where
  toFun p :=
    { toAddSubmonoid := (p : Submodule R M).toAddSubmonoid.map (of R M a)
      smul_mem' := by
        rintro f - ⟨m : M, h : m in (p : Submodule R M), rfl⟩
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
        exact ⟨aeval a f • m, aeval_apply_smul_mem_of_le_comap' h f a p.2, of_aeval_smul a f m⟩ }
  invFun q := ⟨(Submodule.orderIsoMapComap (of R M a)).symm (q.restrictScalars R), fun m hm => by
    simpa [← X_smul_of] using! q.smul_mem (X : R[X]) hm⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p p'} := ⟨fun h x hx => by aesop (rule_sets := [SetLike!]), fun h x hx => by aesop⟩

/--
lemma `mem_mapSubmodule_apply` / 引理 `mem_mapSubmodule_apply`

English:
lemma mem_mapSubmodule_apply
  given: {p : (Algebra.lsmul R R M a).invtSubmodule} {m : AEval R M a}
  proof: ⟨fun ⟨_, hm, hm'⟩ => hm'.symm ▸ hm, fun hm => ⟨(of R M a).symm m, hm, rfl⟩⟩

中文:
引理 mem_mapSubmodule_apply
  条件: {p : (Algebra.lsmul R R M a).invtSubmodule} {m : AEval R M a}
  证明: ⟨fun ⟨_, hm, hm'⟩ => hm'.symm ▸ hm, fun hm => ⟨(of R M a).symm m, hm, rfl⟩⟩
-/
@[simp] lemma mem_mapSubmodule_apply {p : (Algebra.lsmul R R M a).invtSubmodule} {m : AEval R M a} :
    m in mapSubmodule R M a p ↔ (of R M a).symm m in (p : Submodule R M) :=
  ⟨fun ⟨_, hm, hm'⟩ => hm'.symm ▸ hm, fun hm => ⟨(of R M a).symm m, hm, rfl⟩⟩

/--
lemma `mem_mapSubmodule_symm_apply` / 引理 `mem_mapSubmodule_symm_apply`

English:
lemma mem_mapSubmodule_symm_apply
  given: {q : Submodule R[X] (AEval R M a)} {m : M}
  proof: Iff.rfl

中文:
引理 mem_mapSubmodule_symm_apply
  条件: {q : Submodule R[X] (AEval R M a)} {m : M}
  证明: Iff.rfl
-/
@[simp] lemma mem_mapSubmodule_symm_apply {q : Submodule R[X] (AEval R M a)} {m : M} :
    m in ((mapSubmodule R M a).symm q : Submodule R M) ↔ of R M a m in q :=
  Iff.rfl

variable {R M}
variable (p : Submodule R M) (hp : p in (Algebra.lsmul R R M a).invtSubmodule)

/--
Definition of `equiv_mapSubmodule` / `equiv_mapSubmodule` 的定义

English:
definition equiv_mapSubmodule
  signature: :
  body: ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl

中文:
定义 equiv_mapSubmodule
  签名: :
  定义体: ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl
-/
def equiv_mapSubmodule :
    p ≃ₗ[R] mapSubmodule R M a ⟨p, hp⟩ where
  toFun x := ⟨of R M a x, by simp⟩
  invFun x := ⟨((of R M _).symm (x : AEval R M a)), by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  map_add' x y := rfl
  map_smul' t x := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `restrict_equiv_mapSubmodule` / `restrict_equiv_mapSubmodule` 的定义

English:
definition restrict_equiv_mapSubmodule
  signature: :
  body: LinearEquiv.ofAEval ((Algebra.lsmul R R M a).restrict hp) (equiv_mapSubmodule a p hp)
    (fun x => by simp [equiv_mapSubmodule, X_smul_of])

中文:
定义 restrict_equiv_mapSubmodule
  签名: :
  定义体: LinearEquiv.ofAEval ((Algebra.lsmul R R M a).restrict hp) (equiv_mapSubmodule a p hp)
    (fun x => by simp [equiv_mapSubmodule, X_smul_of])

Depends on / 依赖: Algebra, Algebra.lsmul, LinearEquiv, LinearEquiv.ofAEval, X_smul_of, equiv_mapSubmodule, ofAEval, restrict
-/
noncomputable def restrict_equiv_mapSubmodule :
    (AEval R p <| (Algebra.lsmul R R M a).restrict hp) ≃ₗ[R[X]] mapSubmodule R M a ⟨p, hp⟩ :=
  LinearEquiv.ofAEval ((Algebra.lsmul R R M a).restrict hp) (equiv_mapSubmodule a p hp)
    (fun x => by simp [equiv_mapSubmodule, X_smul_of])

end Submodule

end AEval

variable (φ : M ->ₗ[R] M)
/--
Definition of `AEval'` / `AEval'` 的定义

English:
abbreviation AEval'
  body: AEval R M φ

中文:
缩写 AEval'
  定义体: AEval R M φ
-/
abbrev AEval' := AEval R M φ
/--
Definition of `AEval'.of` / `AEval'.of` 的定义

English:
abbreviation AEval'.of
  signature: : M ≃ₗ[R] AEval' φ
  body: AEval.of R M φ

中文:
缩写 AEval'.of
  签名: : M ≃ₗ[R] AEval' φ
  定义体: AEval.of R M φ
-/
abbrev AEval'.of : M ≃ₗ[R] AEval' φ := AEval.of R M φ

/--
lemma `AEval'_def` / 引理 `AEval'_def`

English:
lemma AEval'_def
  statement: AEval' φ = AEval R M φ
  proof: rfl

中文:
引理 AEval'_def
  结论: AEval' φ = AEval R M φ
  证明: rfl
-/
lemma AEval'_def : AEval' φ = AEval R M φ := rfl

/--
lemma `AEval'.X_smul_of` / 引理 `AEval'.X_smul_of`

English:
lemma AEval'.X_smul_of
  given: (m : M)
  statement: (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m)
  proof: AEval.X_smul_of _ _

中文:
引理 AEval'.X_smul_of
  条件: (m : M)
  结论: (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m)
  证明: AEval.X_smul_of _ _
-/
lemma AEval'.X_smul_of (m : M) : (X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m) :=
  AEval.X_smul_of _ _

/--
lemma `AEval'.X_pow_smul_of` / 引理 `AEval'.X_pow_smul_of`

English:
lemma AEval'.X_pow_smul_of
  given: (m : M) (n : Nat)
  statement: (X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m)
  proof: AEval.X_pow_smul_of ..

中文:
引理 AEval'.X_pow_smul_of
  条件: (m : M) (n : 自然数)
  结论: (X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m)
  证明: AEval.X_pow_smul_of ..
-/
lemma AEval'.X_pow_smul_of (m : M) (n : Nat) : (X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m) :=
  AEval.X_pow_smul_of ..

/--
lemma `AEval'.of_symm_X_smul` / 引理 `AEval'.of_symm_X_smul`

English:
lemma AEval'.of_symm_X_smul
  given: (m : AEval' φ)
  proof: AEval.of_symm_X_smul _ _

中文:
引理 AEval'.of_symm_X_smul
  条件: (m : AEval' φ)
  证明: AEval.of_symm_X_smul _ _
-/
lemma AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((X : R[X]) • m) = φ ((AEval'.of φ).symm m) := AEval.of_symm_X_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R M] : Module.Finite R[X] AEval' φ
  body: inferInstance

中文:
实例 [Module.Finite
  签名: R M] : Module.Finite R[X] AEval' φ
  定义体: inferInstance
-/
instance [Module.Finite R M] : Module.Finite R[X] AEval' φ := inferInstance

end Module
