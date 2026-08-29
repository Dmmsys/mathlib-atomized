/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Lie.TensorProduct

/-!
# Extension and restriction of scalars for Lie algebras and Lie modules

Lie algebras and their representations have a well-behaved theory of extension and restriction of
scalars.

## Main definitions

* `LieAlgebra.ExtendScalars.instLieAlgebra`
* `LieAlgebra.ExtendScalars.instLieModule`
* `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

@[expose] public section

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in
/--
Definition of `bracket'` / `bracket'` 的定义

English:
definition bracket'
  signature: : A otimes[R] L ->ₗ[A] A otimes[R] M ->ₗ[A] A otimes[R] M
  body: TensorProduct.curry
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L otimes[R] M ->ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap

@[simp]

中文:
定义 bracket'
  签名: : A otimes[R] L ->ₗ[A] A otimes[R] M ->ₗ[A] A otimes[R] M
  定义体: TensorProduct.curry
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L otimes[R] M ->ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap

@[simp]
-/
private def bracket' : A otimes[R] L ->ₗ[A] A otimes[R] M ->ₗ[A] A otimes[R] M :=
TensorProduct.curry
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L otimes[R] M ->ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap

@[simp]
/--
theorem `bracket'_tmul` / 定理 `bracket'_tmul`

English:
theorem bracket'_tmul
  given: (s t : A) (x : L) (m : M)
  proof: rfl

中文:
定理 bracket'_tmul
  条件: (s t : A) (x : L) (m : M)
  证明: rfl
-/
private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s otimesₜ[R] x) (t otimesₜ[R] m) = (s * t) otimesₜ ⁅x, m⁆ := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bracket (A otimes[R] L) (A otimes[R] M)
  body: bracket' R A L M x m

中文:
实例 :
  签名: Bracket (A otimes[R] L) (A otimes[R] M)
  定义体: bracket' R A L M x m

Depends on / 依赖: bracket
-/
instance : Bracket (A otimes[R] L) (A otimes[R] M) where bracket x m := bracket' R A L M x m

/--
theorem `bracket_def` / 定理 `bracket_def`

English:
theorem bracket_def
  given: (x : A otimes[R] L) (m : A otimes[R] M)
  statement: ⁅x, m⁆ = bracket' R A L M x m
  proof: rfl

@[simp]

中文:
定理 bracket_def
  条件: (x : A otimes[R] L) (m : A otimes[R] M)
  结论: ⁅x, m⁆ = bracket' R A L M x m
  证明: rfl

@[simp]
-/
private theorem bracket_def (x : A otimes[R] L) (m : A otimes[R] M) : ⁅x, m⁆ = bracket' R A L M x m :=
  rfl

@[simp]
/--
theorem `bracket_tmul` / 定理 `bracket_tmul`

English:
theorem bracket_tmul
  given: (s t : A) (x : L) (y : M)
  statement: ⁅s otimesₜ[R] x, t otimesₜ[R] y⁆ = (s * t) otimesₜ ⁅x, y⁆
  proof: rfl

中文:
定理 bracket_tmul
  条件: (s t : A) (x : L) (y : M)
  结论: ⁅s otimesₜ[R] x, t otimesₜ[R] y⁆ = (s * t) otimesₜ ⁅x, y⁆
  证明: rfl
-/
theorem bracket_tmul (s t : A) (x : L) (y : M) : ⁅s otimesₜ[R] x, t otimesₜ[R] y⁆ = (s * t) otimesₜ ⁅x, y⁆ := rfl

set_option backward.privateInPublic true in
/--
theorem `bracket_lie_self` / 定理 `bracket_lie_self`

English:
theorem bracket_lie_self
  given: (x : A otimes[R] L)
  statement: ⁅x, x⁆ = 0
  proof: by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add]; rw [map_add]; rw [Linear

中文:
定理 bracket_lie_self
  条件: (x : A otimes[R] L)
  结论: ⁅x, x⁆ = 0
  证明: by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add]; rw [map_add]; rw [Linear
-/
private theorem bracket_lie_self (x : A otimes[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add]; rw [map_add]; rw [LinearMap.add_apply]; rw [LinearMap.add_apply]; rw [h₁]; rw [h₂]; rw [zero_add]; rw [add_zero]; rw [add_comm]; rw [this]
    refine z₁.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₁ l₁; refine z₂.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero, LinearMap.zero_apply]
      · intro a₂ l₂
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, TensorProduct.tmul_neg, bracket'_tmul,
          add_neg_cancel]
      · intro y₁ y₂ hy₁ hy₂
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, LinearMap.add_apply, map_add]
    · intro y₁ y₂ hy₁ hy₂
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, LinearMap.add_apply, map_add]

set_option backward.privateInPublic true in
/--
theorem `bracket_leibniz_lie` / 定理 `bracket_leibniz_lie`

English:
theorem bracket_leibniz_lie
  given: (x y : A otimes[R] L) (z : A otimes[R] M)
  proof: by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp onl

中文:
定理 bracket_leibniz_lie
  条件: (x y : A otimes[R] L) (z : A otimes[R] M)
  证明: by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp onl
-/
private theorem bracket_leibniz_lie (x y : A otimes[R] L) (z : A otimes[R] M) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero]
      · intro a₃ l₃; simp only [bracket'_tmul]
        rw [mul_left_comm a₂ a₁ a₃]; rw [mul_assoc]; rw [leibniz_lie]; rw [TensorProduct.tmul_add]
      · grind
    · grind [LinearMap.add_apply]
  · grind [LinearMap.add_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instLieRing` / 实例 `instLieRing`

English:
instance instLieRing
  signature: : LieRing (A otimes[R] L) where
  body: by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L

中文:
实例 instLieRing
  签名: : LieRing (A otimes[R] L) where
  定义体: by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, bracket_def, bracket_leibniz_lie, bracket_lie_self, leibniz_lie, lie_add, lie_self, map_add
-/
instance instLieRing : LieRing (A otimes[R] L) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L

/--
Instance `instBaseLieAlgebra` / 实例 `instBaseLieAlgebra`

English:
instance instBaseLieAlgebra
  signature: : LieAlgebra R (A otimes[R] L) where lie_smul
  body: by simp [bracket_def]

中文:
实例 instBaseLieAlgebra
  签名: : LieAlgebra R (A otimes[R] L) where lie_smul
  定义体: by simp [bracket_def]

Depends on / 依赖: bracket_def
-/
instance instBaseLieAlgebra : LieAlgebra R (A otimes[R] L) where lie_smul := by simp [bracket_def]

/--
Instance `instLieAlgebra` / 实例 `instLieAlgebra`

English:
instance instLieAlgebra
  signature: : LieAlgebra A (A otimes[R] L) where lie_smul _a _x _y
  body: map_smul _ _ _

中文:
实例 instLieAlgebra
  签名: : LieAlgebra A (A otimes[R] L) where lie_smul _a _x _y
  定义体: map_smul _ _ _

Depends on / 依赖: map_smul
-/
instance instLieAlgebra : LieAlgebra A (A otimes[R] L) where lie_smul _a _x _y := map_smul _ _ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instLieRingModule` / 实例 `instLieRingModule`

English:
instance instLieRingModule
  signature: : LieRingModule (A otimes[R] L) (A otimes[R] M) where
  body: by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

中文:
实例 instLieRingModule
  签名: : LieRingModule (A otimes[R] L) (A otimes[R] M) where
  定义体: by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, bracket_def, bracket_leibniz_lie, leibniz_lie, lie_add, map_add
-/
instance instLieRingModule : LieRingModule (A otimes[R] L) (A otimes[R] M) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instLieModule` / 实例 `instLieModule`

English:
instance instLieModule
  signature: : LieModule A (A otimes[R] L) (A otimes[R] M) where
  body: by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul _ _ _ := map_smul _ _ _

中文:
实例 instLieModule
  签名: : LieModule A (A otimes[R] L) (A otimes[R] M) where
  定义体: by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul _ _ _ := map_smul _ _ _

Depends on / 依赖: LinearMap, LinearMap.smul_apply, bracket_def, lie_smul, map_smul, smul_apply
-/
instance instLieModule : LieModule A (A otimes[R] L) (A otimes[R] M) where
  smul_lie t x m := by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul _ _ _ := map_smul _ _ _

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  body: { TensorProduct.map f.toLinearMap g with
    map_lie' {x y} := by
      simp only [bracket_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      refine x.induction_on (by simp) ?_ ?_
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ => by simp) (fun _ _ h1 h2 => by simp [h1, h2])


中文:
定义 map
  签名: {R A B L L' : 类型} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  定义体: { TensorProduct.map f.toLinearMap g with
    map_lie' {x y} := by
      simp only [bracket_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      refine x.induction_on (by simp) ?_ ?_
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ => by simp) (fun _ _ h1 h2 => by simp [h1, h2])


Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, LinearMap, LinearMap.coe_toAddHom, TensorProduct, TensorProduct.map, bracket_def, coe_toAddHom, f.toLinearMap, induction_on, map_lie, toFun_eq_coe, toLinearMap, x.induction_on, y.induction_on
-/
def map {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] (f : A ->ₐ[R] B) (g : L ->ₗ⁅R⁆ L') :
    A otimes[R] L ->ₗ⁅R⁆ B otimes[R] L' :=
  { TensorProduct.map f.toLinearMap g with
    map_lie' {x y} := by
      simp only [bracket_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      refine x.induction_on (by simp) ?_ ?_
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ => by simp) (fun _ _ h1 h2 => by simp [h1, h2])
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ h => by simp [h]) (by simp_all) }

@[simp]
/--
lemma `map_apply_tmul` / 引理 `map_apply_tmul`

English:
lemma map_apply_tmul
  statement: {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
  proof: rfl

中文:
引理 map_apply_tmul
  结论: {R A B L L' : 类型} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
  证明: rfl
-/
lemma map_apply_tmul {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {f : A ->ₐ[R] B}
    {g : L ->ₗ⁅R⁆ L'} (a : A) (x : L) :
    map f g (a otimesₜ x) = (f a) otimesₜ (g x) :=
  rfl

end ExtendScalars

namespace RestrictScalars


variable [h : LieRing L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (RestrictScalars R A L)
  body: h

中文:
实例 :
  签名: LieRing (RestrictScalars R A L)
  定义体: h
-/
instance : LieRing (RestrictScalars R A L) :=
  h

variable [CommRing A] [LieAlgebra A L]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `lieAlgebra` / 实例 `lieAlgebra`

English:
instance lieAlgebra
  signature: [CommRing R] [Algebra R A]
  body: (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

中文:
实例 lieAlgebra
  签名: [CommRing R] [Algebra R A]
  定义体: (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

Depends on / 依赖: RestrictScalars, RestrictScalars.addEquiv, addEquiv, algebraMap, lie_smul
-/
instance lieAlgebra [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A L) where
  lie_smul t x y := (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

end RestrictScalars

end LieAlgebra

section ExtendScalars

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
/--
lemma `LieModule.toEnd_baseChange` / 引理 `LieModule.toEnd_baseChange`

English:
lemma LieModule.toEnd_baseChange
  given: (x : L)
  proof: by
  ext; simp

中文:
引理 LieModule.toEnd_baseChange
  条件: (x : L)
  证明: by
  ext; simp
-/
lemma LieModule.toEnd_baseChange (x : L) :
    toEnd A (A otimes[R] L) (A otimes[R] M) (1 otimesₜ x) = (toEnd R L M x).baseChange A := by
  ext; simp

namespace LieSubmodule

variable (N : LieSubmodule R L M)

open LieModule

set_option backward.isDefEq.respectTransparency false in
variable {R L M} in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : LieSubmodule A (A otimes[R] L) (A otimes[R] M)
  body: { (N : Submodule R M).baseChange A with
    lie_mem := by
      intro x m hm
      rw [Submodule.mem_carrier]; rw [SetLike.mem_coe] at hm ⊢
      rw [Submodule.baseChange_eq_span] at hm
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hm
      refine x.induction_on (by simp

中文:
定义 baseChange
  签名: : LieSubmodule A (A otimes[R] L) (A otimes[R] M)
  定义体: { (N : Submodule R M).baseChange A with
    lie_mem := by
      intro x m hm
      rw [Submodule.mem_carrier]; rw [SetLike.mem_coe] at hm ⊢
      rw [Submodule.baseChange_eq_span] at hm
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hm
      refine x.induction_on (by simp

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.mem_span_iff_linearCombination, Finsupp.sum, SetLike, SetLike.mem_coe, Submodule, Submodule.baseChange_eq_span, Submodule.mem_carrier, Submodule.sum_mem, baseChange, baseChange_eq_span, induction_on, lie_mem, linearCombination_apply, map_smul, map_sum, mem_carrier, mem_coe, mem_span_iff_linearCombination
-/
def baseChange : LieSubmodule A (A otimes[R] L) (A otimes[R] M) :=
  { (N : Submodule R M).baseChange A with
    lie_mem := by
      intro x m hm
      rw [Submodule.mem_carrier]; rw [SetLike.mem_coe] at hm ⊢
      rw [Submodule.baseChange_eq_span] at hm
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hm
      refine x.induction_on (by simp) (fun a y => ?_) (fun y z hy hz => ?_)
      · change toEnd A (A otimes[R] L) (A otimes[R] M) _ _ in _
        simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, toEnd_apply_apply]
        refine Submodule.sum_mem _ fun ⟨_, n, hn, h⟩ _ => Submodule.smul_mem _ _ ?_
        rw [Subtype.coe_mk]; rw [← h]
        exact Submodule.tmul_mem_baseChange_of_mem _ (N.lie_mem hn)
      · rw [add_lie]
        exact ((N : Submodule R M).baseChange A).add_mem hy hz }

@[simp]
/--
lemma `coe_baseChange` / 引理 `coe_baseChange`

English:
lemma coe_baseChange
  proof: rfl

中文:
引理 coe_baseChange
  证明: rfl
-/
lemma coe_baseChange :
    (N.baseChange A : Submodule A (A otimes[R] M)) = (N : Submodule R M).baseChange A :=
  rfl

variable {N}

variable {R A L M} in
/--
lemma `tmul_mem_baseChange_of_mem` / 引理 `tmul_mem_baseChange_of_mem`

English:
lemma tmul_mem_baseChange_of_mem
  given: (a : A) {m : M} (hm : m in N)
  proof: (N : Submodule R M).tmul_mem_baseChange_of_mem a hm

中文:
引理 tmul_mem_baseChange_of_mem
  条件: (a : A) {m : M} (hm : m in N)
  证明: (N : Submodule R M).tmul_mem_baseChange_of_mem a hm

Depends on / 依赖: Submodule, tmul_mem_baseChange_of_mem
-/
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m in N) :
    a otimesₜ[R] m in N.baseChange A :=
  (N : Submodule R M).tmul_mem_baseChange_of_mem a hm

/--
lemma `mem_baseChange_iff` / 引理 `mem_baseChange_iff`

English:
lemma mem_baseChange_iff
  given: {m : A otimes[R] M}
  proof: by
  rw [← Submodule.baseChange_eq_span]; rfl

@[simp]

中文:
引理 mem_baseChange_iff
  条件: {m : A otimes[R] M}
  证明: by
  rw [← Submodule.baseChange_eq_span]; rfl

@[simp]

Depends on / 依赖: Submodule, Submodule.baseChange_eq_span, baseChange_eq_span
-/
lemma mem_baseChange_iff {m : A otimes[R] M} :
    m in N.baseChange A ↔
    m in Submodule.span A ((N : Submodule R M).map (TensorProduct.mk R A M 1)) := by
  rw [← Submodule.baseChange_eq_span]; rfl

@[simp]
/--
lemma `baseChange_bot` / 引理 `baseChange_bot`

English:
lemma baseChange_bot
  statement: (⊥ : LieSubmodule R L M).baseChange A = ⊥
  proof: by
  simp only [baseChange, bot_toSubmodule, Submodule.baseChange_bot]
  rfl

@[simp]

中文:
引理 baseChange_bot
  结论: (⊥ : LieSubmodule R L M).baseChange A = ⊥
  证明: by
  simp only [baseChange, bot_toSubmodule, Submodule.baseChange_bot]
  rfl

@[simp]

Depends on / 依赖: Submodule, Submodule.baseChange_bot, baseChange, baseChange_bot, bot_toSubmodule
-/
lemma baseChange_bot : (⊥ : LieSubmodule R L M).baseChange A = ⊥ := by
  simp only [baseChange, bot_toSubmodule, Submodule.baseChange_bot]
  rfl

@[simp]
/--
lemma `baseChange_top` / 引理 `baseChange_top`

English:
lemma baseChange_top
  statement: (⊤ : LieSubmodule R L M).baseChange A = ⊤
  proof: by
  simp only [baseChange, top_toSubmodule, Submodule.baseChange_top]
  rfl

中文:
引理 baseChange_top
  结论: (⊤ : LieSubmodule R L M).baseChange A = ⊤
  证明: by
  simp only [baseChange, top_toSubmodule, Submodule.baseChange_top]
  rfl

Depends on / 依赖: Submodule, Submodule.baseChange_top, baseChange, baseChange_top, top_toSubmodule
-/
lemma baseChange_top : (⊤ : LieSubmodule R L M).baseChange A = ⊤ := by
  simp only [baseChange, top_toSubmodule, Submodule.baseChange_top]
  rfl

/--
lemma `lie_baseChange` / 引理 `lie_baseChange`

English:
lemma lie_baseChange
  given: {I : LieIdeal R L} {N : LieSubmodule R L M}
  proof: by
  set s : Set (A otimes[R] M) := { m | exists x in I, exists n in N, 1 otimesₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | exists x in I, exists n in N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj]; rw [coe_baseChange]; rw [lieIdeal_oper_eq_linear_span']; rw [Submodule

中文:
引理 lie_baseChange
  条件: {I : LieIdeal R L} {N : LieSubmodule R L M}
  证明: by
  set s : Set (A otimes[R] M) := { m | exists x in I, exists n in N, 1 otimesₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | exists x in I, exists n in N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj]; rw [coe_baseChange]; rw [lieIdeal_oper_eq_linear_span']; rw [Submodule

Depends on / 依赖: Submodule, Submodule.baseChange_span, Submodule.span_le.mpr, Submodule.span_mono, TensorProduct, TensorProduct.mk, baseChange_span, coe_baseChange, le_antisymm, lieIdeal_oper_eq_linear_span, otimes, span_le, span_mono, tmul_mem_baseChange, toSubmodule_inj
-/
lemma lie_baseChange {I : LieIdeal R L} {N : LieSubmodule R L M} :
    ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆ := by
  set s : Set (A otimes[R] M) := { m | exists x in I, exists n in N, 1 otimesₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | exists x in I, exists n in N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj]; rw [coe_baseChange]; rw [lieIdeal_oper_eq_linear_span']; rw [Submodule.baseChange_span]; rw [this]; rw [lieIdeal_oper_eq_linear_span']
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨x, hx, m, hm, rfl⟩
    exact ⟨1 otimesₜ x, tmul_mem_baseChange_of_mem 1 hx,
           1 otimesₜ m, tmul_mem_baseChange_of_mem 1 hm, by simp⟩
  · rintro - ⟨x, hx, m, hm, rfl⟩
    rw [mem_baseChange_iff] at hx hm
    refine Submodule.span_induction₂ (p := fun x m _ _ => ⁅x, m⁆ in Submodule.span A s)
      ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hx hm
    · rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact Submodule.subset_span ⟨x, hx, y, hy, by simp⟩
    all_goals { intros; simp [add_mem, Submodule.smul_mem, *] }

end LieSubmodule

end ExtendScalars
