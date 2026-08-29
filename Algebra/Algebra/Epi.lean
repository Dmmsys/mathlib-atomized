/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Algebras which are commutative ring epimorphisms
-/

@[expose] public section

noncomputable section
open Function TensorProduct

namespace Algebra

section Semiring

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

/--
Definition of `IsEpi` / `IsEpi` 的定义

English:
class IsEpi
  parameters: : Prop where
  axioms and operations (1):
    - injective_lift_mul : Injective lift LinearMap.mul R A

中文:
类 是满态射
  参数: : 命题 where
  公理与运算 (1 个):
    - injective_lift_mul : 单射 lift 线性映射.mul R A
-/
protected class IsEpi : Prop where
injective_lift_mul : Injective lift LinearMap.mul R A

/--
lemma `isEpi_iff_forall_one_tmul_eq` / 引理 `isEpi_iff_forall_one_tmul_eq`

English:
lemma isEpi_iff_forall_one_tmul_eq
  proof: by
refine ⟨fun h a => IsEpi.injective_lift_mul by simp, fun h => ⟨fun x y hxy => ?_⟩⟩
  have h' (x : A otimes[R] A) : exists a : A, x = a otimesₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u otimesₜ[R] v = u otimesₜ[R] 1 * 1 otimesₜ[R] v := by simp
                   _ = u otimesₜ[R] 1 * v otimesₜ[R] 1 := by rw [h]
                   _ = (u * v) otimesₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

中文:
引理 isEpi_iff_对任意_one_tmul_eq
  证明: by
refine ⟨fun h a => IsEpi.injective_lift_mul by simp, fun h => ⟨fun x y hxy => ?_⟩⟩
  have h' (x : A otimes[R] A) : exists a : A, x = a otimesₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u otimesₜ[R] v = u otimesₜ[R] 1 * 1 otimesₜ[R] v := by simp
                   _ = u otimesₜ[R] 1 * v otimesₜ[R] 1 := by rw [h]
                   _ = (u * v) otimesₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

Depends on / 依赖: IsEpi.injective_lift_mul, TensorProduct, TensorProduct.induction_on, add_tmul, induction_on, injective_lift_mul, otimes
-/
lemma isEpi_iff_forall_one_tmul_eq :
    Algebra.IsEpi R A ↔ forall a : A, 1 otimesₜ[R] a = a otimesₜ[R] 1 := by
refine ⟨fun h a => IsEpi.injective_lift_mul by simp, fun h => ⟨fun x y hxy => ?_⟩⟩
  have h' (x : A otimes[R] A) : exists a : A, x = a otimesₜ 1 := by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul u v =>
      use u * v
      calc u otimesₜ[R] v = u otimesₜ[R] 1 * 1 otimesₜ[R] v := by simp
                   _ = u otimesₜ[R] 1 * v otimesₜ[R] 1 := by rw [h]
                   _ = (u * v) otimesₜ[R] 1 := by simp
    | add u v hu hv =>
      obtain ⟨u, rfl⟩ := hu
      obtain ⟨v, rfl⟩ := hv
      exact ⟨u + v, by simp [add_tmul]⟩
  obtain ⟨a, rfl⟩ := h' x
  obtain ⟨b, rfl⟩ := h' y
  aesop

/--
lemma `isEpi_of_surjective_algebraMap` / 引理 `isEpi_of_surjective_algebraMap`

English:
lemma isEpi_of_surjective_algebraMap
  given: (h : Surjective (algebraMap R A))
  proof: by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun a => ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one]; rw [smul_tmul]

中文:
引理 isEpi_of_surjective_algebraMap
  条件: (h : 满射 (algebraMap R A))
  证明: by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun a => ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one]; rw [smul_tmul]

Depends on / 依赖: algebraMap_eq_smul_one, isEpi_iff_forall_one_tmul_eq, smul_tmul
-/
lemma isEpi_of_surjective_algebraMap (h : Surjective (algebraMap R A)) :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun a => ?_
  obtain ⟨r, rfl⟩ := h a
  rw [algebraMap_eq_smul_one]; rw [smul_tmul]

end Semiring

-- TODO Generalise to any localization
instance (R A : Type*) [CommRing R] [IsDomain R] [Field A] [Algebra R A] [IsFractionRing R A] :
    Algebra.IsEpi R A := by
  refine (isEpi_iff_forall_one_tmul_eq R A).mpr fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  set f := algebraMap R A with hf
  replace hb : f b != 0 := by aesop
  calc 1 otimesₜ[R] (f a / f b)
       = 1 otimesₜ[R] (a • (1 / f b)) := by rw [← smul_div_assoc, algebraMap_eq_smul_one a]
     _ = f a otimesₜ[R] (1 / f b) := by rw [← smul_tmul, algebraMap_eq_smul_one a]
     _ = (b • (f a / f b)) otimesₜ[R] (1 / f b) := by rw [smul_def, mul_div_cancel₀ _ hb]
     _ = (f a / f b) otimesₜ[R] (b • (1 / f b)) := by rw [smul_tmul]
     _ = (f a / f b) otimesₜ[R] 1 := by rw [smul_def, mul_div_cancel₀ _ hb]

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/--
lemma `isEpi_iff_surjective_algebraMap_of_finite` / 引理 `isEpi_iff_surjective_algebraMap_of_finite`

English:
lemma isEpi_iff_surjective_algebraMap_of_finite
  given: [Module.Finite R A]
  proof: by
  refine ⟨fun h => ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') otimes[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : exists s, 1 otimesₜ[R] s = x otimesₜ[R] y := by
        use x * y
        trans x otimesₜ 1 * 1 otimesₜ y
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ]; rw [← hs]; rw [map_tmul]; rw [this]; rw [zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') otimes[R] (A ⧸ R'))

@[deprecated (since := "2026-01-13")]
alias _root_.RingHom.surjective_of_tmul_eq_tmul_of_finite :=
  isEpi_iff_surjective_algebraMap_of_finite

中文:
引理 isEpi_iff_surjective_algebraMap_of_finite
  条件: [模.有限 R A]
  证明: by
  refine ⟨fun h => ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') otimes[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : exists s, 1 otimesₜ[R] s = x otimesₜ[R] y := by
        use x * y
        trans x otimesₜ 1 * 1 otimesₜ y
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ]; rw [← hs]; rw [map_tmul]; rw [this]; rw [zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') otimes[R] (A ⧸ R'))

@[deprecated (since := "2026-01-13")]
alias _root_.RingHom.surjective_of_tmul_eq_tmul_of_finite :=
  isEpi_iff_surjective_algebraMap_of_finite

Depends on / 依赖: Algebra, Algebra.linearMap, LinearMap, LinearMap.range_eq_top, Quotient, Submodule, Submodule.Quotient.subsingleton_iff, Subsingleton, isEpi_of_surjective_algebraMap, linearMap, mkQ_surjective, otimes, range_eq_top, subsingleton_iff, subsingleton_of_forall_eq, subsingleton_or_nontrivial, zero_add
-/
lemma isEpi_iff_surjective_algebraMap_of_finite [Module.Finite R A] :
    Algebra.IsEpi R A ↔ Surjective (algebraMap R A) := by
  refine ⟨fun h => ?_, isEpi_of_surjective_algebraMap R A⟩
  let R' := (Algebra.linearMap R A).range
  rcases subsingleton_or_nontrivial (A ⧸ R') with h | _
  · rwa [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top] at h
  have : Subsingleton ((A ⧸ R') otimes[R] (A ⧸ R')) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    induction y with
    | zero => rfl
    | add a b e₁ e₂ => rwa [e₁, zero_add]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
      obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
      obtain ⟨s, hs⟩ : exists s, 1 otimesₜ[R] s = x otimesₜ[R] y := by
        use x * y
        trans x otimesₜ 1 * 1 otimesₜ y
        · simp [(isEpi_iff_forall_one_tmul_eq R A).mp]
        · simp
      have : R'.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap R A)⟩
      rw [← map_tmul R'.mkQ R'.mkQ]; rw [← hs]; rw [map_tmul]; rw [this]; rw [zero_tmul]
  cases false_of_nontrivial_of_subsingleton ((A ⧸ R') otimes[R] (A ⧸ R'))

@[deprecated (since := "2026-01-13")]
alias _root_.RingHom.surjective_of_tmul_eq_tmul_of_finite :=
  isEpi_iff_surjective_algebraMap_of_finite

end Ring

section CommSemiring

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

variable {A} in
/--
lemma `tmul_comm` / 引理 `tmul_comm`

English:
lemma tmul_comm
  given: (a b : A)
  proof: by
  have (a b : A) := calc a otimesₜ[R] b
      = a • (1 otimesₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b otimesₜ[R] 1) := by rw [(isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 otimesₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b]; rw [this b a]; rw [smul_comm]

中文:
引理 tmul_comm
  条件: (a b : A)
  证明: by
  have (a b : A) := calc a otimesₜ[R] b
      = a • (1 otimesₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b otimesₜ[R] 1) := by rw [(isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 otimesₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b]; rw [this b a]; rw [smul_comm]

Depends on / 依赖: isEpi_iff_forall_one_tmul_eq, smul_comm, tmul_eq_smul_one_tmul
-/
lemma tmul_comm (a b : A) :
    a otimesₜ[R] b = b otimesₜ[R] a := by
  have (a b : A) := calc a otimesₜ[R] b
      = a • (1 otimesₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b otimesₜ[R] 1) := by rw [(isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 otimesₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b]; rw [this b a]; rw [smul_comm]

section Module

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `injective_lift_lsmul` / 引理 `injective_lift_lsmul`

English:
lemma injective_lift_lsmul
  proof: by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃ A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices forall (a : A) (m : M), 1 otimesₜ[R] (a • m) = a otimesₜ[R] m by
    let f : M ->ₗ[R] A otimes[R] M :=
      { toFun m := 1 otimesₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using! this a m
    exact HasLeftInverse.injective ⟨f, fun x => congr($aux x)⟩
  intro a m
  let f : A otimes[R] A ->ₗ[R] A otimes[R] M := lift
    { toFun x :=
      { toFun y := x otimesₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using! congr_arg f (tmul_comm R 1 a)

中文:
引理 injective_lift_lsmul
  证明: by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃ A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices forall (a : A) (m : M), 1 otimesₜ[R] (a • m) = a otimesₜ[R] m by
    let f : M ->ₗ[R] A otimes[R] M :=
      { toFun m := 1 otimesₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using! this a m
    exact HasLeftInverse.injective ⟨f, fun x => congr($aux x)⟩
  intro a m
  let f : A otimes[R] A ->ₗ[R] A otimes[R] M := lift
    { toFun x :=
      { toFun y := x otimesₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using! congr_arg f (tmul_comm R 1 a)
-/
lemma injective_lift_lsmul :
    Injective (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) := by
  /- Morally the proof is to recognise that we can construct the map `A ⊗[R] M → M` as a
  composition of (`A`-linear) equivalences:
  ```
  A ⊗[R] M ≃ A ⊗[R] (A ⊗[A] M)
           ≃ (A ⊗[R] A) ⊗[A] M
           ≃ A ⊗[A] M
           ≃ M
  ```
  However the second equivalence above requires a version of heterogeneous tensor product
  associativity which is problematic in Mathlib because `TensorProduct.leftModule` prioritises the
  left factor in any tensor product. We therefore formalise a slightly lower level proof below. -/
  suffices forall (a : A) (m : M), 1 otimesₜ[R] (a • m) = a otimesₜ[R] m by
    let f : M ->ₗ[R] A otimes[R] M :=
      { toFun m := 1 otimesₜ m
        map_add' m n := tmul_add _ _ _
        map_smul' r m := tmul_smul _ _ _ }
    have aux : f ∘ₗ (lift <| LinearMap.restrictScalars₁₂ R R (LinearMap.lsmul A M)) = .id := by
      ext a m; simpa using! this a m
    exact HasLeftInverse.injective ⟨f, fun x => congr($aux x)⟩
  intro a m
  let f : A otimes[R] A ->ₗ[R] A otimes[R] M := lift
    { toFun x :=
      { toFun y := x otimesₜ (y • m)
        map_add' := by simp [add_smul, tmul_add]
        map_smul' := by simp }
      map_add' := by intros; ext; simp [add_tmul]
      map_smul' := by intros; ext; simp [smul_tmul'] }
  simpa [f] using! congr_arg f (tmul_comm R 1 a)

/--
Definition of `_root_.TensorProduct.lid'` / `_root_.TensorProduct.lid'` 的定义

English:
definition _root_.TensorProduct.lid'
  signature: : A otimes[R] M ≃ₗ[A] M
  body: .ofBijective
    (AlgebraTensorModule.lift <| LinearMap.restrictScalarsₗ R A M M A ∘ₗ LinearMap.lsmul A M)
    ⟨injective_lift_lsmul R A M, fun m => ⟨1 otimesₜ m, by simp⟩⟩

中文:
定义 _root_.张量积.lid'
  签名: : A otimes[R] M ≃ₗ[A] M
  定义体: .ofBijective
    (AlgebraTensorModule.lift <| LinearMap.restrictScalarsₗ R A M M A ∘ₗ LinearMap.lsmul A M)
    ⟨injective_lift_lsmul R A M, fun m => ⟨1 otimesₜ m, by simp⟩⟩

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, AlgebraTensorModule, AlgebraTensorModule.lift, LinearMap, LinearMap.lsmul, LinearMap.restrictScalars, algebraMap, algebraMap_eq_smul_one, injective_lift_lsmul, ofBijective, smul_assoc, smul_eq_mul, smul_one_mul
-/
def _root_.TensorProduct.lid' : A otimes[R] M ≃ₗ[A] M :=
  .ofBijective
    (AlgebraTensorModule.lift <| LinearMap.restrictScalarsₗ R A M M A ∘ₗ LinearMap.lsmul A M)
    ⟨injective_lift_lsmul R A M, fun m => ⟨1 otimesₜ m, by simp⟩⟩

/--
lemma `_root_.TensorProduct.lid'_apply_tmul` / 引理 `_root_.TensorProduct.lid'_apply_tmul`

English:
lemma _root_.TensorProduct.lid'_apply_tmul
  given: (a : A) (m : M)
  proof: rfl

中文:
引理 _root_.张量积.lid'_apply_tmul
  条件: (a : A) (m : M)
  证明: rfl

Depends on / 依赖: algebraMap, smul_comm
-/
@[simp] lemma _root_.TensorProduct.lid'_apply_tmul (a : A) (m : M) :
    TensorProduct.lid' R A M (a otimesₜ m) = a • m :=
  rfl

/--
lemma `_root_.TensorProduct.lid'_symm_apply` / 引理 `_root_.TensorProduct.lid'_symm_apply`

English:
lemma _root_.TensorProduct.lid'_symm_apply
  given: (m : M)
  proof: (TensorProduct.lid' R A M).injective by simp

中文:
引理 _root_.张量积.lid'_symm_apply
  条件: (m : M)
  证明: (TensorProduct.lid' R A M).injective by simp

Depends on / 依赖: Algebra, Algebra.semiringToRing, semiringToRing
-/
@[simp] lemma _root_.TensorProduct.lid'_symm_apply (m : M) :
    (TensorProduct.lid' R A M).symm m = 1 otimesₜ m :=
(TensorProduct.lid' R A M).injective by simp

end Module

end CommSemiring

end Algebra
