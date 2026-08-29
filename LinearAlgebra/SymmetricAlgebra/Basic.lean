/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the symmetric algebra of `M`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

* `SymmetricAlgebra R M`: a concrete construction of the symmetric algebra defined as a
  quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
  ring structure.
* `SymmetricAlgebra.ι R`: the canonical R-linear map `M →ₗ[R] SymmetricAlgebra R M`.
* Given a morphism `ι : M →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the algebra
  homomorphism from `SymmetricAlgebra R M` to `A` lifted from `ι` is bijective.
* Given a linear map `f : M →ₗ[R] A'` to a commutative R-algebra `A'`, and a morphism
  `ι : M →ₗ[R] A` with `p : IsSymmetricAlgebra ι`, `IsSymmetricAlgebra.lift p f`
  is the lift of `f` to an `R`-algebra morphism `A →ₐ[R] A'`.

## Note

See `SymAlg R` instead if you are looking for the symmetrized algebra, which gives a commutative
multiplication on `R` by $a \circ b = \frac{1}{2}(ab + ba)$.
-/

@[expose] public section

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
Inductive type `TensorAlgebra.SymRel` / 归纳类型 `TensorAlgebra.SymRel`

English:
inductive TensorAlgebra.SymRel
  parameters: : TensorAlgebra R M -> TensorAlgebra R M -> Prop where
  constructors (1):
    - mul_comm: (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)

中文:
归纳类型 TensorAlgebra.SymRel
  参数: : TensorAlgebra R M -> TensorAlgebra R M -> 命题 where
  构造子 (1 个):
    - mul_comm: (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)
-/
inductive TensorAlgebra.SymRel : TensorAlgebra R M -> TensorAlgebra R M -> Prop where
  | mul_comm (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)

/--
Definition of `TensorAlgebra.symRingCon` / `TensorAlgebra.symRingCon` 的定义

English:
definition TensorAlgebra.symRingCon
  signature: : RingCon (TensorAlgebra R M)
  body: ringConGen (SymRel R M)

中文:
定义 TensorAlgebra.symRingCon
  签名: : RingCon (TensorAlgebra R M)
  定义体: ringConGen (SymRel R M)
-/
@[no_expose] def TensorAlgebra.symRingCon : RingCon (TensorAlgebra R M) := ringConGen (SymRel R M)

open TensorAlgebra

/-- Concrete construction of the symmetric algebra of `M` by quotienting out
the tensor algebra by the commutativity relation. -/
.Quotient abbrev SymmetricAlgebra := symRingCon R M

namespace SymmetricAlgebra

/--
Definition of `algHom` / `algHom` 的定义

English:
abbreviation algHom
  signature: : TensorAlgebra R M ->ₐ[R] SymmetricAlgebra R M
  body: RingCon.mkₐ R _

中文:
缩写 algHom
  签名: : TensorAlgebra R M ->ₐ[R] SymmetricAlgebra R M
  定义体: RingCon.mkₐ R _

Depends on / 依赖: RingCon, RingCon.mk
-/
abbrev algHom : TensorAlgebra R M ->ₐ[R] SymmetricAlgebra R M := RingCon.mkₐ R _

/--
lemma `algHom_surjective` / 引理 `algHom_surjective`

English:
lemma algHom_surjective
  statement: Function.Surjective (algHom R M)
  proof: Quotient.mk_surjective

中文:
引理 algHom_surjective
  结论: 函数.满射 (algHom R M)
  证明: Quotient.mk_surjective

Depends on / 依赖: Quotient, Quotient.mk_surjective, mk_surjective
-/
lemma algHom_surjective : Function.Surjective (algHom R M) := Quotient.mk_surjective

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : M ->ₗ[R] SymmetricAlgebra R M
  body: algHom R M ∘ₗ TensorAlgebra.ι R

@[elab_as_elim]

中文:
定义 ι
  签名: : M ->ₗ[R] SymmetricAlgebra R M
  定义体: algHom R M ∘ₗ TensorAlgebra.ι R

@[elab_as_elim]

Depends on / 依赖: TensorAlgebra, algHom
-/
def ι : M ->ₗ[R] SymmetricAlgebra R M := algHom R M ∘ₗ TensorAlgebra.ι R

@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {motive : SymmetricAlgebra R M -> Prop}
  proof: by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

中文:
定理 induction
  结论: {motive : SymmetricAlgebra R M -> 命题}
  证明: by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

Depends on / 依赖: AlgHom, AlgHom.commutes, TensorAlgebra, TensorAlgebra.induction, algHom_surjective, algebraMap, commutes, map_add, map_mul
-/
theorem induction {motive : SymmetricAlgebra R M -> Prop}
    (algebraMap : forall r, motive (algebraMap R (SymmetricAlgebra R M) r)) (ι : forall x, motive (ι R M x))
    (mul : forall a b, motive a -> motive b -> motive (a * b))
    (add : forall a b, motive a -> motive b -> motive (a + b))
    (a : SymmetricAlgebra R M) : motive a := by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

open TensorAlgebra in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring (SymmetricAlgebra R M)
  body: by
    change Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y =>
have := Rin

中文:
实例 :
  签名: 交换半环 (SymmetricAlgebra R M)
  定义体: by
    change Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y =>
have := Rin

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_left, Algebra.commute_algebraMap_right, Commute, RingCon, RingCon.coe_mul, RingCon.le_ringConGen, SymRel, SymRel.mul_comm, SymmetricAlgebra, SymmetricAlgebra.induction, add_left, algebraMap, coe_mul, commute_algebraMap_left, commute_algebraMap_right, commute_iff_eq, ha.add_left, ha.mul_left, hb.mul_right
-/
instance : CommSemiring (SymmetricAlgebra R M) where
  mul_comm a b := by
    change Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y =>
have := RingCon.le_ringConGen (r := SymRel R M) _ _ SymRel.mul_comm y x
        simpa [commute_iff_eq, ι, ← RingCon.coe_mul]
      | mul a b ha hb => exact ha.mul_left hb
      | add a b ha hb => exact ha.add_left hb
    | mul b c hb hc => exact hb.mul_right hc
    | add b c hb hc => exact hb.add_right hc

instance (R M) [CommRing R] [AddCommMonoid M] [Module R M] : CommRing (SymmetricAlgebra R M) where
  __ := (inferInstance : CommSemiring (SymmetricAlgebra R M))
  __ := (inferInstance : Ring (SymmetricAlgebra R M))

variable {R M} {A : Type*} [CommSemiring A] [Algebra R A]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (M ->ₗ[R] A) ≃ (SymmetricAlgebra R M ->ₐ[R] A)
  body: let equiv : (TensorAlgebra R M ->ₐ[R] A) ≃
    {f : TensorAlgebra R M ->ₐ[R] A // TensorAlgebra.symRingCon R M <= RingCon.ker f.toRingHom} :=
      (Equiv.subtypeUnivEquiv fun h _ _ h' => ?_).symm
(TensorAlgebra.lift R).trans equiv.trans RingCon.liftₐEquiv (symRingCon R M)

中文:
定义 lift
  签名: : (M ->ₗ[R] A) ≃ (SymmetricAlgebra R M ->ₐ[R] A)
  定义体: let equiv : (TensorAlgebra R M ->ₐ[R] A) ≃
    {f : TensorAlgebra R M ->ₐ[R] A // TensorAlgebra.symRingCon R M <= RingCon.ker f.toRingHom} :=
      (Equiv.subtypeUnivEquiv fun h _ _ h' => ?_).symm
(TensorAlgebra.lift R).trans equiv.trans RingCon.liftₐEquiv (symRingCon R M)

Depends on / 依赖: Equiv.subtypeUnivEquiv, RingCon, RingCon.ker, RingCon.lift, TensorAlgebra, TensorAlgebra.lift, TensorAlgebra.symRingCon, equiv.trans, f.toRingHom, subtypeUnivEquiv, symRingCon, toRingHom
-/
def lift : (M ->ₗ[R] A) ≃ (SymmetricAlgebra R M ->ₐ[R] A) :=
  let equiv : (TensorAlgebra R M ->ₐ[R] A) ≃
    {f : TensorAlgebra R M ->ₐ[R] A // TensorAlgebra.symRingCon R M <= RingCon.ker f.toRingHom} :=
      (Equiv.subtypeUnivEquiv fun h _ _ h' => ?_).symm
(TensorAlgebra.lift R).trans equiv.trans RingCon.liftₐEquiv (symRingCon R M)
where finally
  refine RingCon.ringConGen_le.2 (fun x y h' => ?_) h'
  induction h' with | mul_comm x y
  rw [RingCon.ker_apply]; rw [map_mul]; rw [map_mul]; rw [mul_comm]

variable (f : M ->ₗ[R] A)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lift_ι_apply` / 引理 `lift_ι_apply`

English:
lemma lift_ι_apply
  given: (a : M)
  statement: lift f (ι R M a) = f a
  proof: by
  simp [lift, ι, algHom, RingCon.liftₐEquiv]

@[simp]

中文:
引理 lift_ι_apply
  条件: (a : M)
  结论: lift f (ι R M a) = f a
  证明: by
  simp [lift, ι, algHom, RingCon.liftₐEquiv]

@[simp]

Depends on / 依赖: RingCon, RingCon.lift, algHom
-/
lemma lift_ι_apply (a : M) : lift f (ι R M a) = f a := by
  simp [lift, ι, algHom, RingCon.liftₐEquiv]

@[simp]
/--
lemma `lift_comp_ι` / 引理 `lift_comp_ι`

English:
lemma lift_comp_ι
  statement: lift f ∘ₗ ι R M = f
  proof: LinearMap.ext lift_ι_apply f

@[ext 1200]

中文:
引理 lift_comp_ι
  结论: lift f ∘ₗ ι R M = f
  证明: LinearMap.ext lift_ι_apply f

@[ext 1200]

Depends on / 依赖: LinearMap, LinearMap.ext
-/
lemma lift_comp_ι : lift f ∘ₗ ι R M = f := LinearMap.ext lift_ι_apply f

@[ext 1200]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {F G : SymmetricAlgebra R M ->ₐ[R] A}
  proof: by
  ext x
  exact congr($h x)

@[simp]

中文:
定理 algHom_ext
  结论: {F G : SymmetricAlgebra R M ->ₐ[R] A}
  证明: by
  ext x
  exact congr($h x)

@[simp]
-/
theorem algHom_ext {F G : SymmetricAlgebra R M ->ₐ[R] A}
    (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M ->ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
/--
lemma `lift_ι` / 引理 `lift_ι`

English:
lemma lift_ι
  statement: lift (ι R M) = .id R (SymmetricAlgebra R M)
  proof: by
  apply algHom_ext
  rw [lift_comp_ι]
  ext
  simp

中文:
引理 lift_ι
  结论: lift (ι R M) = .id R (SymmetricAlgebra R M)
  证明: by
  apply algHom_ext
  rw [lift_comp_ι]
  ext
  simp

Depends on / 依赖: algHom_ext
-/
lemma lift_ι : lift (ι R M) = .id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  rw [lift_comp_ι]
  ext
  simp

/--
Definition of `algebraMapInv` / `algebraMapInv` 的定义

English:
definition algebraMapInv
  signature: : SymmetricAlgebra R M ->ₐ[R] R
  body: lift (0 : M ->ₗ[R] R)

中文:
定义 algebraMapInv
  签名: : SymmetricAlgebra R M ->ₐ[R] R
  定义体: lift (0 : M ->ₗ[R] R)
-/
def algebraMapInv : SymmetricAlgebra R M ->ₐ[R] R :=
  lift (0 : M ->ₗ[R] R)

/--
theorem `algebraMapInv_ι` / 定理 `algebraMapInv_ι`

English:
theorem algebraMapInv_ι
  given: (x : M)
  statement: algebraMapInv (ι R M x) = 0
  proof: lift_ι_apply 0 x

中文:
定理 algebraMapInv_ι
  条件: (x : M)
  结论: algebraMapInv (ι R M x) = 0
  证明: lift_ι_apply 0 x
-/
theorem algebraMapInv_ι (x : M) : algebraMapInv (ι R M x) = 0 := lift_ι_apply 0 x

variable (M)

/--
theorem `algebraMap_leftInverse` / 定理 `algebraMap_leftInverse`

English:
theorem algebraMap_leftInverse
  proof: fun x => by
  simp [algebraMapInv]

@[simp]

中文:
定理 algebraMap_leftInverse
  证明: fun x => by
  simp [algebraMapInv]

@[simp]

Depends on / 依赖: algebraMapInv
-/
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M) := fun x => by
  simp [algebraMapInv]

@[simp]
/--
theorem `algebraMap_inj` / 定理 `algebraMap_inj`

English:
theorem algebraMap_inj
  given: (x y : R)
  proof: (algebraMap_leftInverse M).injective.eq_iff

@[simp]

中文:
定理 algebraMap_inj
  条件: (x y : R)
  证明: (algebraMap_leftInverse M).injective.eq_iff

@[simp]

Depends on / 依赖: algebraMap_leftInverse, eq_iff, injective, injective.eq_iff
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (SymmetricAlgebra R M) x = algebraMap R (SymmetricAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff

@[simp]
/--
theorem `algebraMap_eq_zero_iff` / 定理 `algebraMap_eq_zero_iff`

English:
theorem algebraMap_eq_zero_iff
  given: (x : R)
  statement: algebraMap R (SymmetricAlgebra R M) x = 0 ↔ x = 0
  proof: map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]

中文:
定理 algebraMap_eq_zero_iff
  条件: (x : R)
  结论: algebraMap R (SymmetricAlgebra R M) x = 0 ↔ x = 0
  证明: map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]

Depends on / 依赖: Integrable, Integrable.mono_measure, IntegrableOn, MeasurableSet, Measure, Measure.restrict_mono, VectorMeasure, VectorMeasure.IntegrableOn, algebraMap, algebraMap_leftInverse, injective, le_rfl, map_eq_zero_iff, mono_measure, restrict_mono, restrict_not_measurable, variation_restrict
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]
/--
theorem `algebraMap_eq_one_iff` / 定理 `algebraMap_eq_one_iff`

English:
theorem algebraMap_eq_one_iff
  given: (x : R)
  statement: algebraMap R (SymmetricAlgebra R M) x = 1 ↔ x = 1
  proof: map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

中文:
定理 algebraMap_eq_one_iff
  条件: (x : R)
  结论: algebraMap R (SymmetricAlgebra R M) x = 1 ↔ x = 1
  证明: map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

Depends on / 依赖: Integrable, Integrable.mono_measure, Measure, Measure.restrict_union_le, add_measure, algebraMap, algebraMap_leftInverse, hf.add_measure, injective, map_eq_one_iff, mono_measure, restrict_union_le, variation_restrict, variation_restrict_le
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial (SymmetricAlgebra R M)
  body: (algebraMap_leftInverse M).injective.nontrivial

中文:
实例 [非平凡
  签名: R] : 非平凡 (SymmetricAlgebra R M)
  定义体: (algebraMap_leftInverse M).injective.nontrivial

Depends on / 依赖: algebraMap_leftInverse, injective, injective.nontrivial, nontrivial
-/
instance [Nontrivial R] : Nontrivial (SymmetricAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

end SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] (f : M ->ₗ[R] A)
variable {R} {M}

/--
Definition of `IsSymmetricAlgebra` / `IsSymmetricAlgebra` 的定义

English:
definition IsSymmetricAlgebra
  signature: (f : M ->ₗ[R] A)
  body: Function.Bijective (SymmetricAlgebra.lift f)

中文:
定义 IsSymmetricAlgebra
  签名: (f : M ->ₗ[R] A)
  定义体: Function.Bijective (SymmetricAlgebra.lift f)

Depends on / 依赖: Bijective, Function, Function.Bijective, SymmetricAlgebra, SymmetricAlgebra.lift
-/
def IsSymmetricAlgebra (f : M ->ₗ[R] A) : Prop :=
  Function.Bijective (SymmetricAlgebra.lift f)

/--
theorem `SymmetricAlgebra.isSymmetricAlgebra_ι` / 定理 `SymmetricAlgebra.isSymmetricAlgebra_ι`

English:
theorem SymmetricAlgebra.isSymmetricAlgebra_ι
  statement: IsSymmetricAlgebra (ι R M)
  proof: by
  rw [IsSymmetricAlgebra]; rw [lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

中文:
定理 SymmetricAlgebra.isSymmetricAlgebra_ι
  结论: IsSymmetricAlgebra (ι R M)
  证明: by
  rw [IsSymmetricAlgebra]; rw [lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

Depends on / 依赖: Function, Function.Involutive.bijective, Involutive, IsSymmetricAlgebra, bijective
-/
theorem SymmetricAlgebra.isSymmetricAlgebra_ι : IsSymmetricAlgebra (ι R M) := by
  rw [IsSymmetricAlgebra]; rw [lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

namespace IsSymmetricAlgebra

variable {f : M ->ₗ[R] A} (h : IsSymmetricAlgebra f)

section equiv

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : SymmetricAlgebra R M ≃ₐ[R] A
  body: .ofBijective (SymmetricAlgebra.lift f) h

@[simp]

中文:
定义 equiv
  签名: : SymmetricAlgebra R M ≃ₐ[R] A
  定义体: .ofBijective (SymmetricAlgebra.lift f) h

@[simp]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, SymmetricAlgebra, SymmetricAlgebra.lift, h.mono, integrableOn_univ, ofBijective, subset_univ
-/
noncomputable def equiv : SymmetricAlgebra R M ≃ₐ[R] A :=
  .ofBijective (SymmetricAlgebra.lift f) h

@[simp]
/--
lemma `equiv_apply` / 引理 `equiv_apply`

English:
lemma equiv_apply
  given: (a : SymmetricAlgebra R M)
  statement: h.equiv a = SymmetricAlgebra.lift f a
  proof: rfl

@[simp]

中文:
引理 equiv_apply
  条件: (a : SymmetricAlgebra R M)
  结论: h.equiv a = SymmetricAlgebra.lift f a
  证明: rfl

@[simp]
-/
lemma equiv_apply (a : SymmetricAlgebra R M) : h.equiv a = SymmetricAlgebra.lift f a := rfl

@[simp]
/--
lemma `equiv_toAlgHom` / 引理 `equiv_toAlgHom`

English:
lemma equiv_toAlgHom
  statement: h.equiv = SymmetricAlgebra.lift f
  proof: rfl

@[simp]

中文:
引理 equiv_toAlgHom
  结论: h.equiv = SymmetricAlgebra.lift f
  证明: rfl

@[simp]

Depends on / 依赖: integrable_indicator_iff
-/
lemma equiv_toAlgHom : h.equiv = SymmetricAlgebra.lift f := rfl

@[simp]
/--
lemma `equiv_symm_apply` / 引理 `equiv_symm_apply`

English:
lemma equiv_symm_apply
  given: (a : M)
  statement: h.equiv.symm (f a) = SymmetricAlgebra.ι R M a
  proof: h.equiv.injective (by simp)

@[simp]

中文:
引理 equiv_symm_apply
  条件: (a : M)
  结论: h.equiv.symm (f a) = SymmetricAlgebra.ι R M a
  证明: h.equiv.injective (by simp)

@[simp]

Depends on / 依赖: h.equiv.injective, injective
-/
lemma equiv_symm_apply (a : M) : h.equiv.symm (f a) = SymmetricAlgebra.ι R M a :=
  h.equiv.injective (by simp)

@[simp]
/--
lemma `equiv_symm_comp` / 引理 `equiv_symm_comp`

English:
lemma equiv_symm_comp
  statement: h.equiv.toLinearEquiv.symm ∘ₗ f = SymmetricAlgebra.ι R M
  proof: LinearMap.ext fun x => equiv_symm_apply h x

中文:
引理 equiv_symm_comp
  结论: h.equiv.toLinearEquiv.symm ∘ₗ f = SymmetricAlgebra.ι R M
  证明: LinearMap.ext fun x => equiv_symm_apply h x

Depends on / 依赖: LinearMap, LinearMap.ext, equiv_symm_apply
-/
lemma equiv_symm_comp : h.equiv.toLinearEquiv.symm ∘ₗ f = SymmetricAlgebra.ι R M :=
  LinearMap.ext fun x => equiv_symm_apply h x

/--
lemma `of_equiv` / 引理 `of_equiv`

English:
lemma of_equiv
  statement: (e : SymmetricAlgebra R M ≃ₐ[R] A)
  proof: by
  suffices h : e = SymmetricAlgebra.lift f by
    change Function.Bijective _
    exact h ▸ e.bijective
  ext x
  simpa using congr($he x)

中文:
引理 of_equiv
  结论: (e : SymmetricAlgebra R M ≃ₐ[R] A)
  证明: by
  suffices h : e = SymmetricAlgebra.lift f by
    change Function.Bijective _
    exact h ▸ e.bijective
  ext x
  simpa using congr($he x)

Depends on / 依赖: Bijective, Function, Function.Bijective, SymmetricAlgebra, SymmetricAlgebra.lift, bijective, e.bijective
-/
lemma of_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A)
    (he : (e : SymmetricAlgebra R M ->ₗ[R] A) ∘ₗ SymmetricAlgebra.ι R M = f) :
    IsSymmetricAlgebra f := by
  suffices h : e = SymmetricAlgebra.lift f by
    change Function.Bijective _
    exact h ▸ e.bijective
  ext x
  simpa using congr($he x)

/--
lemma `comp_equiv` / 引理 `comp_equiv`

English:
lemma comp_equiv
  given: (e : SymmetricAlgebra R M ≃ₐ[R] A)
  proof: .of_equiv e rfl

中文:
引理 comp_equiv
  条件: (e : SymmetricAlgebra R M ≃ₐ[R] A)
  证明: .of_equiv e rfl

Depends on / 依赖: of_equiv
-/
lemma comp_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A) :
    IsSymmetricAlgebra (e.toLinearMap ∘ₗ (SymmetricAlgebra.ι R M)) := .of_equiv e rfl

end equiv

section UniversalProperty

variable {A' : Type*} [CommSemiring A'] [Algebra R A'] (g : M ->ₗ[R] A')

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : A ->ₐ[R] A'
  body: (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]

中文:
定义 lift
  签名: : A ->ₐ[R] A'
  定义体: (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]

Depends on / 依赖: SymmetricAlgebra, SymmetricAlgebra.lift, h.equiv.symm
-/
noncomputable def lift : A ->ₐ[R] A' := (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]
/--
lemma `lift_eq` / 引理 `lift_eq`

English:
lemma lift_eq
  given: (a : M)
  statement: h.lift g (f a) = g a
  proof: by simp [lift]

@[simp]

中文:
引理 lift_eq
  条件: (a : M)
  结论: h.lift g (f a) = g a
  证明: by simp [lift]

@[simp]
-/
lemma lift_eq (a : M) : h.lift g (f a) = g a := by simp [lift]

@[simp]
/--
lemma `lift_comp_linearMap` / 引理 `lift_comp_linearMap`

English:
lemma lift_comp_linearMap
  statement: h.lift g ∘ₗ f = g
  proof: LinearMap.ext lift_eq h g

中文:
引理 lift_comp_linearMap
  结论: h.lift g ∘ₗ f = g
  证明: LinearMap.ext lift_eq h g

Depends on / 依赖: LinearMap, LinearMap.ext, lift_eq
-/
lemma lift_comp_linearMap : h.lift g ∘ₗ f = g := LinearMap.ext lift_eq h g

/--
lemma `algHom_ext` / 引理 `algHom_ext`

English:
lemma algHom_ext
  statement: (h : IsSymmetricAlgebra f) {F G : A ->ₐ[R] A'}
  proof: by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simpa using congr($hFG x)

中文:
引理 algHom_ext
  结论: (h : IsSymmetricAlgebra f) {F G : A ->ₐ[R] A'}
  证明: by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simpa using congr($hFG x)

Depends on / 依赖: DFunLike, DFunLike.ext, F.comp, G.comp, LinearMap, LinearMap.ext, SymmetricAlgebra, SymmetricAlgebra.algHom_ext, _iff, algHom_ext, h.equiv.surjective.injective_comp_right, h.equiv.toAlgHom, injective_comp_right, surjective, toAlgHom
-/
lemma algHom_ext (h : IsSymmetricAlgebra f) {F G : A ->ₐ[R] A'}
    (hFG : F ∘ₗ f = (G ∘ₗ f : M ->ₗ[R] A')) : F = G := by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simpa using congr($hFG x)

variable {g} in
/--
lemma `lift_unique` / 引理 `lift_unique`

English:
lemma lift_unique
  given: {F : A ->ₐ[R] A'} (hF : F ∘ₗ f = g)
  statement: F = h.lift g
  proof: h.algHom_ext (by simpa)

中文:
引理 lift_unique
  条件: {F : A ->ₐ[R] A'} (hF : F ∘ₗ f = g)
  结论: F = h.lift g
  证明: h.algHom_ext (by simpa)

Depends on / 依赖: algHom_ext, h.algHom_ext
-/
lemma lift_unique {F : A ->ₐ[R] A'} (hF : F ∘ₗ f = g) : F = h.lift g :=
  h.algHom_ext (by simpa)

end UniversalProperty

include h in
@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {motive : A -> Prop}
  proof: by
  rw [← h.equiv.right_inv a]
  generalize h.equiv.invFun a = y
  change motive (SymmetricAlgebra.lift f y)
  induction y using SymmetricAlgebra.induction with
  | algebraMap r => simpa using algebraMap r
  | ι y => simpa using ι y
  | mul _ _ hx hy => simpa using mul _ _ hx hy
  | add _ _ hx hy =

中文:
定理 induction
  结论: {motive : A -> 命题}
  证明: by
  rw [← h.equiv.right_inv a]
  generalize h.equiv.invFun a = y
  change motive (SymmetricAlgebra.lift f y)
  induction y using SymmetricAlgebra.induction with
  | algebraMap r => simpa using algebraMap r
  | ι y => simpa using ι y
  | mul _ _ hx hy => simpa using mul _ _ hx hy
  | add _ _ hx hy =

Depends on / 依赖: SymmetricAlgebra, SymmetricAlgebra.induction, SymmetricAlgebra.lift, algebraMap, generalize, h.equiv.invFun, h.equiv.right_inv, invFun, motive, right_inv
-/
theorem induction {motive : A -> Prop}
    (algebraMap : forall r, motive ((algebraMap R A) r)) (ι : forall x, motive (f x))
    (mul : forall a b, motive a -> motive b -> motive (a * b))
    (add : forall a b, motive a -> motive b -> motive (a + b))
    (a : A) : motive a := by
  rw [← h.equiv.right_inv a]
  generalize h.equiv.invFun a = y
  change motive (SymmetricAlgebra.lift f y)
  induction y using SymmetricAlgebra.induction with
  | algebraMap r => simpa using algebraMap r
  | ι y => simpa using ι y
  | mul _ _ hx hy => simpa using mul _ _ hx hy
  | add _ _ hx hy => simpa using add _ _ hx hy

end IsSymmetricAlgebra
