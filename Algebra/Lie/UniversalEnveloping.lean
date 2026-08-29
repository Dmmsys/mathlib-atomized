/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Universal enveloping algebra

Given a commutative ring `R` and a Lie algebra `L` over `R`, we construct the universal
enveloping algebra of `L`, together with its universal property.

## Main definitions

  * `UniversalEnvelopingAlgebra`: the universal enveloping algebra, endowed with an
    `R`-algebra structure.
  * `UniversalEnvelopingAlgebra.ι`: the Lie algebra morphism from `L` to its universal
    enveloping algebra.
  * `UniversalEnvelopingAlgebra.lift`: given an associative algebra `A`, together with a Lie
    algebra morphism `f : L →ₗ⁅R⁆ A`, `lift R L f : UniversalEnvelopingAlgebra R L →ₐ[R] A` is the
    unique morphism of algebras through which `f` factors.
  * `UniversalEnvelopingAlgebra.ι_comp_lift`: states that the lift of a morphism is indeed part
    of a factorisation.
  * `UniversalEnvelopingAlgebra.lift_unique`: states that lifts of morphisms are indeed unique.
  * `UniversalEnvelopingAlgebra.hom_ext`: a restatement of `lift_unique` as an extensionality
    lemma.

## Tags

lie algebra, universal enveloping algebra, tensor algebra
-/

@[expose] public section


universe u₁ u₂ u₃

variable (R : Type u₁) (L : Type u₂)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "ιₜ" => TensorAlgebra.ι R

namespace UniversalEnvelopingAlgebra

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: : TensorAlgebra R L -> TensorAlgebra R L -> Prop
  constructors (1):
    - lie_compat: (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)

中文:
归纳类型 Rel
  参数: : TensorAlgebra R L -> TensorAlgebra R L -> 命题
  构造子 (1 个):
    - lie_compat: (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)
-/
inductive Rel : TensorAlgebra R L -> TensorAlgebra R L -> Prop
  | lie_compat (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)

/--
Definition of `ringCon` / `ringCon` 的定义

English:
definition ringCon
  signature: : RingCon (TensorAlgebra R L)
  body: ringConGen (Rel R L)

中文:
定义 ringCon
  签名: : RingCon (TensorAlgebra R L)
  定义体: ringConGen (Rel R L)
-/
@[no_expose] def ringCon : RingCon (TensorAlgebra R L) := ringConGen (Rel R L)

end UniversalEnvelopingAlgebra

/--
Definition of `UniversalEnvelopingAlgebra` / `UniversalEnvelopingAlgebra` 的定义

English:
definition UniversalEnvelopingAlgebra
  body: (UniversalEnvelopingAlgebra.ringCon R L).Quotient
deriving Inhabited, Ring, Algebra R

中文:
定义 UniversalEnvelopingAlgebra
  定义体: (UniversalEnvelopingAlgebra.ringCon R L).Quotient
deriving Inhabited, Ring, Algebra R

Depends on / 依赖: Quotient, UniversalEnvelopingAlgebra, UniversalEnvelopingAlgebra.ringCon, ringCon
-/
def UniversalEnvelopingAlgebra := (UniversalEnvelopingAlgebra.ringCon R L).Quotient
deriving Inhabited, Ring, Algebra R

namespace UniversalEnvelopingAlgebra

/--
Definition of `mkAlgHom` / `mkAlgHom` 的定义

English:
definition mkAlgHom
  signature: : TensorAlgebra R L ->ₐ[R] UniversalEnvelopingAlgebra R L
  body: RingCon.mkₐ R _

中文:
定义 mkAlgHom
  签名: : TensorAlgebra R L ->ₐ[R] UniversalEnvelopingAlgebra R L
  定义体: RingCon.mkₐ R _

Depends on / 依赖: RingCon, RingCon.mk
-/
def mkAlgHom : TensorAlgebra R L ->ₐ[R] UniversalEnvelopingAlgebra R L :=
  RingCon.mkₐ R _

variable {L}
attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false in
/-- The natural Lie algebra morphism from a Lie algebra to its universal enveloping algebra. -/
@[simps!]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : L ->ₗ⁅R⁆ UniversalEnvelopingAlgebra R L
  body: { (mkAlgHom R L).toLinearMap.comp ιₜ with
    map_lie' := fun {x y} => by
      suffices mkAlgHom R L (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) = mkAlgHom R L (ιₜ x * ιₜ y) by
        rw [map_mul] at this; simp [LieRing.of_associative_ring_bracket, ← this]
exact Quotient.sound RingCon.le_ringConGen _ _ (Rel.lie_com

中文:
定义 ι
  签名: : L ->ₗ⁅R⁆ UniversalEnvelopingAlgebra R L
  定义体: { (mkAlgHom R L).toLinearMap.comp ιₜ with
    map_lie' := fun {x y} => by
      suffices mkAlgHom R L (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) = mkAlgHom R L (ιₜ x * ιₜ y) by
        rw [map_mul] at this; simp [LieRing.of_associative_ring_bracket, ← this]
exact Quotient.sound RingCon.le_ringConGen _ _ (Rel.lie_com

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, Quotient, Quotient.sound, Rel.lie_compat, RingCon, RingCon.le_ringConGen, le_ringConGen, lie_compat, map_lie, map_mul, mkAlgHom, of_associative_ring_bracket, toLinearMap, toLinearMap.comp
-/
def ι : L ->ₗ⁅R⁆ UniversalEnvelopingAlgebra R L :=
  { (mkAlgHom R L).toLinearMap.comp ιₜ with
    map_lie' := fun {x y} => by
      suffices mkAlgHom R L (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) = mkAlgHom R L (ιₜ x * ιₜ y) by
        rw [map_mul] at this; simp [LieRing.of_associative_ring_bracket, ← this]
exact Quotient.sound RingCon.le_ringConGen _ _ (Rel.lie_compat x y) }

variable {A : Type u₃} [Ring A] [Algebra R A] (f : L ->ₗ⁅R⁆ A)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (L ->ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L ->ₐ[R] A) where
  body: RingCon.liftₐ _
(TensorAlgebra.lift R (f : L ->ₗ[R] A)) by
        grw [ringCon, RingCon.ringConGen_le]
        intro a b h; induction h
        simp [LieRing.of_associative_ring_bracket]
  invFun F := (F : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R)
  left_inv f := by
    ext
    -- Porting

中文:
定义 lift
  签名: : (L ->ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L ->ₐ[R] A) where
  定义体: RingCon.liftₐ _
(TensorAlgebra.lift R (f : L ->ₗ[R] A)) by
        grw [ringCon, RingCon.ringConGen_le]
        intro a b h; induction h
        simp [LieRing.of_associative_ring_bracket]
  invFun F := (F : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R)
  left_inv f := by
    ext
    -- Porting

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, RingCon, RingCon.lift, RingCon.ringConGen_le, TensorAlgebra, TensorAlgebra.lift, UniversalEnvelopingAlgebra, invFun, left_inv, of_associative_ring_bracket, ringCon, ringConGen_le
-/
def lift : (L ->ₗ⁅R⁆ A) ≃ (UniversalEnvelopingAlgebra R L ->ₐ[R] A) where
  toFun f :=
    RingCon.liftₐ _
(TensorAlgebra.lift R (f : L ->ₗ[R] A)) by
        grw [ringCon, RingCon.ringConGen_le]
        intro a b h; induction h
        simp [LieRing.of_associative_ring_bracket]
  invFun F := (F : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R)
  left_inv f := by
    ext
    -- Porting note: was
    -- simp only [ι, mkAlgHom, TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap,
    -- LinearMap.toFun_eq_coe, LinearMap.coe_comp, LieHom.coe_comp, AlgHom.coe_toLieHom,
    -- LieHom.coe_mk, Function.comp_apply, AlgHom.toLinearMap_apply,
    -- RingQuot.liftAlgHom_mkAlgHom_apply]
    simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
      UniversalEnvelopingAlgebra.ι_apply, mkAlgHom]
    simp [UniversalEnvelopingAlgebra]
  right_inv F := by
    apply RingCon.Quotient.hom_extₐ
    ext
    -- Porting note: was
    -- simp only [ι, mkAlgHom, TensorAlgebra.lift_ι_apply, LieHom.coe_toLinearMap,
    -- LinearMap.toFun_eq_coe, LinearMap.coe_comp, LieHom.toLinearMap_comp,
    -- AlgHom.comp_toLinearMap, Function.comp_apply, AlgHom.toLinearMap_apply,
    -- RingQuot.liftAlgHom_mkAlgHom_apply, AlgHom.coe_toLieHom, LieHom.coe_mk]
    -- extra `rfl` after https://github.com/leanprover/lean4/pull/2644
    simp [mkAlgHom]; rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : UniversalEnvelopingAlgebra R L ->ₐ[R] A)
  proof: rfl

@[simp]

中文:
定理 lift_symm_apply
  条件: (F : UniversalEnvelopingAlgebra R L ->ₐ[R] A)
  证明: rfl

@[simp]
-/
theorem lift_symm_apply (F : UniversalEnvelopingAlgebra R L ->ₐ[R] A) :
    (lift R).symm F = (F : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R) :=
  rfl

@[simp]
/--
theorem `ι_comp_lift` / 定理 `ι_comp_lift`

English:
theorem ι_comp_lift
  statement: lift R f ∘ ι R = f
  proof: funext LieHom.ext_iff.mp (lift R).symm_apply_apply f

中文:
定理 ι_comp_lift
  结论: lift R f ∘ ι R = f
  证明: funext LieHom.ext_iff.mp (lift R).symm_apply_apply f

Depends on / 依赖: LieHom, LieHom.ext_iff.mp, ext_iff, symm_apply_apply
-/
theorem ι_comp_lift : lift R f ∘ ι R = f :=
funext LieHom.ext_iff.mp (lift R).symm_apply_apply f

-- `simp`-normal form is `lift_ι_apply'`.
/--
theorem `lift_ι_apply` / 定理 `lift_ι_apply`

English:
theorem lift_ι_apply
  given: (x : L)
  statement: lift R f (ι R x) = f x
  proof: by
  rw [← Function.comp_apply (f := lift R f) (g := ι R) (x := x)]; rw [ι_comp_lift]

@[simp]

中文:
定理 lift_ι_apply
  条件: (x : L)
  结论: lift R f (ι R x) = f x
  证明: by
  rw [← Function.comp_apply (f := lift R f) (g := ι R) (x := x)]; rw [ι_comp_lift]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply
-/
theorem lift_ι_apply (x : L) : lift R f (ι R x) = f x := by
  rw [← Function.comp_apply (f := lift R f) (g := ι R) (x := x)]; rw [ι_comp_lift]

@[simp]
/--
theorem `lift_ι_apply'` / 定理 `lift_ι_apply'`

English:
theorem lift_ι_apply'
  given: (x : L)
  proof: by
  simpa using lift_ι_apply R f x

中文:
定理 lift_ι_apply'
  条件: (x : L)
  证明: by
  simpa using lift_ι_apply R f x

Depends on / 依赖: Algebra, Algebra.linearMap, IsLocalization, IsLocalization.smul_mk, IsLocalizedModule, IsLocalizedModule.mk, IsLocalizedModule.smul_inj, _cancel, _self, linearMap, smul_inj, smul_mk
-/
theorem lift_ι_apply' (x : L) :
    lift R f ((UniversalEnvelopingAlgebra.mkAlgHom R L) (ιₜ x)) = f x := by
  simpa using lift_ι_apply R f x

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (g : UniversalEnvelopingAlgebra R L ->ₐ[R] A)
  statement: g ∘ ι R = f ↔ g = lift R f
  proof: by
  refine Iff.trans ?_ (lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]

中文:
定理 lift_unique
  条件: (g : UniversalEnvelopingAlgebra R L ->ₐ[R] A)
  结论: g ∘ ι R = f ↔ g = lift R f
  证明: by
  refine Iff.trans ?_ (lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]

Depends on / 依赖: Iff.trans, symm_apply_eq
-/
theorem lift_unique (g : UniversalEnvelopingAlgebra R L ->ₐ[R] A) : g ∘ ι R = f ↔ g = lift R f := by
  refine Iff.trans ?_ (lift R).symm_apply_eq
  constructor <;> · intro h; ext; simp [← h]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : UniversalEnvelopingAlgebra R L ->ₐ[R] A}
  proof: have h' : (lift R).symm g₁ = (lift R).symm g₂ := by simp [h]
  (lift R).symm.injective h'

中文:
定理 hom_ext
  结论: {g₁ g₂ : UniversalEnvelopingAlgebra R L ->ₐ[R] A}
  证明: have h' : (lift R).symm g₁ = (lift R).symm g₂ := by simp [h]
  (lift R).symm.injective h'

Depends on / 依赖: injective, symm.injective
-/
theorem hom_ext {g₁ g₂ : UniversalEnvelopingAlgebra R L ->ₐ[R] A}
    (h :
      (g₁ : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R) =
        (g₂ : UniversalEnvelopingAlgebra R L ->ₗ⁅R⁆ A).comp (ι R)) :
    g₁ = g₂ :=
  have h' : (lift R).symm g₁ = (lift R).symm g₂ := by simp [h]
  (lift R).symm.injective h'

end UniversalEnvelopingAlgebra
