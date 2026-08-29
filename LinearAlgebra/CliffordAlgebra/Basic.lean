/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song
-/
module

public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Isometry
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic form `Q` is
an `R`-algebra denoted `CliffordAlgebra Q`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebraMap _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism from `CliffordAlgebra Q` to `A`, which is denoted `CliffordAlgebra.lift Q f cond`.

The canonical linear map `M → CliffordAlgebra Q` is denoted `CliffordAlgebra.ι Q`.

## Theorems

The main theorems proved ensure that `CliffordAlgebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `CliffordAlgebra.Rel Q` on `TensorAlgebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.
-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

open TensorAlgebra

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: : TensorAlgebra R M -> TensorAlgebra R M -> Prop
  constructors (1):
    - of: (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))

中文:
归纳类型 Rel
  参数: : TensorAlgebra R M -> TensorAlgebra R M -> 命题
  构造子 (1 个):
    - of: (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))
-/
inductive Rel : TensorAlgebra R M -> TensorAlgebra R M -> Prop
  | of (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))

/--
Definition of `ringCon` / `ringCon` 的定义

English:
definition ringCon
  signature: : RingCon (TensorAlgebra R M)
  body: ringConGen (Rel Q)

中文:
定义 ringCon
  签名: : RingCon (TensorAlgebra R M)
  定义体: ringConGen (Rel Q)
-/
@[no_expose] def ringCon : RingCon (TensorAlgebra R M) := ringConGen (Rel Q)

end CliffordAlgebra

/-- The Clifford algebra of an `R`-module `M` equipped with a `QuadraticForm` `Q`.
-/
@[wikidata Q674689]
.Quotient def CliffordAlgebra := CliffordAlgebra.ringCon Q
deriving Inhabited

namespace CliffordAlgebra

-- This instance exists to avoid nsmul and zsmul diamonds.
instance {R A M} [CommSemiring R] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Module R M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] : SMul R (CliffordAlgebra Q) :=
inferInstanceAs SMul R (RingCon.Quotient _)

deriving instance Ring for CliffordAlgebra

instance (priority := 900) instAlgebra' {R A M} [CommSemiring R] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Module R M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] :
    Algebra R (CliffordAlgebra Q) :=
inferInstanceAs Algebra R (RingCon.Quotient _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (CliffordAlgebra Q)
  body: inferInstance

中文:
实例 :
  签名: Algebra R (CliffordAlgebra Q)
  定义体: inferInstance
-/
instance : Algebra R (CliffordAlgebra Q) := inferInstance

-- verify there are no diamonds
-- but doesn't work at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
example : (Semiring.toNatAlgebra : Algebra Nat (CliffordAlgebra Q)) = instAlgebra' _ := rfl
-- but doesn't work at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
example : (Ring.toIntAlgebra _ : Algebra Int (CliffordAlgebra Q)) = instAlgebra' _ := rfl

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] [IsScalarTower S A M] :
    SMulCommClass R S (CliffordAlgebra Q) :=
  RingCon.instSMulCommClassQuotient _

instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [SMul R S] [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S A] (Q : QuadraticForm A M) :
    IsScalarTower R S (CliffordAlgebra Q) :=
  RingCon.instIsScalarTowerQuotient _

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : M ->ₗ[R] CliffordAlgebra Q
  body: (RingCon.mkₐ R _).toLinearMap.comp (TensorAlgebra.ι R)

中文:
定义 ι
  签名: : M ->ₗ[R] CliffordAlgebra Q
  定义体: (RingCon.mkₐ R _).toLinearMap.comp (TensorAlgebra.ι R)

Depends on / 依赖: RingCon, RingCon.mk, TensorAlgebra, toLinearMap, toLinearMap.comp
-/
def ι : M ->ₗ[R] CliffordAlgebra Q :=
  (RingCon.mkₐ R _).toLinearMap.comp (TensorAlgebra.ι R)

/--
theorem `ι_apply` / 定理 `ι_apply`

English:
theorem ι_apply
  given: (m : M)
  proof: rfl

中文:
定理 ι_apply
  条件: (m : M)
  证明: rfl
-/
private theorem ι_apply (m : M) :
    ι Q m = (TensorAlgebra.ι R m : CliffordAlgebra.ringCon Q |>.Quotient) := rfl

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
/--
theorem `ι_sq_scalar` / 定理 `ι_sq_scalar`

English:
theorem ι_sq_scalar
  given: (m : M)
  statement: ι Q m * ι Q m = algebraMap R _ (Q m)
  proof: Quotient.sound RingCon.le_ringConGen _ _ (Rel.of m)

中文:
定理 ι_sq_scalar
  条件: (m : M)
  结论: ι Q m * ι Q m = algebraMap R _ (Q m)
  证明: Quotient.sound RingCon.le_ringConGen _ _ (Rel.of m)

Depends on / 依赖: Quotient, Quotient.sound, Rel.of, RingCon, RingCon.le_ringConGen, le_ringConGen
-/
theorem ι_sq_scalar (m : M) : ι Q m * ι Q m = algebraMap R _ (Q m) :=
Quotient.sound RingCon.le_ringConGen _ _ (Rel.of m)

variable {Q} {A : Type*} [Semiring A] [Algebra R A]

@[simp]
/--
theorem `comp_ι_sq_scalar` / 定理 `comp_ι_sq_scalar`

English:
theorem comp_ι_sq_scalar
  given: (g : CliffordAlgebra Q ->ₐ[R] A) (m : M)
  proof: by
  rw [← map_mul]; rw [ι_sq_scalar]; rw [AlgHom.commutes]

中文:
定理 comp_ι_sq_scalar
  条件: (g : CliffordAlgebra Q ->ₐ[R] A) (m : M)
  证明: by
  rw [← map_mul]; rw [ι_sq_scalar]; rw [AlgHom.commutes]

Depends on / 依赖: AlgHom, AlgHom.commutes, commutes, map_mul
-/
theorem comp_ι_sq_scalar (g : CliffordAlgebra Q ->ₐ[R] A) (m : M) :
    g (ι Q m) * g (ι Q m) = algebraMap _ _ (Q m) := by
  rw [← map_mul]; rw [ι_sq_scalar]; rw [AlgHom.commutes]

set_option backward.isDefEq.respectTransparency.types false in
variable (Q) in
/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `CliffordAlgebra Q` to `A`.
-/
@[simps symm_apply]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: :
  body: RingCon.liftₐ (CliffordAlgebra.ringCon Q)
      (TensorAlgebra.lift R (f : M ->ₗ[R] A))
      (by
        exact RingCon.ringConGen_le.2 fun x y (h : Rel Q x y) => by
          induction h
          simp [f.prop])
  invFun F :=
    ⟨F.toLinearMap.comp (ι Q), fun m => by
      rw [LinearMap.comp_apply

中文:
定义 lift
  签名: :
  定义体: RingCon.liftₐ (CliffordAlgebra.ringCon Q)
      (TensorAlgebra.lift R (f : M ->ₗ[R] A))
      (by
        exact RingCon.ringConGen_le.2 fun x y (h : Rel Q x y) => by
          induction h
          simp [f.prop])
  invFun F :=
    ⟨F.toLinearMap.comp (ι Q), fun m => by
      rw [LinearMap.comp_apply

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, CliffordAlgebra, CliffordAlgebra.ringCon, F.toLinearMap.comp, LinearMap, LinearMap.comp_apply, LinearMap.ext, Quotient, RingCon, RingCon.Quotient.hom_ext, RingCon.lift, RingCon.ringConGen_le, TensorAlgebra, TensorAlgebra.hom_ext, TensorAlgebra.lift, TensorAlgebra.lift_, comp_apply, f.prop, hom_ext
-/
def lift :
    { f : M ->ₗ[R] A // forall m, f m * f m = algebraMap _ _ (Q m) } ≃ (CliffordAlgebra Q ->ₐ[R] A) where
  toFun f :=
    RingCon.liftₐ (CliffordAlgebra.ringCon Q)
      (TensorAlgebra.lift R (f : M ->ₗ[R] A))
      (by
        exact RingCon.ringConGen_le.2 fun x y (h : Rel Q x y) => by
          induction h
          simp [f.prop])
  invFun F :=
    ⟨F.toLinearMap.comp (ι Q), fun m => by
      rw [LinearMap.comp_apply]; rw [AlgHom.toLinearMap_apply]; rw [comp_ι_sq_scalar]⟩
  left_inv f := by
    ext x
    dsimp
    exact (RingCon.liftₐ_mk _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ x)
  right_inv F :=
RingCon.Quotient.hom_extₐ
TensorAlgebra.hom_ext
        LinearMap.ext fun x => by
          dsimp
          exact (RingCon.liftₐ_mk _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ _)

@[simp]
/--
theorem `ι_comp_lift` / 定理 `ι_comp_lift`

English:
theorem ι_comp_lift
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m))
  proof: Subtype.mk_eq_mk.mp (lift Q).symm_apply_apply ⟨f, cond⟩

@[simp]

中文:
定理 ι_comp_lift
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = algebraMap _ _ (Q m))
  证明: Subtype.mk_eq_mk.mp (lift Q).symm_apply_apply ⟨f, cond⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.mk_eq_mk.mp, mk_eq_mk, symm_apply_apply
-/
theorem ι_comp_lift (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m)) :
    (lift Q ⟨f, cond⟩).toLinearMap.comp (ι Q) = f :=
Subtype.mk_eq_mk.mp (lift Q).symm_apply_apply ⟨f, cond⟩

@[simp]
/--
theorem `lift_ι_apply` / 定理 `lift_ι_apply`

English:
theorem lift_ι_apply
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m)) (x)
  proof: (LinearMap.ext_iff.mp <| ι_comp_lift f cond) x

@[simp]

中文:
定理 lift_ι_apply
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = algebraMap _ _ (Q m)) (x)
  证明: (LinearMap.ext_iff.mp <| ι_comp_lift f cond) x

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff.mp, ext_iff
-/
theorem lift_ι_apply (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m)) (x) :
    lift Q ⟨f, cond⟩ (ι Q x) = f x :=
  (LinearMap.ext_iff.mp <| ι_comp_lift f cond) x

@[simp]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (f : M ->ₗ[R] A) (cond : forall m : M, f m * f m = algebraMap _ _ (Q m))
  proof: by
  convert! (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).symm_apply_eq
  rw [lift_symm_apply]; rw [Subtype.mk_eq_mk]

@[simp]

中文:
定理 lift_unique
  结论: (f : M ->ₗ[R] A) (cond : 对任意 m : M, f m * f m = algebraMap _ _ (Q m))
  证明: by
  convert! (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).symm_apply_eq
  rw [lift_symm_apply]; rw [Subtype.mk_eq_mk]

@[simp]

Depends on / 依赖: CliffordAlgebra, Subtype, Subtype.mk_eq_mk, convert, lift_symm_apply, mk_eq_mk, symm_apply_eq
-/
theorem lift_unique (f : M ->ₗ[R] A) (cond : forall m : M, f m * f m = algebraMap _ _ (Q m))
    (g : CliffordAlgebra Q ->ₐ[R] A) : g.toLinearMap.comp (ι Q) = f ↔ g = lift Q ⟨f, cond⟩ := by
  convert! (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).symm_apply_eq
  rw [lift_symm_apply]; rw [Subtype.mk_eq_mk]

@[simp]
/--
theorem `lift_comp_ι` / 定理 `lift_comp_ι`

English:
theorem lift_comp_ι
  given: (g : CliffordAlgebra Q ->ₐ[R] A)
  proof: by
  exact (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).apply_symm_apply g

中文:
定理 lift_comp_ι
  条件: (g : CliffordAlgebra Q ->ₐ[R] A)
  证明: by
  exact (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).apply_symm_apply g

Depends on / 依赖: CliffordAlgebra, apply_symm_apply
-/
theorem lift_comp_ι (g : CliffordAlgebra Q ->ₐ[R] A) :
    lift Q ⟨g.toLinearMap.comp (ι Q), comp_ι_sq_scalar _⟩ = g := by
  exact (lift Q : _ ≃ (CliffordAlgebra Q ->ₐ[R] A)).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {A : Type*} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q ->ₐ[R] A}
  proof: by
  intro h
  apply (lift Q).symm.injective
  rw [lift_symm_apply]; rw [lift_symm_apply]
  simp only [h]

中文:
定理 hom_ext
  条件: {A : 类型} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q ->ₐ[R] A}
  证明: by
  intro h
  apply (lift Q).symm.injective
  rw [lift_symm_apply]; rw [lift_symm_apply]
  simp only [h]

Depends on / 依赖: injective, lift_symm_apply, symm.injective
-/
theorem hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q ->ₐ[R] A} :
    f.toLinearMap.comp (ι Q) = g.toLinearMap.comp (ι Q) -> f = g := by
  intro h
  apply (lift Q).symm.injective
  rw [lift_symm_apply]; rw [lift_symm_apply]
  simp only [h]

-- TODO: fix non-terminal simp (related to the porting note)
set_option linter.flexible false in
-- This proof closely follows `TensorAlgebra.induction`
/-- If `C` holds for the `algebraMap` of `r : R` into `CliffordAlgebra Q`, the `ι` of `x : M`,
and is preserved under addition and multiplication, then it holds for all of `CliffordAlgebra Q`.

See also the stronger `CliffordAlgebra.left_induction` and `CliffordAlgebra.right_induction`.
-/
@[elab_as_elim]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {C : CliffordAlgebra Q -> Prop}
  proof: by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (CliffordAlgebra Q) :=
    { carrier := {a | C a}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let of : { f : M ->ₗ[R] s // forall m, f m * f m = A

中文:
定理 induction
  结论: {C : CliffordAlgebra Q -> 命题}
  证明: by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (CliffordAlgebra Q) :=
    { carrier := {a | C a}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let of : { f : M ->ₗ[R] s // forall m, f m * f m = A
-/
theorem induction {C : CliffordAlgebra Q -> Prop}
    (algebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι Q x))
    (mul : forall a b, C a -> C b -> C (a * b)) (add : forall a b, C a -> C b -> C (a + b))
    (a : CliffordAlgebra Q) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (CliffordAlgebra Q) :=
    { carrier := {a | C a}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let of : { f : M ->ₗ[R] s // forall m, f m * f m = Algebra.algebraMap _ _ (Q m) } :=
    ⟨(CliffordAlgebra.ι Q).codRestrict (Subalgebra.toSubmodule s) ι,
fun m => Subtype.ext ι_sq_scalar Q m⟩
  -- the mapping through the subalgebra is the identity
  have of_id : s.val.comp (lift Q of) = AlgHom.id R (CliffordAlgebra Q) := by
    ext x
    simpa [of, -LinearMap.codRestrict_apply]
      -- This `@[simp]` lemma applies to `coeSort s.subModule`, but the goal contains
      -- a plain `coeSort s`. So we remove it from the `simp` arguments, and add it to
      -- the term that `simpa` will simplify before applying.
      using LinearMap.codRestrict_apply s.toSubmodule (CliffordAlgebra.ι Q) x (h := ι)
  -- finding a proof is finding an element of the subalgebra
  rw [← AlgHom.id_apply (R := R) a]; rw [← of_id]
  exact (lift Q of a).prop

@[simp]
/--
theorem `adjoin_range_ι` / 定理 `adjoin_range_ι`

English:
theorem adjoin_range_ι
  statement: Algebra.adjoin R (Set.range (ι Q)) = ⊤
  proof: by
  refine top_unique fun x hx => ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | add x y hx hy => exact add_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)

@[simp]

中文:
定理 adjoin_range_ι
  结论: Algebra.adjoin R (Set.range (ι Q)) = ⊤
  证明: by
  refine top_unique fun x hx => ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | add x y hx hy => exact add_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)

@[simp]

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Set.mem_range_self, add_mem, algebraMap, algebraMap_mem, mem_range_self, mul_mem, subset_adjoin, top_unique
-/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι Q)) = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | add x y hx hy => exact add_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)

@[simp]
/--
theorem `range_lift` / 定理 `range_lift`

English:
theorem range_lift
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m))
  proof: by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

中文:
定理 range_lift
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = algebraMap _ _ (Q m))
  证明: by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.map_top, Function, Function.comp_def, Set.range_comp, comp_def, map_adjoin, map_top, range_comp, simp_rw
-/
theorem range_lift (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m)) :
    (lift Q ⟨f, cond⟩).range = Algebra.adjoin R (Set.range f) := by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]

/--
theorem `mul_add_swap_eq_polar_of_forall_mul_self_eq` / 定理 `mul_add_swap_eq_polar_of_forall_mul_self_eq`

English:
theorem mul_add_swap_eq_polar_of_forall_mul_self_eq
  statement: {A : Type*} [Ring A] [Algebra R A]
  proof: calc
    f a * f b + f b * f a = f (a + b) * f (a + b) - f a * f a - f b * f b := by
      rw [f.map_add]; rw [mul_add]; rw [add_mul]; rw [add_mul]; abel
    _ = algebraMap R _ (Q (a + b)) - algebraMap R _ (Q a) - algebraMap R _ (Q b) := by
      rw [hf]; rw [hf]; rw [hf]
    _ = algebraMap R _ (Q (

中文:
定理 mul_add_swap_eq_polar_of_forall_mul_self_eq
  结论: {A : 类型} [Ring A] [Algebra R A]
  证明: calc
    f a * f b + f b * f a = f (a + b) * f (a + b) - f a * f a - f b * f b := by
      rw [f.map_add]; rw [mul_add]; rw [add_mul]; rw [add_mul]; abel
    _ = algebraMap R _ (Q (a + b)) - algebraMap R _ (Q a) - algebraMap R _ (Q b) := by
      rw [hf]; rw [hf]; rw [hf]
    _ = algebraMap R _ (Q (

Depends on / 依赖: QuadraticMap, QuadraticMap.polar, add_mul, algebraMap, f.map_add, map_add, map_sub, mul_add
-/
theorem mul_add_swap_eq_polar_of_forall_mul_self_eq {A : Type*} [Ring A] [Algebra R A]
    (f : M ->ₗ[R] A) (hf : forall x, f x * f x = algebraMap _ _ (Q x)) (a b : M) :
    f a * f b + f b * f a = algebraMap R _ (QuadraticMap.polar Q a b) :=
  calc
    f a * f b + f b * f a = f (a + b) * f (a + b) - f a * f a - f b * f b := by
      rw [f.map_add]; rw [mul_add]; rw [add_mul]; rw [add_mul]; abel
    _ = algebraMap R _ (Q (a + b)) - algebraMap R _ (Q a) - algebraMap R _ (Q b) := by
      rw [hf]; rw [hf]; rw [hf]
    _ = algebraMap R _ (Q (a + b) - Q a - Q b) := by rw [← map_sub, ← map_sub]
    _ = algebraMap R _ (QuadraticMap.polar Q a b) := rfl

/--
theorem `forall_mul_self_eq_iff` / 定理 `forall_mul_self_eq_iff`

English:
theorem forall_mul_self_eq_iff
  statement: {A : Type*} [Ring A] [Algebra R A] (h2 : IsUnit (2 : A))
  proof: by
  simp_rw [DFunLike.ext_iff]
  refine ⟨mul_add_swap_eq_polar_of_forall_mul_self_eq _, fun h x => ?_⟩
  change forall x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) at h
  apply h2.mul_left_cancel
  rw [two_mul]; rw [two_mul]; rw [h x x]; rw [QuadraticMap.polar_self]; r

中文:
定理 forall_mul_self_eq_iff
  结论: {A : 类型} [Ring A] [Algebra R A] (h2 : IsUnit (2 : A))
  证明: by
  simp_rw [DFunLike.ext_iff]
  refine ⟨mul_add_swap_eq_polar_of_forall_mul_self_eq _, fun h x => ?_⟩
  change forall x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) at h
  apply h2.mul_left_cancel
  rw [two_mul]; rw [two_mul]; rw [h x x]; rw [QuadraticMap.polar_self]; r

Depends on / 依赖: DFunLike, DFunLike.ext_iff, QuadraticMap, QuadraticMap.polar, QuadraticMap.polar_self, algebraMap, ext_iff, h2.mul_left_cancel, map_add, mul_add_swap_eq_polar_of_forall_mul_self_eq, mul_left_cancel, polar_self, simp_rw, two_mul, two_smul
-/
theorem forall_mul_self_eq_iff {A : Type*} [Ring A] [Algebra R A] (h2 : IsUnit (2 : A))
    (f : M ->ₗ[R] A) :
    (forall x, f x * f x = algebraMap _ _ (Q x)) ↔
      (LinearMap.mul R A).compl₂ f ∘ₗ f + (LinearMap.mul R A).flip.compl₂ f ∘ₗ f =
        Q.polarBilin.compr₂ (Algebra.linearMap R A) := by
  simp_rw [DFunLike.ext_iff]
  refine ⟨mul_add_swap_eq_polar_of_forall_mul_self_eq _, fun h x => ?_⟩
  change forall x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) at h
  apply h2.mul_left_cancel
  rw [two_mul]; rw [two_mul]; rw [h x x]; rw [QuadraticMap.polar_self]; rw [two_smul]; rw [map_add]

/--
theorem `ι_mul_ι_add_swap` / 定理 `ι_mul_ι_add_swap`

English:
theorem ι_mul_ι_add_swap
  given: (a b : M)
  proof: mul_add_swap_eq_polar_of_forall_mul_self_eq _ (ι_sq_scalar _) _ _

中文:
定理 ι_mul_ι_add_swap
  条件: (a b : M)
  证明: mul_add_swap_eq_polar_of_forall_mul_self_eq _ (ι_sq_scalar _) _ _

Depends on / 依赖: mul_add_swap_eq_polar_of_forall_mul_self_eq
-/
theorem ι_mul_ι_add_swap (a b : M) :
    ι Q a * ι Q b + ι Q b * ι Q a = algebraMap R _ (QuadraticMap.polar Q a b) :=
  mul_add_swap_eq_polar_of_forall_mul_self_eq _ (ι_sq_scalar _) _ _

/--
theorem `ι_mul_ι_comm` / 定理 `ι_mul_ι_comm`

English:
theorem ι_mul_ι_comm
  given: (a b : M)
  proof: eq_sub_of_add_eq (ι_mul_ι_add_swap a b)

中文:
定理 ι_mul_ι_comm
  条件: (a b : M)
  证明: eq_sub_of_add_eq (ι_mul_ι_add_swap a b)

Depends on / 依赖: eq_sub_of_add_eq
-/
theorem ι_mul_ι_comm (a b : M) :
    ι Q a * ι Q b = algebraMap R _ (QuadraticMap.polar Q a b) - ι Q b * ι Q a :=
  eq_sub_of_add_eq (ι_mul_ι_add_swap a b)

/--
theorem `mul_ι_mul_ι_mul_comm` / 定理 `mul_ι_mul_ι_mul_comm`

English:
theorem mul_ι_mul_ι_mul_comm
  given: (x : CliffordAlgebra Q) (a b : M) (y : CliffordAlgebra Q)
  proof: by
  rw [mul_assoc]; rw [← mul_assoc _ _ y]; rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_sub]; rw [Algebra.left_comm]; rw [mul_assoc]; rw [mul_assoc]

中文:
定理 mul_ι_mul_ι_mul_comm
  条件: (x : CliffordAlgebra Q) (a b : M) (y : CliffordAlgebra Q)
  证明: by
  rw [mul_assoc]; rw [← mul_assoc _ _ y]; rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_sub]; rw [Algebra.left_comm]; rw [mul_assoc]; rw [mul_assoc]

Depends on / 依赖: Algebra, Algebra.left_comm, left_comm, mul_assoc, mul_sub, sub_mul
-/
theorem mul_ι_mul_ι_mul_comm (x : CliffordAlgebra Q) (a b : M) (y : CliffordAlgebra Q) :
    (x * ι Q a) * (ι Q b * y) =
      algebraMap R _ (QuadraticMap.polar Q a b) * (x * y) - (x * ι Q b) * (ι Q a * y) := by
  rw [mul_assoc]; rw [← mul_assoc _ _ y]; rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_sub]; rw [Algebra.left_comm]; rw [mul_assoc]; rw [mul_assoc]

section isOrtho

/--
theorem `ι_mul_ι_add_swap_of_isOrtho` / 定理 `ι_mul_ι_add_swap_of_isOrtho`

English:
theorem ι_mul_ι_add_swap_of_isOrtho
  given: {a b : M} (h : Q.IsOrtho a b)
  proof: by
  rw [ι_mul_ι_add_swap]; rw [h.polar_eq_zero]
  simp

中文:
定理 ι_mul_ι_add_swap_of_isOrtho
  条件: {a b : M} (h : Q.IsOrtho a b)
  证明: by
  rw [ι_mul_ι_add_swap]; rw [h.polar_eq_zero]
  simp
-/
@[simp] theorem ι_mul_ι_add_swap_of_isOrtho {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * ι Q b + ι Q b * ι Q a = 0 := by
  rw [ι_mul_ι_add_swap]; rw [h.polar_eq_zero]
  simp

/--
theorem `ι_mul_ι_comm_of_isOrtho` / 定理 `ι_mul_ι_comm_of_isOrtho`

English:
theorem ι_mul_ι_comm_of_isOrtho
  given: {a b : M} (h : Q.IsOrtho a b)
  proof: eq_neg_of_add_eq_zero_left ι_mul_ι_add_swap_of_isOrtho h

中文:
定理 ι_mul_ι_comm_of_isOrtho
  条件: {a b : M} (h : Q.IsOrtho a b)
  证明: eq_neg_of_add_eq_zero_left ι_mul_ι_add_swap_of_isOrtho h

Depends on / 依赖: eq_neg_of_add_eq_zero_left
-/
theorem ι_mul_ι_comm_of_isOrtho {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * ι Q b = -(ι Q b * ι Q a) :=
eq_neg_of_add_eq_zero_left ι_mul_ι_add_swap_of_isOrtho h

/--
theorem `mul_ι_mul_ι_of_isOrtho` / 定理 `mul_ι_mul_ι_of_isOrtho`

English:
theorem mul_ι_mul_ι_of_isOrtho
  given: (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b)
  proof: by
  rw [mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [mul_neg]; rw [mul_assoc]

中文:
定理 mul_ι_mul_ι_of_isOrtho
  条件: (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b)
  证明: by
  rw [mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [mul_neg]; rw [mul_assoc]

Depends on / 依赖: mul_assoc, mul_neg
-/
theorem mul_ι_mul_ι_of_isOrtho (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) :
    x * ι Q a * ι Q b = -(x * ι Q b * ι Q a) := by
  rw [mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [mul_neg]; rw [mul_assoc]

/--
theorem `ι_mul_ι_mul_of_isOrtho` / 定理 `ι_mul_ι_mul_of_isOrtho`

English:
theorem ι_mul_ι_mul_of_isOrtho
  given: (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b)
  proof: by
  rw [← mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [neg_mul]; rw [mul_assoc]

中文:
定理 ι_mul_ι_mul_of_isOrtho
  条件: (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b)
  证明: by
  rw [← mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [neg_mul]; rw [mul_assoc]

Depends on / 依赖: mul_assoc, neg_mul
-/
theorem ι_mul_ι_mul_of_isOrtho (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * (ι Q b * x) = -(ι Q b * (ι Q a * x)) := by
  rw [← mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho h]; rw [neg_mul]; rw [mul_assoc]

/--
theorem `mul_ι_mul_ι_mul_comm_of_isOrtho` / 定理 `mul_ι_mul_ι_mul_comm_of_isOrtho`

English:
theorem mul_ι_mul_ι_mul_comm_of_isOrtho
  proof: by
  rw [mul_ι_mul_ι_mul_comm]; rw [h.polar_eq_zero]; rw [map_zero]; rw [zero_mul]; rw [zero_sub]

中文:
定理 mul_ι_mul_ι_mul_comm_of_isOrtho
  证明: by
  rw [mul_ι_mul_ι_mul_comm]; rw [h.polar_eq_zero]; rw [map_zero]; rw [zero_mul]; rw [zero_sub]

Depends on / 依赖: h.polar_eq_zero, map_zero, polar_eq_zero, zero_mul, zero_sub
-/
theorem mul_ι_mul_ι_mul_comm_of_isOrtho
    (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) (y : CliffordAlgebra Q) :
    (x * ι Q a) * (ι Q b * y) = - ((x * ι Q b) * (ι Q a * y)) := by
  rw [mul_ι_mul_ι_mul_comm]; rw [h.polar_eq_zero]; rw [map_zero]; rw [zero_mul]; rw [zero_sub]

end isOrtho

/--
theorem `ι_mul_ι_mul_ι` / 定理 `ι_mul_ι_mul_ι`

English:
theorem ι_mul_ι_mul_ι
  given: (a b : M)
  proof: by
  rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← Algebra.commutes]; rw [←
    Algebra.smul_def]; rw [← map_smul]; rw [← map_smul]; rw [← map_sub]

@[simp]

中文:
定理 ι_mul_ι_mul_ι
  条件: (a b : M)
  证明: by
  rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← Algebra.commutes]; rw [←
    Algebra.smul_def]; rw [← map_smul]; rw [← map_smul]; rw [← map_sub]

@[simp]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, commutes, map_smul, map_sub, mul_assoc, smul_def, sub_mul
-/
theorem ι_mul_ι_mul_ι (a b : M) :
    ι Q a * ι Q b * ι Q a = ι Q (QuadraticMap.polar Q a b • a - Q a • b) := by
  rw [ι_mul_ι_comm]; rw [sub_mul]; rw [mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [← Algebra.commutes]; rw [←
    Algebra.smul_def]; rw [← map_smul]; rw [← map_smul]; rw [← map_sub]

@[simp]
/--
theorem `ι_range_map_lift` / 定理 `ι_range_map_lift`

English:
theorem ι_range_map_lift
  given: (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m))
  proof: by
  rw [← LinearMap.range_comp]; rw [ι_comp_lift]

中文:
定理 ι_range_map_lift
  条件: (f : M ->ₗ[R] A) (cond : 对任意 m, f m * f m = algebraMap _ _ (Q m))
  证明: by
  rw [← LinearMap.range_comp]; rw [ι_comp_lift]

Depends on / 依赖: LinearMap, LinearMap.range_comp, range_comp
-/
theorem ι_range_map_lift (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (Q m)) :
    (LinearMap.range (ι Q)).map (lift Q ⟨f, cond⟩).toLinearMap = LinearMap.range f := by
  rw [← LinearMap.range_comp]; rw [ι_comp_lift]

section Map

variable {M₁ M₂ M₃ : Type*}
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Q₁ ->qᵢ Q₂)
  body: CliffordAlgebra.lift Q₁
⟨ι Q₂ ∘ₗ f.toLinearMap, fun m => (ι_sq_scalar _ _).trans RingHom.congr_arg _ f.map_app m⟩

@[simp]

中文:
定义 map
  签名: (f : Q₁ ->qᵢ Q₂)
  定义体: CliffordAlgebra.lift Q₁
⟨ι Q₂ ∘ₗ f.toLinearMap, fun m => (ι_sq_scalar _ _).trans RingHom.congr_arg _ f.map_app m⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, RingHom, RingHom.congr_arg, congr_arg, f.map_app, f.toLinearMap, map_app, toLinearMap
-/
def map (f : Q₁ ->qᵢ Q₂) :
    CliffordAlgebra Q₁ ->ₐ[R] CliffordAlgebra Q₂ :=
  CliffordAlgebra.lift Q₁
⟨ι Q₂ ∘ₗ f.toLinearMap, fun m => (ι_sq_scalar _ _).trans RingHom.congr_arg _ f.map_app m⟩

@[simp]
/--
theorem `map_comp_ι` / 定理 `map_comp_ι`

English:
theorem map_comp_ι
  given: (f : Q₁ ->qᵢ Q₂)
  proof: ι_comp_lift _ _

@[simp]

中文:
定理 map_comp_ι
  条件: (f : Q₁ ->qᵢ Q₂)
  证明: ι_comp_lift _ _

@[simp]
-/
theorem map_comp_ι (f : Q₁ ->qᵢ Q₂) :
    (map f).toLinearMap ∘ₗ ι Q₁ = ι Q₂ ∘ₗ f.toLinearMap :=
  ι_comp_lift _ _

@[simp]
/--
theorem `map_apply_ι` / 定理 `map_apply_ι`

English:
theorem map_apply_ι
  given: (f : Q₁ ->qᵢ Q₂) (m : M₁)
  statement: map f (ι Q₁ m) = ι Q₂ (f m)
  proof: lift_ι_apply _ _ m

中文:
定理 map_apply_ι
  条件: (f : Q₁ ->qᵢ Q₂) (m : M₁)
  结论: map f (ι Q₁ m) = ι Q₂ (f m)
  证明: lift_ι_apply _ _ m
-/
theorem map_apply_ι (f : Q₁ ->qᵢ Q₂) (m : M₁) : map f (ι Q₁ m) = ι Q₂ (f m) :=
  lift_ι_apply _ _ m

variable (Q₁) in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (QuadraticMap.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra Q₁)
  proof: by
  ext m; exact map_apply_ι _ m

@[simp]

中文:
定理 map_id
  结论: map (QuadraticMap.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra Q₁)
  证明: by
  ext m; exact map_apply_ι _ m

@[simp]
-/
theorem map_id : map (QuadraticMap.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra Q₁) := by
  ext m; exact map_apply_ι _ m

@[simp]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ Q₂)
  proof: by
  ext m
  dsimp only [LinearMap.comp_apply, AlgHom.comp_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [map_apply_ι]; rw [map_apply_ι]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.comp_apply]

@[simp]

中文:
定理 map_comp_map
  条件: (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ Q₂)
  证明: by
  ext m
  dsimp only [LinearMap.comp_apply, AlgHom.comp_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [map_apply_ι]; rw [map_apply_ι]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.comp_apply]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.id_apply, AlgHom.toLinearMap_apply, Isometry, LinearMap, LinearMap.comp_apply, QuadraticMap, QuadraticMap.Isometry.comp_apply, comp_apply, id_apply, toLinearMap_apply
-/
theorem map_comp_map (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ Q₂) :
    (map f).comp (map g) = map (f.comp g) := by
  ext m
  dsimp only [LinearMap.comp_apply, AlgHom.comp_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [map_apply_ι]; rw [map_apply_ι]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.comp_apply]

@[simp]
/--
theorem `ι_range_map_map` / 定理 `ι_range_map_map`

English:
theorem ι_range_map_map
  given: (f : Q₁ ->qᵢ Q₂)
  proof: (ι_range_map_lift _ _).trans (LinearMap.range_comp _ _)

中文:
定理 ι_range_map_map
  条件: (f : Q₁ ->qᵢ Q₂)
  证明: (ι_range_map_lift _ _).trans (LinearMap.range_comp _ _)

Depends on / 依赖: LinearMap, LinearMap.range_comp, range_comp
-/
theorem ι_range_map_map (f : Q₁ ->qᵢ Q₂) :
    (LinearMap.range (ι Q₁)).map (map f).toLinearMap = f.range.map (ι Q₂) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_comp _ _)

open Function in
/--
lemma `leftInverse_map_of_leftInverse` / 引理 `leftInverse_map_of_leftInverse`

English:
lemma leftInverse_map_of_leftInverse
  statement: {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  proof: by
  intro x
  replace h : g.comp f = QuadraticMap.Isometry.id Q₁ := DFunLike.ext _ _ h
  rw [← AlgHom.comp_apply]; rw [map_comp_map]; rw [h]; rw [map_id]; rw [AlgHom.coe_id]; rw [id_eq]

中文:
引理 leftInverse_map_of_leftInverse
  结论: {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  证明: by
  intro x
  replace h : g.comp f = QuadraticMap.Isometry.id Q₁ := DFunLike.ext _ _ h
  rw [← AlgHom.comp_apply]; rw [map_comp_map]; rw [h]; rw [map_id]; rw [AlgHom.coe_id]; rw [id_eq]

Depends on / 依赖: AlgHom, AlgHom.coe_id, AlgHom.comp_apply, DFunLike, DFunLike.ext, Isometry, QuadraticMap, QuadraticMap.Isometry.id, coe_id, comp_apply, g.comp, id_eq, map_comp_map, map_id, replace
-/
lemma leftInverse_map_of_leftInverse {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ ->qᵢ Q₂) (g : Q₂ ->qᵢ Q₁) (h : LeftInverse g f) : LeftInverse (map g) (map f) := by
  intro x
  replace h : g.comp f = QuadraticMap.Isometry.id Q₁ := DFunLike.ext _ _ h
  rw [← AlgHom.comp_apply]; rw [map_comp_map]; rw [h]; rw [map_id]; rw [AlgHom.coe_id]; rw [id_eq]

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  statement: {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁ ->qᵢ Q₂)
  proof: CliffordAlgebra.induction
    (fun r => ⟨algebraMap R (CliffordAlgebra Q₁) r, by simp only [AlgHom.commutes]⟩)
    (fun y => let ⟨x, hx⟩ := hf y; ⟨CliffordAlgebra.ι Q₁ x, by simp only [map_apply_ι, hx]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by simp only [map_mul, hx, hy]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y

中文:
引理 map_surjective
  结论: {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁ ->qᵢ Q₂)
  证明: CliffordAlgebra.induction
    (fun r => ⟨algebraMap R (CliffordAlgebra Q₁) r, by simp only [AlgHom.commutes]⟩)
    (fun y => let ⟨x, hx⟩ := hf y; ⟨CliffordAlgebra.ι Q₁ x, by simp only [map_apply_ι, hx]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by simp only [map_mul, hx, hy]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y

Depends on / 依赖: AlgHom, AlgHom.commutes, CliffordAlgebra, CliffordAlgebra.induction, algebraMap, commutes, map_add, map_mul
-/
lemma map_surjective {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁ ->qᵢ Q₂)
    (hf : Function.Surjective f) : Function.Surjective (CliffordAlgebra.map f) :=
  CliffordAlgebra.induction
    (fun r => ⟨algebraMap R (CliffordAlgebra Q₁) r, by simp only [AlgHom.commutes]⟩)
    (fun y => let ⟨x, hx⟩ := hf y; ⟨CliffordAlgebra.ι Q₁ x, by simp only [map_apply_ι, hx]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by simp only [map_mul, hx, hy]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by simp only [map_add, hx, hy]⟩)

/-- Two `CliffordAlgebra`s are equivalent as algebras if their quadratic forms are
equivalent. -/
@[simps! apply]
/--
Definition of `equivOfIsometry` / `equivOfIsometry` 的定义

English:
definition equivOfIsometry
  signature: (e : Q₁.IsometryEquiv Q₂)
  body: AlgEquiv.ofAlgHom (map e.toIsometry) (map e.symm.toIsometry)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₂ using 2
      ext m
      exact e.toLinearEquiv.apply_symm_apply m)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₁ using 2
      ext m
      exact e.toLinearEquiv.s

中文:
定义 equivOfIsometry
  签名: (e : Q₁.IsometryEquiv Q₂)
  定义体: AlgEquiv.ofAlgHom (map e.toIsometry) (map e.symm.toIsometry)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₂ using 2
      ext m
      exact e.toLinearEquiv.apply_symm_apply m)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₁ using 2
      ext m
      exact e.toLinearEquiv.s

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, apply_symm_apply, convert, e.symm.toIsometry, e.toIsometry, e.toLinearEquiv.apply_symm_apply, e.toLinearEquiv.symm_apply_apply, map_comp_map, map_id, ofAlgHom, symm_apply_apply, toIsometry, toLinearEquiv
-/
def equivOfIsometry (e : Q₁.IsometryEquiv Q₂) : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂ :=
  AlgEquiv.ofAlgHom (map e.toIsometry) (map e.symm.toIsometry)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₂ using 2
      ext m
      exact e.toLinearEquiv.apply_symm_apply m)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₁ using 2
      ext m
      exact e.toLinearEquiv.symm_apply_apply m)

@[simp]
/--
theorem `equivOfIsometry_symm` / 定理 `equivOfIsometry_symm`

English:
theorem equivOfIsometry_symm
  given: (e : Q₁.IsometryEquiv Q₂)
  proof: rfl

@[simp]

中文:
定理 equivOfIsometry_symm
  条件: (e : Q₁.IsometryEquiv Q₂)
  证明: rfl

@[simp]
-/
theorem equivOfIsometry_symm (e : Q₁.IsometryEquiv Q₂) :
    (equivOfIsometry e).symm = equivOfIsometry e.symm :=
  rfl

@[simp]
/--
theorem `equivOfIsometry_trans` / 定理 `equivOfIsometry_trans`

English:
theorem equivOfIsometry_trans
  given: (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃)
  proof: by
  ext x
  exact AlgHom.congr_fun (map_comp_map _ _) x

@[simp]

中文:
定理 equivOfIsometry_trans
  条件: (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃)
  证明: by
  ext x
  exact AlgHom.congr_fun (map_comp_map _ _) x

@[simp]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, map_comp_map
-/
theorem equivOfIsometry_trans (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (equivOfIsometry e₁₂).trans (equivOfIsometry e₂₃) = equivOfIsometry (e₁₂.trans e₂₃) := by
  ext x
  exact AlgHom.congr_fun (map_comp_map _ _) x

@[simp]
/--
theorem `equivOfIsometry_refl` / 定理 `equivOfIsometry_refl`

English:
theorem equivOfIsometry_refl
  proof: by
  ext x
  exact AlgHom.congr_fun (map_id Q₁) x

中文:
定理 equivOfIsometry_refl
  证明: by
  ext x
  exact AlgHom.congr_fun (map_id Q₁) x

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, map_id
-/
theorem equivOfIsometry_refl :
    (equivOfIsometry <| QuadraticMap.IsometryEquiv.refl Q₁) = AlgEquiv.refl := by
  ext x
  exact AlgHom.congr_fun (map_id Q₁) x

end Map

end CliffordAlgebra

namespace TensorAlgebra

variable {Q}

/--
Definition of `toClifford` / `toClifford` 的定义

English:
definition toClifford
  signature: : TensorAlgebra R M ->ₐ[R] CliffordAlgebra Q
  body: TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]

中文:
定义 toClifford
  签名: : TensorAlgebra R M ->ₐ[R] CliffordAlgebra Q
  定义体: TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]

Depends on / 依赖: CliffordAlgebra, TensorAlgebra, TensorAlgebra.lift
-/
def toClifford : TensorAlgebra R M ->ₐ[R] CliffordAlgebra Q :=
  TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]
/--
theorem `toClifford_ι` / 定理 `toClifford_ι`

English:
theorem toClifford_ι
  given: (m : M)
  statement: toClifford (TensorAlgebra.ι R m) = CliffordAlgebra.ι Q m
  proof: by
  simp [toClifford]

中文:
定理 toClifford_ι
  条件: (m : M)
  结论: toClifford (TensorAlgebra.ι R m) = CliffordAlgebra.ι Q m
  证明: by
  simp [toClifford]

Depends on / 依赖: toClifford
-/
theorem toClifford_ι (m : M) : toClifford (TensorAlgebra.ι R m) = CliffordAlgebra.ι Q m := by
  simp [toClifford]

end TensorAlgebra
