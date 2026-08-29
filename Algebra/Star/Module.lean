/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Module.Rat
public import Mathlib.LinearAlgebra.Prod

/-!
# The star operation, bundled as a star-linear equiv

We define `starLinearEquiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `Algebra.Module.Basic` imported to prove.

## TODO

- Define `starLinearEquiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `IsOp R S` and have an instance `IsOp R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `RingHomInvPair` instances to be able to define the semilinear
  equivalence.
-/

@[expose] public section


section SMulLemmas

variable {R M : Type*}

@[simp]
/--
theorem `star_natCast_smul` / 定理 `star_natCast_smul`

English:
theorem star_natCast_smul
  statement: [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : Nat)
  proof: map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

中文:
定理 star_natCast_smul
  结论: [半环 R] [加法交换幺半群 M] [模 R M] [StarAdd幺半群 M] (n : 自然数)
  证明: map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

Depends on / 依赖: map_natCast_smul, starAddEquiv
-/
theorem star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : Nat)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/--
theorem `star_intCast_smul` / 定理 `star_intCast_smul`

English:
theorem star_intCast_smul
  statement: [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : Int)
  proof: map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

中文:
定理 star_intCast_smul
  结论: [环 R] [加法交换群 M] [模 R M] [StarAdd幺半群 M] (n : 整数)
  证明: map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

Depends on / 依赖: map_intCast_smul, starAddEquiv
-/
theorem star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : Int)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/--
theorem `star_inv_natCast_smul` / 定理 `star_inv_natCast_smul`

English:
theorem star_inv_natCast_smul
  statement: [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
  proof: map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

中文:
定理 star_inv_natCast_smul
  结论: [除半环 R] [加法交换幺半群 M] [模 R M] [StarAdd幺半群 M]
  证明: map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Equation, Equation.map, convert, f.toRingHom, map_baseChange, map_inv_natCast_smul, starAddEquiv, toRingHom, toRingHom_eq_coe
-/
theorem star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : Nat) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/--
theorem `star_inv_intCast_smul` / 定理 `star_inv_intCast_smul`

English:
theorem star_inv_intCast_smul
  statement: [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
  proof: map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

中文:
定理 star_inv_intCast_smul
  结论: [除环 R] [加法交换群 M] [模 R M] [StarAdd幺半群 M]
  证明: map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]

Depends on / 依赖: map_inv_intCast_smul, starAddEquiv
-/
theorem star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : Int) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
/--
theorem `star_ratCast_smul` / 定理 `star_ratCast_smul`

English:
theorem star_ratCast_smul
  statement: [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : Rat)
  proof: map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

中文:
定理 star_ratCast_smul
  结论: [除环 R] [加法交换群 M] [模 R M] [StarAdd幺半群 M] (n : 有理数)
  证明: map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

Depends on / 依赖: map_ratCast_smul, starAddEquiv
-/
theorem star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : Rat)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

/-!
Per the naming convention, these two lemmas call `(q • ·)` `nnrat_smul` and `rat_smul` respectively,
rather than `nnqsmul` and `qsmul` because the latter are reserved to the actions coming from
`DivisionSemiring` and `DivisionRing`. We provide aliases with `nnqsmul` and `qsmul` for
discoverability.
-/

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnqsmul`. -/
@[simp high]
/--
lemma `star_nnrat_smul` / 引理 `star_nnrat_smul`

English:
lemma star_nnrat_smul
  given: [AddCommMonoid R] [StarAddMonoid R] [Module Rat>=0 R] (q : Rat>=0) (x : R)
  proof: map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

中文:
引理 star_nnrat_smul
  条件: [加法交换幺半群 R] [StarAdd幺半群 R] [模 有理数>=0 R] (q : 有理数>=0) (x : R)
  证明: map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

Depends on / 依赖: map_nnrat_smul, starAddEquiv
-/
lemma star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Module Rat>=0 R] (q : Rat>=0) (x : R) :
    star (q • x) = q • star x := map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

/--
lemma `star_rat_smul` / 引理 `star_rat_smul`

English:
lemma star_rat_smul
  given: [AddCommGroup R] [StarAddMonoid R] [Module Rat R] (q : Rat) (x : R)
  proof: map_rat_smul (starAddEquiv : R ≃+ R) _ _

中文:
引理 star_rat_smul
  条件: [加法交换群 R] [StarAdd幺半群 R] [模 有理数 R] (q : 有理数) (x : R)
  证明: map_rat_smul (starAddEquiv : R ≃+ R) _ _
-/
@[simp high] lemma star_rat_smul [AddCommGroup R] [StarAddMonoid R] [Module Rat R] (q : Rat) (x : R) :
    star (q • x) = q • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnrat_smul`. -/
alias star_nnqsmul := star_nnrat_smul

/-- Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one coming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for
discoverability. See `star_rat_smul`. -/
alias star_qsmul := star_rat_smul

/--
Instance `StarAddMonoid.toStarModuleNNRat` / 实例 `StarAddMonoid.toStarModuleNNRat`

English:
instance StarAddMonoid.toStarModuleNNRat
  signature: [AddCommMonoid R] [Module Rat>=0 R] [StarAddMonoid R]
  body: star_nnrat_smul

中文:
实例 StarAdd幺半群.toStarModuleNNRat
  签名: [加法交换幺半群 R] [模 有理数>=0 R] [StarAdd幺半群 R]
  定义体: star_nnrat_smul

Depends on / 依赖: star_nnrat_smul
-/
instance StarAddMonoid.toStarModuleNNRat [AddCommMonoid R] [Module Rat>=0 R] [StarAddMonoid R] :
    StarModule Rat>=0 R where star_smul := star_nnrat_smul

/--
Instance `StarAddMonoid.toStarModuleRat` / 实例 `StarAddMonoid.toStarModuleRat`

English:
instance StarAddMonoid.toStarModuleRat
  signature: [AddCommGroup R] [Module Rat R] [StarAddMonoid R]
  body: star_rat_smul

中文:
实例 StarAdd幺半群.toStarModuleRat
  签名: [加法交换群 R] [模 有理数 R] [StarAdd幺半群 R]
  定义体: star_rat_smul

Depends on / 依赖: star_rat_smul
-/
instance StarAddMonoid.toStarModuleRat [AddCommGroup R] [Module Rat R] [StarAddMonoid R] :
    StarModule Rat R where star_smul := star_rat_smul

end SMulLemmas

section starLinearEquiv

variable (R : Type*) {A : Type*}
  [CommSemiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A] [StarModule R A]

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps! apply]
/--
Definition of `starLinearEquiv` / `starLinearEquiv` 的定义

English:
definition starLinearEquiv
  signature: : A ≃ₗ⋆[R] A where
  body: starAddEquiv
  map_smul' := star_smul

@[simp]

中文:
定义 starLinearEquiv
  签名: : A ≃ₗ⋆[R] A where
  定义体: starAddEquiv
  map_smul' := star_smul

@[simp]

Depends on / 依赖: starAddEquiv
-/
def starLinearEquiv : A ≃ₗ⋆[R] A where
  __ := starAddEquiv
  map_smul' := star_smul

@[simp]
/--
theorem `toAddEquiv_starLinearEquiv` / 定理 `toAddEquiv_starLinearEquiv`

English:
theorem toAddEquiv_starLinearEquiv
  proof: rfl

@[simp]

中文:
定理 toAddEquiv_starLinearEquiv
  证明: rfl

@[simp]
-/
theorem toAddEquiv_starLinearEquiv :
    (starLinearEquiv R : A ≃ₗ⋆[R] A).toAddEquiv = starAddEquiv :=
  rfl

@[simp]
/--
theorem `symm_starLinearEquiv` / 定理 `symm_starLinearEquiv`

English:
theorem symm_starLinearEquiv
  statement: (starLinearEquiv R : A ≃ₗ⋆[R] A).symm = starLinearEquiv R
  proof: rfl

@[deprecated "Use `symm_starLinearEquiv` and `starLinearEquiv_apply` instead"
  (since := "2026-06-03")]

中文:
定理 symm_starLinearEquiv
  结论: (starLinearEquiv R : A ≃ₗ⋆[R] A).symm = starLinearEquiv R
  证明: rfl

@[deprecated "Use `symm_starLinearEquiv` and `starLinearEquiv_apply` instead"
  (since := "2026-06-03")]
-/
theorem symm_starLinearEquiv : (starLinearEquiv R : A ≃ₗ⋆[R] A).symm = starLinearEquiv R :=
  rfl

@[deprecated "Use `symm_starLinearEquiv` and `starLinearEquiv_apply` instead"
  (since := "2026-06-03")]
/--
theorem `starLinearEquiv_symm_apply` / 定理 `starLinearEquiv_symm_apply`

English:
theorem starLinearEquiv_symm_apply
  given: (x : A)
  proof: by
  simp

中文:
定理 starLinearEquiv_symm_apply
  条件: (x : A)
  证明: by
  simp
-/
theorem starLinearEquiv_symm_apply (x : A) :
    (starLinearEquiv R).symm x = starAddEquiv.invFun x := by
  simp

end starLinearEquiv

section SelfSkewAdjoint

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

/--
Definition of `selfAdjoint.submodule` / `selfAdjoint.submodule` 的定义

English:
definition selfAdjoint.submodule
  signature: : Submodule R A
  body: { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }

中文:
定义 selfAdjoint.submodule
  签名: : 子模 R A
  定义体: { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.all, selfAdjoint, smul_mem
-/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }

/--
Definition of `skewAdjoint.submodule` / `skewAdjoint.submodule` 的定义

English:
definition skewAdjoint.submodule
  signature: : Submodule R A
  body: { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

中文:
定义 skewAdjoint.submodule
  签名: : 子模 R A
  定义体: { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

Depends on / 依赖: skewAdjoint, skewAdjoint.smul_mem, smul_mem
-/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

variable {A} [Invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
/--
Definition of `selfAdjointPart` / `selfAdjointPart` 的定义

English:
definition selfAdjointPart
  signature: : A ->ₗ[R] selfAdjoint A where
  body: ⟨(⅟2 : R) • (x + star x), by
      rw [selfAdjoint.mem_iff]; rw [star_smul]; rw [star_trivial]; rw [star_add]; rw [star_star]; rw [add_comm]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟2 * r = r * ⅟2 from Commute.invOf_left <| (

中文:
定义 selfAdjointPart
  签名: : A ->ₗ[R] selfAdjoint A where
  定义体: ⟨(⅟2 : R) • (x + star x), by
      rw [selfAdjoint.mem_iff]; rw [star_smul]; rw [star_trivial]; rw [star_add]; rw [star_star]; rw [add_comm]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟2 * r = r * ⅟2 from Commute.invOf_left <| (

Depends on / 依赖: Commute, Commute.invOf_left, add_add_add_comm, add_comm, cast_commute, invOf_left, map_add, map_smul, mem_iff, mul_smul, selfAdjoint, selfAdjoint.mem_iff, star_add, star_smul, star_star, star_trivial
-/
def selfAdjointPart : A ->ₗ[R] selfAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x + star x), by
      rw [selfAdjoint.mem_iff]; rw [star_smul]; rw [star_trivial]; rw [star_add]; rw [star_star]; rw [add_comm]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟2 * r = r * ⅟2 from Commute.invOf_left <| (2 : Nat).cast_commute r]

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
/--
Definition of `skewAdjointPart` / `skewAdjointPart` 的定义

English:
definition skewAdjointPart
  signature: : A ->ₗ[R] skewAdjoint A where
  body: ⟨(⅟2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [←

中文:
定义 skewAdjointPart
  签名: : A ->ₗ[R] skewAdjoint A where
  定义体: ⟨(⅟2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [←

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_add, Commute, Commute.invOf_right, coe_add, commute_cast, invOf_right, map_add, map_smul, mem_iff, mul_smul, neg_sub, skewAdjoint, skewAdjoint.mem_iff, smul_add, smul_neg, smul_sub, star_add, star_smul, star_star
-/
def skewAdjointPart : A ->ₗ[R] skewAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [← mul_smul, ← smul_sub,
show r * ⅟2 = ⅟2 * r from Commute.invOf_right (2 : Nat).commute_cast r]

/--
theorem `StarModule.selfAdjointPart_add_skewAdjointPart` / 定理 `StarModule.selfAdjointPart_add_skewAdjointPart`

English:
theorem StarModule.selfAdjointPart_add_skewAdjointPart
  given: (x : A)
  proof: by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]

中文:
定理 对合模.selfAdjointPart_add_skewAdjointPart
  条件: (x : A)
  证明: by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]

Depends on / 依赖: add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul, selfAdjointPart_apply_coe, skewAdjointPart_apply_coe, smul_add, smul_sub
-/
theorem StarModule.selfAdjointPart_add_skewAdjointPart (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]

/--
theorem `IsSelfAdjoint.coe_selfAdjointPart_apply` / 定理 `IsSelfAdjoint.coe_selfAdjointPart_apply`

English:
theorem IsSelfAdjoint.coe_selfAdjointPart_apply
  given: {x : A} (hx : IsSelfAdjoint x)
  proof: by
  rw [selfAdjointPart_apply_coe]; rw [hx.star_eq]; rw [smul_add]; rw [invOf_two_smul_add_invOf_two_smul]

中文:
定理 IsSelfAdjoint.coe_selfAdjointPart_apply
  条件: {x : A} (hx : IsSelfAdjoint x)
  证明: by
  rw [selfAdjointPart_apply_coe]; rw [hx.star_eq]; rw [smul_add]; rw [invOf_two_smul_add_invOf_two_smul]

Depends on / 依赖: hx.star_eq, invOf_two_smul_add_invOf_two_smul, selfAdjointPart_apply_coe, smul_add, star_eq
-/
theorem IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    (selfAdjointPart R x : A) = x := by
  rw [selfAdjointPart_apply_coe]; rw [hx.star_eq]; rw [smul_add]; rw [invOf_two_smul_add_invOf_two_smul]

/--
theorem `IsSelfAdjoint.selfAdjointPart_apply` / 定理 `IsSelfAdjoint.selfAdjointPart_apply`

English:
theorem IsSelfAdjoint.selfAdjointPart_apply
  given: {x : A} (hx : IsSelfAdjoint x)
  proof: Subtype.ext (hx.coe_selfAdjointPart_apply R)

@[simp]

中文:
定理 IsSelfAdjoint.selfAdjointPart_apply
  条件: {x : A} (hx : IsSelfAdjoint x)
  证明: Subtype.ext (hx.coe_selfAdjointPart_apply R)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, coe_selfAdjointPart_apply, hx.coe_selfAdjointPart_apply
-/
theorem IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    selfAdjointPart R x = ⟨x, hx⟩ :=
  Subtype.ext (hx.coe_selfAdjointPart_apply R)

@[simp]
/--
theorem `selfAdjointPart_comp_subtype_selfAdjoint` / 定理 `selfAdjointPart_comp_subtype_selfAdjoint`

English:
theorem selfAdjointPart_comp_subtype_selfAdjoint
  proof: LinearMap.ext fun x => x.2.selfAdjointPart_apply R

中文:
定理 selfAdjointPart_comp_subtype_selfAdjoint
  证明: LinearMap.ext fun x => x.2.selfAdjointPart_apply R

Depends on / 依赖: LinearMap, LinearMap.ext, selfAdjointPart_apply
-/
theorem selfAdjointPart_comp_subtype_selfAdjoint :
    (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun x => x.2.selfAdjointPart_apply R

/--
theorem `IsSelfAdjoint.skewAdjointPart_apply` / 定理 `IsSelfAdjoint.skewAdjointPart_apply`

English:
theorem IsSelfAdjoint.skewAdjointPart_apply
  given: {x : A} (hx : IsSelfAdjoint x)
  proof: Subtype.ext by
  rw [skewAdjointPart_apply_coe]; rw [hx.star_eq]; rw [sub_self]; rw [smul_zero]; rw [ZeroMemClass.coe_zero]

@[simp]

中文:
定理 IsSelfAdjoint.skewAdjointPart_apply
  条件: {x : A} (hx : IsSelfAdjoint x)
  证明: Subtype.ext by
  rw [skewAdjointPart_apply_coe]; rw [hx.star_eq]; rw [sub_self]; rw [smul_zero]; rw [ZeroMemClass.coe_zero]

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, ZeroMemClass, ZeroMemClass.coe_zero, coe_zero, hx.star_eq, skewAdjointPart_apply_coe, smul_zero, star_eq, sub_self
-/
theorem IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
skewAdjointPart R x = 0 := Subtype.ext by
  rw [skewAdjointPart_apply_coe]; rw [hx.star_eq]; rw [sub_self]; rw [smul_zero]; rw [ZeroMemClass.coe_zero]

@[simp]
/--
theorem `skewAdjointPart_comp_subtype_selfAdjoint` / 定理 `skewAdjointPart_comp_subtype_selfAdjoint`

English:
theorem skewAdjointPart_comp_subtype_selfAdjoint
  proof: LinearMap.ext fun x => x.2.skewAdjointPart_apply R

@[simp]

中文:
定理 skewAdjointPart_comp_subtype_selfAdjoint
  证明: LinearMap.ext fun x => x.2.skewAdjointPart_apply R

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, skewAdjointPart_apply
-/
theorem skewAdjointPart_comp_subtype_selfAdjoint :
    (skewAdjointPart R).comp (selfAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun x => x.2.skewAdjointPart_apply R

@[simp]
/--
theorem `selfAdjointPart_comp_subtype_skewAdjoint` / 定理 `selfAdjointPart_comp_subtype_skewAdjoint`

English:
theorem selfAdjointPart_comp_subtype_skewAdjoint
  proof: LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by simp [hx]

@[simp]

中文:
定理 selfAdjointPart_comp_subtype_skewAdjoint
  证明: LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by simp [hx]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, Subtype, Subtype.ext
-/
theorem selfAdjointPart_comp_subtype_skewAdjoint :
    (selfAdjointPart R).comp (skewAdjoint.submodule R A).subtype = 0 :=
LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by simp [hx]

@[simp]
/--
theorem `skewAdjointPart_comp_subtype_skewAdjoint` / 定理 `skewAdjointPart_comp_subtype_skewAdjoint`

English:
theorem skewAdjointPart_comp_subtype_skewAdjoint
  proof: LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

中文:
定理 skewAdjointPart_comp_subtype_skewAdjoint
  证明: LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.ext, Submodule, Submodule.subtype_apply, Subtype, Subtype.ext, comp_apply, invOf_two_smul_add_invOf_two_smul, skewAdjointPart_apply_coe, smul_add, sub_neg_eq_add, subtype_apply
-/
theorem skewAdjointPart_comp_subtype_skewAdjoint :
    (skewAdjointPart R).comp (skewAdjoint.submodule R A).subtype = .id :=
LinearMap.ext fun ⟨x, (hx : _ = _)⟩ => Subtype.ext by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

variable (A)

set_option backward.isDefEq.respectTransparency false in
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps!]
/--
Definition of `StarModule.decomposeProdAdjoint` / `StarModule.decomposeProdAdjoint` 的定义

English:
definition StarModule.decomposeProdAdjoint
  signature: : A ≃ₗ[R] selfAdjoint A × skewAdjoint A
  body: by
  refine LinearEquiv.ofLinearMap ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  -- Note: with https://github.com/leanprover

中文:
定义 对合模.decomposeProdAdjoint
  签名: : A ≃ₗ[R] selfAdjoint A × skewAdjoint A
  定义体: by
  refine LinearEquiv.ofLinearMap ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  -- Note: with https://github.com/leanprover

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coprod, LinearMap.ext, StarModule, StarModule.selfAdjointPart_add_skewAdjointPart, coprod, ofLinearMap, selfAdjoint, selfAdjoint.submodule, selfAdjointPart, selfAdjointPart_add_skewAdjointPart, skewAdjoint, skewAdjoint.submodule, skewAdjointPart, submodule, subtype
-/
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A := by
  refine LinearEquiv.ofLinearMap ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  -- Note: with https://github.com/leanprover-community/mathlib4/pull/6965 `Submodule.coe_subtype` doesn't fire in `dsimp` or `simp`
  ext x <;> dsimp <;> erw [Submodule.coe_subtype, Submodule.coe_subtype] <;> simp

end SelfSkewAdjoint

section algebraMap

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]
variable [StarMul A] [Algebra R A] [StarModule R A]

@[simp]
/--
theorem `algebraMap_star_comm` / 定理 `algebraMap_star_comm`

English:
theorem algebraMap_star_comm
  given: (r : R)
  statement: algebraMap R A (star r) = star (algebraMap R A r)
  proof: by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

中文:
定理 algebraMap_star_comm
  条件: (r : R)
  结论: algebraMap R A (star r) = star (algebraMap R A r)
  证明: by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, star_one, star_smul
-/
theorem algebraMap_star_comm (r : R) : algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

variable (A) in
/--
lemma `IsSelfAdjoint.algebraMap` / 引理 `IsSelfAdjoint.algebraMap`

English:
lemma IsSelfAdjoint.algebraMap
  given: {r : R} (hr : IsSelfAdjoint r)
  proof: by
  simpa using! congr(algebraMap R A $(hr.star_eq))

中文:
引理 IsSelfAdjoint.algebraMap
  条件: {r : R} (hr : IsSelfAdjoint r)
  证明: by
  simpa using! congr(algebraMap R A $(hr.star_eq))
-/
protected lemma IsSelfAdjoint.algebraMap {r : R} (hr : IsSelfAdjoint r) :
    IsSelfAdjoint (algebraMap R A r) := by
  simpa using! congr(algebraMap R A $(hr.star_eq))

/--
lemma `isSelfAdjoint_algebraMap_iff` / 引理 `isSelfAdjoint_algebraMap_iff`

English:
lemma isSelfAdjoint_algebraMap_iff
  given: {r : R} (h : Function.Injective (algebraMap R A))
  proof: ⟨fun hr => h algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

中文:
引理 isSelfAdjoint_algebraMap_iff
  条件: {r : R} (h : 函数.单射 (algebraMap R A))
  证明: ⟨fun hr => h algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.algebraMap, algebraMap, algebraMap_star_comm, hr.star_eq, star_eq
-/
lemma isSelfAdjoint_algebraMap_iff {r : R} (h : Function.Injective (algebraMap R A)) :
    IsSelfAdjoint (algebraMap R A r) ↔ IsSelfAdjoint r :=
⟨fun hr => h algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

end algebraMap

/--
theorem `IsIdempotentElem.star_iff` / 定理 `IsIdempotentElem.star_iff`

English:
theorem IsIdempotentElem.star_iff
  given: {R : Type*} [Mul R] [StarMul R] {a : R}
  proof: by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff

中文:
定理 IsIdempotentElem.star_iff
  条件: {R : 类型} [乘法 R] [StarMul R] {a : R}
  证明: by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff

Depends on / 依赖: IsIdempotentElem, star_mul
-/
theorem IsIdempotentElem.star_iff {R : Type*} [Mul R] [StarMul R] {a : R} :
    IsIdempotentElem (star a) ↔ IsIdempotentElem a := by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff
