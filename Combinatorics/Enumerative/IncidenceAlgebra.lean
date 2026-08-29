/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.

This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.

This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.

The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.

## Main definitions

* `1 : IncidenceAlgebra 𝕜 α` is the delta function, defined analogously to the identity matrix.
* `f * g` is the incidence algebra product, defined analogously to the matrix product.
* `IncidenceAlgebra.zeta` is the zeta function, defined analogously to the upper triangular matrix
  of ones.
* `IncidenceAlgebra.mu` is the inverse of the zeta function.

## Implementation notes

One has to define `mu` as either the left or right inverse of `zeta`. We define it as the left
inverse, and prove it is also a right inverse by defining `mu'` as the right inverse and using that
left and right inverses agree if they exist.

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulas for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.

## References

* [Aigner, *Combinatorial Theory, Chapter IV*][aigner1997]
* [Jacobson, *Basic Algebra I, 8.6*][jacobson1974]
* [Doubilet, Rota, Stanley, *On the foundations of Combinatorial Theory
  VI*][doubilet_rota_stanley_vi]
* [Spiegel, O'Donnell, *Incidence Algebras*][spiegel_odonnell1997]
* [Kung, Rota, Yan, *Combinatorics: The Rota Way, Chapter 3*][kung_rota_yan2009]
-/

@[expose] public section

open Finset OrderDual

variable {F 𝕜 𝕝 𝕞 α β : Type*}

/--
Definition of `IncidenceAlgebra` / `IncidenceAlgebra` 的定义

English:
structure IncidenceAlgebra
  parameters: (𝕜 α : Type*) [Zero 𝕜] [LE α]
  axioms and operations (2):
    - toFun : α -> α -> 𝕜
    - eq_zero_of_not_le'(⦃a b) : α⦄ : ¬a <= b -> toFun a b = 0

中文:
结构 IncidenceAlgebra
  参数: (𝕜 α : 类型) [Zero 𝕜] [LE α]
  公理与运算 (2 个):
    - toFun : α -> α -> 𝕜
    - eq_zero_of_not_le'(⦃a b) : α⦄ : ¬a <= b -> toFun a b = 0
-/
structure IncidenceAlgebra (𝕜 α : Type*) [Zero 𝕜] [LE α] where
  /-- The underlying function of an element of the incidence algebra.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α -> α -> 𝕜
  eq_zero_of_not_le' ⦃a b : α⦄ : ¬a <= b -> toFun a b = 0

namespace IncidenceAlgebra
section Zero
variable [Zero 𝕜] [LE α] {a b : α}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (IncidenceAlgebra 𝕜 α) α (α -> 𝕜) where
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 instFunLike
  签名: : FunLike (IncidenceAlgebra 𝕜 α) α (α -> 𝕜) where
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance instFunLike : FunLike (IncidenceAlgebra 𝕜 α) α (α -> 𝕜) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
lemma `apply_eq_zero_of_not_le` / 引理 `apply_eq_zero_of_not_le`

English:
lemma apply_eq_zero_of_not_le
  given: (h : ¬a <= b) (f : IncidenceAlgebra 𝕜 α)
  statement: f a b = 0
  proof: eq_zero_of_not_le' _ h

中文:
引理 apply_eq_zero_of_not_le
  条件: (h : ¬a <= b) (f : IncidenceAlgebra 𝕜 α)
  结论: f a b = 0
  证明: eq_zero_of_not_le' _ h

Depends on / 依赖: Faithful, IsIso.comp_isIso, LightCondSet, LightCondSet.Loc, LightCondensed, LightCondensed.forget, LightProfinite, Sheaf.isConstant_iff_isIso_counit_app, coherentTopology, comp_isIso, constantSheaf, constantSheafAdj_counit_w, discrete, discreteUnderlyingAdj, eq_zero_of_not_le, essImage, essImage_eq_of_natIso, forget, isConstant_iff_isIso_counit_app
-/
lemma apply_eq_zero_of_not_le (h : ¬a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0 :=
  eq_zero_of_not_le' _ h

/--
lemma `le_of_ne_zero` / 引理 `le_of_ne_zero`

English:
lemma le_of_ne_zero
  given: {f : IncidenceAlgebra 𝕜 α}
  statement: f a b != 0 -> a <= b
  proof: not_imp_comm.1 fun h => apply_eq_zero_of_not_le h _

中文:
引理 le_of_ne_zero
  条件: {f : IncidenceAlgebra 𝕜 α}
  结论: f a b != 0 -> a <= b
  证明: not_imp_comm.1 fun h => apply_eq_zero_of_not_le h _

Depends on / 依赖: apply_eq_zero_of_not_le, not_imp_comm
-/
lemma le_of_ne_zero {f : IncidenceAlgebra 𝕜 α} : f a b != 0 -> a <= b :=
  not_imp_comm.1 fun h => apply_eq_zero_of_not_le h _

section Coes

-- this must come after the `FunLike` instance
initialize_simps_projections IncidenceAlgebra (toFun -> apply)

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : IncidenceAlgebra 𝕜 α)
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (f : IncidenceAlgebra 𝕜 α)
  结论: f.toFun = f
  证明: rfl
-/
@[simp] lemma toFun_eq_coe (f : IncidenceAlgebra 𝕜 α) : f.toFun = f := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : α -> α -> 𝕜) (h)
  statement: (mk f h : α -> α -> 𝕜) = f
  proof: rfl

中文:
引理 coe_mk
  条件: (f : α -> α -> 𝕜) (h)
  结论: (mk f h : α -> α -> 𝕜) = f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mk (f : α -> α -> 𝕜) (h) : (mk f h : α -> α -> 𝕜) = f := rfl

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: {f g : IncidenceAlgebra 𝕜 α}
  statement: (f : α -> α -> 𝕜) = g ↔ f = g
  proof: DFunLike.coe_injective.eq_iff

@[ext]

中文:
引理 coe_inj
  条件: {f g : IncidenceAlgebra 𝕜 α}
  结论: (f : α -> α -> 𝕜) = g ↔ f = g
  证明: DFunLike.coe_injective.eq_iff

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
lemma coe_inj {f g : IncidenceAlgebra 𝕜 α} : (f : α -> α -> 𝕜) = g ↔ f = g :=
  DFunLike.coe_injective.eq_iff

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: ⦃f g
  statement: IncidenceAlgebra 𝕜 α⦄ (h : forall a b, a <= b -> f a b = g a b) : f = g
  proof: by
  refine DFunLike.coe_injective (funext₂ fun a b => ?_)
  by_cases hab : a <= b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]

中文:
引理 ext
  条件: ⦃f g
  结论: IncidenceAlgebra 𝕜 α⦄ (h : 对任意 a b, a <= b -> f a b = g a b) : f = g
  证明: by
  refine DFunLike.coe_injective (funext₂ fun a b => ?_)
  by_cases hab : a <= b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, apply_eq_zero_of_not_le, coe_injective
-/
lemma ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, a <= b -> f a b = g a b) : f = g := by
  refine DFunLike.coe_injective (funext₂ fun a b => ?_)
  by_cases hab : a <= b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]

/--
lemma `mk_coe` / 引理 `mk_coe`

English:
lemma mk_coe
  given: (f : IncidenceAlgebra 𝕜 α) (h)
  statement: mk f h = f
  proof: rfl

中文:
引理 mk_coe
  条件: (f : IncidenceAlgebra 𝕜 α) (h)
  结论: mk f h = f
  证明: rfl
-/
@[simp] lemma mk_coe (f : IncidenceAlgebra 𝕜 α) (h) : mk f h = f := rfl

end Coes


/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (IncidenceAlgebra 𝕜 α)
  body: ⟨⟨fun _ _ => 0, fun _ _ _ => rfl⟩⟩

中文:
实例 instZero
  签名: : Zero (IncidenceAlgebra 𝕜 α)
  定义体: ⟨⟨fun _ _ => 0, fun _ _ _ => rfl⟩⟩
-/
instance instZero : Zero (IncidenceAlgebra 𝕜 α) := ⟨⟨fun _ _ => 0, fun _ _ _ => rfl⟩⟩
/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (IncidenceAlgebra 𝕜 α)
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: : Inhabited (IncidenceAlgebra 𝕜 α)
  定义体: ⟨0⟩
-/
instance instInhabited : Inhabited (IncidenceAlgebra 𝕜 α) := ⟨0⟩

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ⇑(0 : IncidenceAlgebra 𝕜 α) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ⇑(0 : IncidenceAlgebra 𝕜 α) = 0
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : IncidenceAlgebra 𝕜 α) = 0 := rfl
/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (a b : α)
  statement: (0 : IncidenceAlgebra 𝕜 α) a b = 0
  proof: rfl

中文:
引理 zero_apply
  条件: (a b : α)
  结论: (0 : IncidenceAlgebra 𝕜 α) a b = 0
  证明: rfl
-/
lemma zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0 := rfl

end Zero

section Add
variable [AddZeroClass 𝕜] [LE α]

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (IncidenceAlgebra 𝕜 α) where
  body: ⟨f + g, fun a b h => by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩

中文:
实例 instAdd
  签名: : Add (IncidenceAlgebra 𝕜 α) where
  定义体: ⟨f + g, fun a b h => by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩

Depends on / 依赖: Pi.add_apply, add_apply, apply_eq_zero_of_not_le, simp_rw, zero_add
-/
instance instAdd : Add (IncidenceAlgebra 𝕜 α) where
  add f g := ⟨f + g, fun a b h => by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (f g : IncidenceAlgebra 𝕜 α)
  statement: ⇑(f + g) = f + g
  proof: rfl

中文:
引理 coe_add
  条件: (f g : IncidenceAlgebra 𝕜 α)
  结论: ⇑(f + g) = f + g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (f g : IncidenceAlgebra 𝕜 α) : ⇑(f + g) = f + g := rfl
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  statement: (f + g) a b = f a b + g a b
  proof: rfl

中文:
引理 add_apply
  条件: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  结论: (f + g) a b = f a b + g a b
  证明: rfl
-/
lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl

end Add

section Smul
variable {M : Type*} [Zero 𝕜] [LE α] [SMulZeroClass M 𝕜]

/--
Instance `instSmulZeroClassRight` / 实例 `instSmulZeroClassRight`

English:
instance instSmulZeroClassRight
  signature: : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  body: ⟨c • ⇑f, fun a b hab => by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _

中文:
实例 instSmulZeroClassRight
  签名: : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  定义体: ⟨c • ⇑f, fun a b hab => by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _

Depends on / 依赖: Pi.smul_apply, apply_eq_zero_of_not_le, simp_rw, smul_apply, smul_zero
-/
instance instSmulZeroClassRight : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  smul c f :=
    ⟨c • ⇑f, fun a b hab => by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _

/--
lemma `coe_constSMul` / 引理 `coe_constSMul`

English:
lemma coe_constSMul
  given: (c : M) (f : IncidenceAlgebra 𝕜 α)
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

中文:
引理 coe_constSMul
  条件: (c : M) (f : IncidenceAlgebra 𝕜 α)
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_constSMul (c : M) (f : IncidenceAlgebra 𝕜 α) : ⇑(c • f) = c • ⇑f := rfl

/--
lemma `constSMul_apply` / 引理 `constSMul_apply`

English:
lemma constSMul_apply
  given: (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α)
  statement: (c • f) a b = c • f a b
  proof: rfl

中文:
引理 constSMul_apply
  条件: (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α)
  结论: (c • f) a b = c • f a b
  证明: rfl
-/
lemma constSMul_apply (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α) : (c • f) a b = c • f a b := rfl

end Smul

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid 𝕜] [LE α]
  body: DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 instAddMonoid
  签名: [AddMonoid 𝕜] [LE α]
  定义体: DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addMonoid, addMonoid, coe_add, coe_injective, coe_zero
-/
instance instAddMonoid [AddMonoid 𝕜] [LE α] : AddMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid 𝕜] [LE α]
  body: DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 instAddCommMonoid
  签名: [AddCommMonoid 𝕜] [LE α]
  定义体: DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_zero
-/
instance instAddCommMonoid [AddCommMonoid 𝕜] [LE α] : AddCommMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup
variable [AddGroup 𝕜] [LE α]

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (IncidenceAlgebra 𝕜 α) where
  body: ⟨-f, fun a b h => by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩

中文:
实例 instNeg
  签名: : Neg (IncidenceAlgebra 𝕜 α) where
  定义体: ⟨-f, fun a b h => by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩

Depends on / 依赖: Pi.neg_apply, apply_eq_zero_of_not_le, neg_apply, neg_zero, simp_rw
-/
instance instNeg : Neg (IncidenceAlgebra 𝕜 α) where
  neg f := ⟨-f, fun a b h => by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (IncidenceAlgebra 𝕜 α) where
  body: ⟨f - g, fun a b h => by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩

中文:
实例 instSub
  签名: : Sub (IncidenceAlgebra 𝕜 α) where
  定义体: ⟨f - g, fun a b h => by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩

Depends on / 依赖: Pi.sub_apply, apply_eq_zero_of_not_le, simp_rw, sub_apply, sub_zero
-/
instance instSub : Sub (IncidenceAlgebra 𝕜 α) where
  sub f g := ⟨f - g, fun a b h => by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (f : IncidenceAlgebra 𝕜 α)
  statement: ⇑(-f) = -f
  proof: rfl

中文:
引理 coe_neg
  条件: (f : IncidenceAlgebra 𝕜 α)
  结论: ⇑(-f) = -f
  证明: rfl
-/
@[simp, norm_cast] lemma coe_neg (f : IncidenceAlgebra 𝕜 α) : ⇑(-f) = -f := rfl
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (f g : IncidenceAlgebra 𝕜 α)
  statement: ⇑(f - g) = f - g
  proof: rfl

中文:
引理 coe_sub
  条件: (f g : IncidenceAlgebra 𝕜 α)
  结论: ⇑(f - g) = f - g
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sub (f g : IncidenceAlgebra 𝕜 α) : ⇑(f - g) = f - g := rfl
/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: (f : IncidenceAlgebra 𝕜 α) (a b : α)
  statement: (-f) a b = -f a b
  proof: rfl

中文:
引理 neg_apply
  条件: (f : IncidenceAlgebra 𝕜 α) (a b : α)
  结论: (-f) a b = -f a b
  证明: rfl
-/
lemma neg_apply (f : IncidenceAlgebra 𝕜 α) (a b : α) : (-f) a b = -f a b := rfl
/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  statement: (f - g) a b = f a b - g a b
  proof: rfl

中文:
引理 sub_apply
  条件: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  结论: (f - g) a b = f a b - g a b
  证明: rfl
-/
lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: : AddGroup (IncidenceAlgebra 𝕜 α)
  body: DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddGroup
  签名: : AddGroup (IncidenceAlgebra 𝕜 α)
  定义体: DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addGroup, addGroup, coe_add, coe_injective, coe_neg, coe_sub, coe_zero
-/
instance instAddGroup : AddGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup 𝕜] [LE α]
  body: DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 instAddCommGroup
  签名: [AddCommGroup 𝕜] [LE α]
  定义体: DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_sub, coe_zero
-/
instance instAddCommGroup [AddCommGroup 𝕜] [LE α] : AddCommGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

section One
variable [Preorder α] [DecidableEq α] [Zero 𝕜] [One 𝕜]

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (IncidenceAlgebra 𝕜 α)
  body: ⟨⟨fun a b => if a = b then 1 else 0, fun _a _b h => ite_eq_right_iff.2 fun H => (h H.le).elim⟩⟩

中文:
实例 instOne
  签名: : One (IncidenceAlgebra 𝕜 α)
  定义体: ⟨⟨fun a b => if a = b then 1 else 0, fun _a _b h => ite_eq_right_iff.2 fun H => (h H.le).elim⟩⟩

Depends on / 依赖: H.le, ite_eq_right_iff
-/
instance instOne : One (IncidenceAlgebra 𝕜 α) :=
  ⟨⟨fun a b => if a = b then 1 else 0, fun _a _b h => ite_eq_right_iff.2 fun H => (h H.le).elim⟩⟩

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (a b : α)
  statement: (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0
  proof: rfl

中文:
引理 one_apply
  条件: (a b : α)
  结论: (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0
  证明: rfl
-/
@[simp] lemma one_apply (a b : α) : (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end One

section Mul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Mul 𝕜]

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (IncidenceAlgebra 𝕜 α) where
  body: ⟨fun a b => ∑ x in Icc a b, f a x * g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩

中文:
实例 instMul
  签名: : Mul (IncidenceAlgebra 𝕜 α) where
  定义体: ⟨fun a b => ∑ x in Icc a b, f a x * g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩

Depends on / 依赖: Icc_eq_empty, sum_empty
-/
instance instMul : Mul (IncidenceAlgebra 𝕜 α) where
  mul f g :=
    ⟨fun a b => ∑ x in Icc a b, f a x * g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  proof: rfl

中文:
引理 mul_apply
  条件: (f g : IncidenceAlgebra 𝕜 α) (a b : α)
  证明: rfl
-/
@[simp] lemma mul_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) :
    (f * g) a b = ∑ x in Icc a b, f a x * g x b := rfl

end Mul

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [Preorder α] [LocallyFiniteOrder α]
  body: instAddCommMonoid
  zero_mul := fun f => by ext; exact sum_eq_zero fun x _ => zero_mul _
  mul_zero := fun f => by ext; exact sum_eq_zero fun x _ => mul_zero _
  left_distrib := fun f g h => by
    ext; exact Eq.trans (sum_congr rfl fun x _ => left_distrib _ _ _) sum_add_distrib
  right_distrib := f

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [Preorder α] [LocallyFiniteOrder α]
  定义体: instAddCommMonoid
  zero_mul := fun f => by ext; exact sum_eq_zero fun x _ => zero_mul _
  mul_zero := fun f => by ext; exact sum_eq_zero fun x _ => mul_zero _
  left_distrib := fun f g h => by
    ext; exact Eq.trans (sum_congr rfl fun x _ => left_distrib _ _ _) sum_add_distrib
  right_distrib := f

Depends on / 依赖: instAddCommMonoid
-/
instance instNonUnitalNonAssocSemiring [Preorder α] [LocallyFiniteOrder α]
    [NonUnitalNonAssocSemiring 𝕜] : NonUnitalNonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instAddCommMonoid
  zero_mul := fun f => by ext; exact sum_eq_zero fun x _ => zero_mul _
  mul_zero := fun f => by ext; exact sum_eq_zero fun x _ => mul_zero _
  left_distrib := fun f g h => by
    ext; exact Eq.trans (sum_congr rfl fun x _ => left_distrib _ _ _) sum_add_distrib
  right_distrib := fun f g h => by
    ext; exact Eq.trans (sum_congr rfl fun x _ => right_distrib _ _ _) sum_add_distrib

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
  body: instNonUnitalNonAssocSemiring
  one_mul := fun f => by ext; simp [*]
  mul_one := fun f => by ext; simp [*]

中文:
实例 instNonAssocSemiring
  签名: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
  定义体: instNonUnitalNonAssocSemiring
  one_mul := fun f => by ext; simp [*]
  mul_one := fun f => by ext; simp [*]

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
    [NonAssocSemiring 𝕜] : NonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonUnitalNonAssocSemiring
  one_mul := fun f => by ext; simp [*]
  mul_one := fun f => by ext; simp [*]

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜]
  body: instNonAssocSemiring
  mul_assoc f g h := by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;>
      aesop (add simp mul_assoc) (add unsafe le_trans)

中文:
实例 instSemiring
  签名: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜]
  定义体: instNonAssocSemiring
  mul_assoc f g h := by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;>
      aesop (add simp mul_assoc) (add unsafe le_trans)

Depends on / 依赖: instNonAssocSemiring
-/
instance instSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] :
    Semiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonAssocSemiring
  mul_assoc f g h := by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;>
      aesop (add simp mul_assoc) (add unsafe le_trans)

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜]
  body: instSemiring
  __ := instAddGroup

中文:
实例 instRing
  签名: [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜]
  定义体: instSemiring
  __ := instAddGroup

Depends on / 依赖: instSemiring
-/
instance instRing [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜] :
    Ring (IncidenceAlgebra 𝕜 α) where
  __ := instSemiring
  __ := instAddGroup

/-! ### Scalar multiplication between incidence algebras -/

section SMul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [AddCommMonoid 𝕝] [SMul 𝕜 𝕝]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α)
  body: ⟨fun f g =>
    ⟨fun a b => ∑ x in Icc a b, f a x • g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]

中文:
实例 instSMul
  签名: : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α)
  定义体: ⟨fun f g =>
    ⟨fun a b => ∑ x in Icc a b, f a x • g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]

Depends on / 依赖: Icc_eq_empty, X.obj, X.property, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property, sum_empty
-/
instance instSMul : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) :=
  ⟨fun f g =>
    ⟨fun a b => ∑ x in Icc a b, f a x • g x b, fun a b h => by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α)
  proof: rfl

中文:
引理 smul_apply
  条件: (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α)
  证明: rfl
-/
lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
    (f • g) a b = ∑ x in Icc a b, f a x • g x b :=
  rfl

end SMul

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
  body: by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;> aesop (add unsafe le_trans)

中文:
实例 instIsScalarTower
  签名: [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
  定义体: by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;> aesop (add unsafe le_trans)

Depends on / 依赖: le_trans, smul_apply, smul_sum, sum_nbij, sum_sigma, sum_smul, unsafe
-/
instance instIsScalarTower [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
    [Semiring 𝕝] [AddCommMonoid 𝕞] [SMul 𝕜 𝕝] [Module 𝕝 𝕞] [DistribMulAction 𝕜 𝕞]
    [IsScalarTower 𝕜 𝕝 𝕞] :
    IsScalarTower (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) (IncidenceAlgebra 𝕞 α) where
  smul_assoc f g h := by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;> aesop (add unsafe le_trans)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
  body: by ext a b hab; simp [ite_smul, hab]
  mul_smul := smul_assoc
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_e

中文:
实例 [Preorder
  签名: α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
  定义体: by ext a b hab; simp [ite_smul, hab]
  mul_smul := smul_assoc
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_e

Depends on / 依赖: Eq.trans, add_smul, ite_smul, mul_smul, smul_add, smul_assoc, smul_zero, sum_add_distrib, sum_congr, sum_eq_zero, zero_smul
-/
instance [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
    [Module 𝕜 𝕝] : Module (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) where
  one_smul f := by ext a b hab; simp [ite_smul, hab]
  mul_smul := smul_assoc
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ => add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_eq_zero fun x _ => zero_smul _ _
  smul_zero f := by ext; exact sum_eq_zero fun x _ => smul_zero _

/--
Instance `smulWithZeroRight` / 实例 `smulWithZeroRight`

English:
instance smulWithZeroRight
  signature: [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α]
  body: DFunLike.coe_injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩
    coe_constSMul

中文:
实例 smulWithZeroRight
  签名: [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α]
  定义体: DFunLike.coe_injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩
    coe_constSMul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.smulWithZero, IncidenceAlgebra, coe_constSMul, coe_injective, coe_zero, smulWithZero
-/
instance smulWithZeroRight [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α] :
    SMulWithZero 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩
    coe_constSMul

/--
Instance `moduleRight` / 实例 `moduleRight`

English:
instance moduleRight
  signature: [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝]
  body: DFunLike.coe_injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩, coe_add⟩
    coe_constSMul

中文:
实例 moduleRight
  签名: [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝]
  定义体: DFunLike.coe_injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩, coe_add⟩
    coe_constSMul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.module, IncidenceAlgebra, coe_add, coe_constSMul, coe_injective, coe_zero, module
-/
instance moduleRight [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝] :
    Module 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α -> α -> α -> 𝕝), coe_zero⟩, coe_add⟩
    coe_constSMul

/--
Instance `algebraRight` / 实例 `algebraRight`

English:
instance algebraRight
  signature: [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
  body: { toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
    map_one' := by
      ext; simp only [mul_boole, one_apply, smul_eq_mul, constSMul_apply, map_one]
    map_mul' c d := by
        ext a b
        obtain rfl | h := eq_or_ne a b
        · simp only [one_apply, smul_eq_mul, mul_apply, const

中文:
实例 algebraRight
  签名: [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
  定义体: { toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
    map_one' := by
      ext; simp only [mul_boole, one_apply, smul_eq_mul, constSMul_apply, map_one]
    map_mul' c d := by
        ext a b
        obtain rfl | h := eq_or_ne a b
        · simp only [one_apply, smul_eq_mul, mul_apply, const

Depends on / 依赖: Icc_self, IncidenceAlgebra, algebraMap, constSMul_apply, eq_comm, eq_or_ne, if_ne, if_neg, ite_and, ite_mul, map_mul, map_one, mul_apply, mul_boole, mul_ite, mul_one, mul_zero, one_apply, smul_eq_mul, sum_eq_zero
-/
instance algebraRight [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
    [CommSemiring 𝕝] [Algebra 𝕜 𝕝] : Algebra 𝕜 (IncidenceAlgebra 𝕝 α) where
  algebraMap :=
  { toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
    map_one' := by
      ext; simp only [mul_boole, one_apply, smul_eq_mul, constSMul_apply, map_one]
    map_mul' c d := by
        ext a b
        obtain rfl | h := eq_or_ne a b
        · simp only [one_apply, smul_eq_mul, mul_apply, constSMul_apply, map_mul,
            eq_comm, Icc_self]
          simp
        · simp only [one_apply, mul_one, smul_eq_mul, mul_apply, zero_mul,
            constSMul_apply, ← ite_and, ite_mul, mul_ite, map_mul, mul_zero, if_neg h]
          refine (sum_eq_zero fun x _ => ?_).symm
exact if_neg fun hx => h hx.2.trans hx.1
    map_zero' := by rw [map_zero, zero_smul]
    map_add' c d := by rw [map_add, add_smul] }
  commutes' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, mul_comm]
  smul_def' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, Algebra.smul_def]

/-! ### The Lambda function -/

section Lambda
variable (𝕜) [Zero 𝕜] [One 𝕜] [Preorder α] [DecidableRel (α := α) (· ⩿ ·)]

/-- The lambda function of the incidence algebra is the function that assigns `1` to every nonempty
interval of cardinality one or two. -/
@[simps]
/--
Definition of `lambda` / `lambda` 的定义

English:
definition lambda
  signature: : IncidenceAlgebra 𝕜 α
  body: ⟨fun a b => if a ⩿ b then 1 else 0, fun _a _b h => if_neg fun hh => h hh.le⟩

中文:
定义 lambda
  签名: : IncidenceAlgebra 𝕜 α
  定义体: ⟨fun a b => if a ⩿ b then 1 else 0, fun _a _b h => if_neg fun hh => h hh.le⟩

Depends on / 依赖: hh.le, if_neg
-/
def lambda : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b => if a ⩿ b then 1 else 0, fun _a _b h => if_neg fun hh => h hh.le⟩

end Lambda

/-! ### The Zeta and Möbius functions -/

section Zeta
variable (𝕜) [Zero 𝕜] [One 𝕜] [LE α] [DecidableLE α] {a b : α}

/--
Definition of `zeta` / `zeta` 的定义

English:
definition zeta
  signature: : IncidenceAlgebra 𝕜 α
  body: ⟨fun a b => if a <= b then 1 else 0, fun _a _b h => if_neg h⟩

中文:
定义 zeta
  签名: : IncidenceAlgebra 𝕜 α
  定义体: ⟨fun a b => if a <= b then 1 else 0, fun _a _b h => if_neg h⟩

Depends on / 依赖: if_neg
-/
def zeta : IncidenceAlgebra 𝕜 α := ⟨fun a b => if a <= b then 1 else 0, fun _a _b h => if_neg h⟩

variable {𝕜}

/--
lemma `zeta_apply` / 引理 `zeta_apply`

English:
lemma zeta_apply
  given: (a b : α)
  statement: zeta 𝕜 a b = if a <= b then 1 else 0
  proof: rfl

中文:
引理 zeta_apply
  条件: (a b : α)
  结论: zeta 𝕜 a b = if a <= b then 1 else 0
  证明: rfl
-/
@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 a b = if a <= b then 1 else 0 := rfl

/--
lemma `zeta_of_le` / 引理 `zeta_of_le`

English:
lemma zeta_of_le
  given: (h : a <= b)
  statement: zeta 𝕜 a b = 1
  proof: if_pos h

中文:
引理 zeta_of_le
  条件: (h : a <= b)
  结论: zeta 𝕜 a b = 1
  证明: if_pos h

Depends on / 依赖: Functor, Functor.IsRightAdjoint, IsRightAdjoint, LightCondSet, LightCondSet.topCatAdjunction.isRightAdjoint, LightProfinite, LightProfinite.toTopCat, PreservesLimitsOfShape, Profinite, Profinite.toTopCat, if_pos, isRightAdjoint, lightProfiniteToLightCondSetIsoTopCatToLightCondSet, lightProfiniteToLightCondSetIsoTopCatToLightCondSet.symm, lightToProfinite, preservesLimitsOfShape_of_natIso, toTopCat, topCatAdjunction, topCatToLightCondSet
-/
lemma zeta_of_le (h : a <= b) : zeta 𝕜 a b = 1 := if_pos h

end Zeta

/--
lemma `zeta_mul_zeta` / 引理 `zeta_mul_zeta`

English:
lemma zeta_mul_zeta
  statement: [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
  proof: by
  rw [mul_apply]; rw [card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1]; rw [zeta_of_le hx.2]; rw [one_mul]

中文:
引理 zeta_mul_zeta
  结论: [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
  证明: by
  rw [mul_apply]; rw [card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1]; rw [zeta_of_le hx.2]; rw [one_mul]

Depends on / 依赖: Nat.cast_one, Nat.cast_sum, card_eq_sum_ones, cast_one, cast_sum, mem_Icc, mul_apply, one_mul, sum_congr, zeta_of_le
-/
lemma zeta_mul_zeta [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply]; rw [card_eq_sum_ones]; rw [Nat.cast_sum]; rw [Nat.cast_one]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1]; rw [zeta_of_le hx.2]; rw [one_mul]

section Mu
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

set_option backward.privateInPublic true in
/--
Definition of `muFun` / `muFun` 的定义

English:
definition muFun
  signature: (a : α)
  body: mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muFun a x
termination_by b => (Icc a b).card

中文:
定义 muFun
  签名: (a : α)
  定义体: mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muFun a x
termination_by b => (Icc a b).card
-/
private def muFun (a : α) : α -> 𝕜
  | b =>
    if a = b then 1
    else
      -∑ x in (Ico a b).attach,
          let h := mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muFun a x
termination_by b => (Icc a b).card

/--
lemma `muFun_apply` / 引理 `muFun_apply`

English:
lemma muFun_apply
  given: (a b : α)
  proof: by rw [muFun]

中文:
引理 muFun_apply
  条件: (a b : α)
  证明: by rw [muFun]
-/
private lemma muFun_apply (a b : α) :
    muFun 𝕜 a b = if a = b then 1 else -∑ x in (Ico a b).attach, muFun 𝕜 a x := by rw [muFun]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `mu` / `mu` 的定义

English:
definition mu
  signature: : IncidenceAlgebra 𝕜 α
  body: ⟨muFun 𝕜, fun a b => not_imp_comm.1 fun h => by
    rw [muFun_apply] at h
    split_ifs at h with hab
    · exact hab.le
    · rw [neg_eq_zero] at h
      obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
      exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

中文:
定义 mu
  签名: : IncidenceAlgebra 𝕜 α
  定义体: ⟨muFun 𝕜, fun a b => not_imp_comm.1 fun h => by
    rw [muFun_apply] at h
    split_ifs at h with hab
    · exact hab.le
    · rw [neg_eq_zero] at h
      obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
      exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

Depends on / 依赖: exists_ne_zero_of_sum_ne_zero, hab.le, muFun_apply, neg_eq_zero, nonempty_Ico, not_imp_comm, split_ifs
-/
def mu : IncidenceAlgebra 𝕜 α :=
  ⟨muFun 𝕜, fun a b => not_imp_comm.1 fun h => by
    rw [muFun_apply] at h
    split_ifs at h with hab
    · exact hab.le
    · rw [neg_eq_zero] at h
      obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
      exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}

/--
lemma `mu_apply` / 引理 `mu_apply`

English:
lemma mu_apply
  given: (a b : α)
  statement: mu 𝕜 a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜 a x
  proof: by
  rw [mu]; rw [coe_mk]; rw [muFun_apply]; rw [sum_attach]

中文:
引理 mu_apply
  条件: (a b : α)
  结论: mu 𝕜 a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜 a x
  证明: by
  rw [mu]; rw [coe_mk]; rw [muFun_apply]; rw [sum_attach]

Depends on / 依赖: coe_mk, muFun_apply, sum_attach
-/
lemma mu_apply (a b : α) : mu 𝕜 a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜 a x := by
  rw [mu]; rw [coe_mk]; rw [muFun_apply]; rw [sum_attach]

/--
lemma `mu_self` / 引理 `mu_self`

English:
lemma mu_self
  given: (a : α)
  statement: mu 𝕜 a a = 1
  proof: by simp [mu_apply]

中文:
引理 mu_self
  条件: (a : α)
  结论: mu 𝕜 a a = 1
  证明: by simp [mu_apply]
-/
@[simp] lemma mu_self (a : α) : mu 𝕜 a a = 1 := by simp [mu_apply]

/--
lemma `mu_eq_neg_sum_Ico_of_ne` / 引理 `mu_eq_neg_sum_Ico_of_ne`

English:
lemma mu_eq_neg_sum_Ico_of_ne
  given: (hab : a != b)
  proof: by rw [mu_apply, if_neg hab]

中文:
引理 mu_eq_neg_sum_Ico_of_ne
  条件: (hab : a != b)
  证明: by rw [mu_apply, if_neg hab]

Depends on / 依赖: if_neg, mu_apply
-/
lemma mu_eq_neg_sum_Ico_of_ne (hab : a != b) :
    mu 𝕜 a b = -∑ x in Ico a b, mu 𝕜 a x := by rw [mu_apply, if_neg hab]

variable (𝕜 α)
/--
Definition of `eulerChar` / `eulerChar` 的定义

English:
definition eulerChar
  signature: [BoundedOrder α]
  body: mu 𝕜 (⊥ : α) ⊤

中文:
定义 eulerChar
  签名: [BoundedOrder α]
  定义体: mu 𝕜 (⊥ : α) ⊤
-/
def eulerChar [BoundedOrder α] : 𝕜 := mu 𝕜 (⊥ : α) ⊤

end Mu

section MuSpec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

/--
lemma `sum_Icc_mu_right` / 引理 `sum_Icc_mu_right`

English:
lemma sum_Icc_mu_right
  given: (a b : α)
  statement: ∑ x in Icc a b, mu 𝕜 a x = if a = b then 1 else 0
  proof: by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ico hab, mu_eq_neg_sum_Ico_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hax => hab <| hax.trans (mem_Icc.1 hx).2) _

中文:
引理 sum_Icc_mu_right
  条件: (a b : α)
  结论: ∑ x in Icc a b, mu 𝕜 a x = if a = b then 1 else 0
  证明: by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ico hab, mu_eq_neg_sum_Ico_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hax => hab <| hax.trans (mem_Icc.1 hx).2) _

Depends on / 依赖: Icc_eq_cons_Ico, apply_eq_zero_of_not_le, hax.trans, mem_Icc, mu_eq_neg_sum_Ico_of_ne, split_ifs, sum_eq_zero
-/
lemma sum_Icc_mu_right (a b : α) : ∑ x in Icc a b, mu 𝕜 a x = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ico hab, mu_eq_neg_sum_Ico_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hax => hab <| hax.trans (mem_Icc.1 hx).2) _

end MuSpec

section Mu'
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

/--
Definition of `muFun'` / `muFun'` 的定义

English:
definition muFun'
  signature: (b : α)
  body: mem_Ioc.1 x.2
          have : (Icc ↑x b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          muFun' b x
termination_by a => (Icc a b).card

中文:
定义 muFun'
  签名: (b : α)
  定义体: mem_Ioc.1 x.2
          have : (Icc ↑x b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          muFun' b x
termination_by a => (Icc a b).card
-/
private def muFun' (b : α) : α -> 𝕜
  | a =>
    if a = b then 1
    else
      -∑ x in (Ioc a b).attach,
          let h := mem_Ioc.1 x.2
          have : (Icc ↑x b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          muFun' b x
termination_by a => (Icc a b).card

/--
lemma `muFun'_apply` / 引理 `muFun'_apply`

English:
lemma muFun'_apply
  given: (a b : α)
  proof: by
  rw [muFun']

中文:
引理 muFun'_apply
  条件: (a b : α)
  证明: by
  rw [muFun']
-/
private lemma muFun'_apply (a b : α) :
    muFun' 𝕜 b a = if a = b then 1 else -∑ x in (Ioc a b).attach, muFun' 𝕜 b x := by
  rw [muFun']

/--
Definition of `mu'` / `mu'` 的定义

English:
definition mu'
  signature: : IncidenceAlgebra 𝕜 α
  body: ⟨fun a b => muFun' 𝕜 b a, fun a b =>
    not_imp_comm.1 fun h => by
      rw [muFun'_apply] at h
      split_ifs at h with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩

中文:
定义 mu'
  签名: : IncidenceAlgebra 𝕜 α
  定义体: ⟨fun a b => muFun' 𝕜 b a, fun a b =>
    not_imp_comm.1 fun h => by
      rw [muFun'_apply] at h
      split_ifs at h with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩
-/
private def mu' : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b => muFun' 𝕜 b a, fun a b =>
    not_imp_comm.1 fun h => by
      rw [muFun'_apply] at h
      split_ifs at h with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}

/--
lemma `mu'_apply` / 引理 `mu'_apply`

English:
lemma mu'_apply
  given: (a b : α)
  statement: mu' 𝕜 a b = if a = b then 1 else -∑ x in Ioc a b, mu' 𝕜 x b
  proof: by
  rw [mu']; rw [coe_mk]; rw [muFun'_apply]; rw [sum_attach]

中文:
引理 mu'_apply
  条件: (a b : α)
  结论: mu' 𝕜 a b = if a = b then 1 else -∑ x in Ioc a b, mu' 𝕜 x b
  证明: by
  rw [mu']; rw [coe_mk]; rw [muFun'_apply]; rw [sum_attach]
-/
private lemma mu'_apply (a b : α) : mu' 𝕜 a b = if a = b then 1 else -∑ x in Ioc a b, mu' 𝕜 x b := by
  rw [mu']; rw [coe_mk]; rw [muFun'_apply]; rw [sum_attach]

/--
lemma `mu'_apply_self` / 引理 `mu'_apply_self`

English:
lemma mu'_apply_self
  given: (a : α)
  statement: mu' 𝕜 a a = 1
  proof: by simp [mu'_apply]

中文:
引理 mu'_apply_self
  条件: (a : α)
  结论: mu' 𝕜 a a = 1
  证明: by simp [mu'_apply]
-/
@[simp] private lemma mu'_apply_self (a : α) : mu' 𝕜 a a = 1 := by simp [mu'_apply]

/--
lemma `mu'_eq_sum_Ioc_of_ne` / 引理 `mu'_eq_sum_Ioc_of_ne`

English:
lemma mu'_eq_sum_Ioc_of_ne
  given: (h : a != b)
  statement: mu' 𝕜 a b = -∑ x in Ioc a b, mu' 𝕜 x b
  proof: by
  rw [mu'_apply]; rw [if_neg h]

中文:
引理 mu'_eq_sum_Ioc_of_ne
  条件: (h : a != b)
  结论: mu' 𝕜 a b = -∑ x in Ioc a b, mu' 𝕜 x b
  证明: by
  rw [mu'_apply]; rw [if_neg h]
-/
private lemma mu'_eq_sum_Ioc_of_ne (h : a != b) : mu' 𝕜 a b = -∑ x in Ioc a b, mu' 𝕜 x b := by
  rw [mu'_apply]; rw [if_neg h]

end Mu'

section Mu'Spec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

/--
lemma `sum_Icc_mu'_left` / 引理 `sum_Icc_mu'_left`

English:
lemma sum_Icc_mu'_left
  given: (a b : α)
  statement: ∑ x in Icc a b, mu' 𝕜 x b = if a = b then 1 else 0
  proof: by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ioc hab, mu'_eq_sum_Ioc_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hxb => hab <| (mem_Icc.1 hx).1.trans hxb) _

中文:
引理 sum_Icc_mu'_left
  条件: (a b : α)
  结论: ∑ x in Icc a b, mu' 𝕜 x b = if a = b then 1 else 0
  证明: by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ioc hab, mu'_eq_sum_Ioc_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hxb => hab <| (mem_Icc.1 hx).1.trans hxb) _
-/
private lemma sum_Icc_mu'_left (a b : α) : ∑ x in Icc a b, mu' 𝕜 x b = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a <= b
  · simp [Icc_eq_cons_Ioc hab, mu'_eq_sum_Ioc_of_ne ‹_›]
  · exact sum_eq_zero fun x hx => apply_eq_zero_of_not_le
      (fun hxb => hab <| (mem_Icc.1 hx).1.trans hxb) _

end Mu'Spec

section MuZeta
variable (𝕜 α) [AddCommGroup 𝕜] [MulOneClass 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [DecidableEq α] [DecidableLE α]

/--
lemma `mu_mul_zeta` / 引理 `mu_mul_zeta`

English:
lemma mu_mul_zeta
  statement: (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  proof: by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu 𝕜 a x := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).2]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu_right ..

中文:
引理 mu_mul_zeta
  结论: (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  证明: by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu 𝕜 a x := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).2]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu_right ..

Depends on / 依赖: IncidenceAlgebra, mem_Icc, mul_apply, sum_Icc_mu_right
-/
lemma mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu 𝕜 a x := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).2]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu_right ..

/--
lemma `zeta_mul_mu'` / 引理 `zeta_mul_mu'`

English:
lemma zeta_mul_mu'
  statement: (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  proof: by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu' 𝕜 x b := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).1]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu'_left ..

中文:
引理 zeta_mul_mu'
  结论: (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  证明: by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu' 𝕜 x b := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).1]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu'_left ..
-/
private lemma zeta_mul_mu' : (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x in Icc a b, mu' 𝕜 x b := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).1]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu'_left ..

end MuZeta

section MuEqMu'
variable [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/--
lemma `mu_eq_mu'` / 引理 `mu_eq_mu'`

English:
lemma mu_eq_mu'
  statement: (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜
  proof: by
  classical
  exact left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)

中文:
引理 mu_eq_mu'
  结论: (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜
  证明: by
  classical
  exact left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)
-/
private lemma mu_eq_mu' : (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜 := by
  classical
  exact left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)

/--
lemma `mu_eq_neg_sum_Ioc_of_ne` / 引理 `mu_eq_neg_sum_Ioc_of_ne`

English:
lemma mu_eq_neg_sum_Ioc_of_ne
  given: (hab : a != b)
  statement: mu 𝕜 a b = -∑ x in Ioc a b, mu 𝕜 x b
  proof: by
  rw [mu_eq_mu']; rw [mu'_eq_sum_Ioc_of_ne hab]

中文:
引理 mu_eq_neg_sum_Ioc_of_ne
  条件: (hab : a != b)
  结论: mu 𝕜 a b = -∑ x in Ioc a b, mu 𝕜 x b
  证明: by
  rw [mu_eq_mu']; rw [mu'_eq_sum_Ioc_of_ne hab]

Depends on / 依赖: _eq_sum_Ioc_of_ne, mu_eq_mu
-/
lemma mu_eq_neg_sum_Ioc_of_ne (hab : a != b) : mu 𝕜 a b = -∑ x in Ioc a b, mu 𝕜 x b := by
  rw [mu_eq_mu']; rw [mu'_eq_sum_Ioc_of_ne hab]

/--
lemma `zeta_mul_mu` / 引理 `zeta_mul_mu`

English:
lemma zeta_mul_mu
  given: [DecidableLE α]
  statement: (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  proof: by
  rw [mu_eq_mu']; rw [zeta_mul_mu']

中文:
引理 zeta_mul_mu
  条件: [DecidableLE α]
  结论: (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1
  证明: by
  rw [mu_eq_mu']; rw [zeta_mul_mu']

Depends on / 依赖: mu_eq_mu, zeta_mul_mu
-/
lemma zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  rw [mu_eq_mu']; rw [zeta_mul_mu']

/--
lemma `sum_Icc_mu_left` / 引理 `sum_Icc_mu_left`

English:
lemma sum_Icc_mu_left
  given: (a b : α)
  statement: ∑ x in Icc a b, mu 𝕜 x b = if a = b then 1 else 0
  proof: by
  rw [mu_eq_mu']; rw [sum_Icc_mu'_left]

中文:
引理 sum_Icc_mu_left
  条件: (a b : α)
  结论: ∑ x in Icc a b, mu 𝕜 x b = if a = b then 1 else 0
  证明: by
  rw [mu_eq_mu']; rw [sum_Icc_mu'_left]

Depends on / 依赖: _left, mu_eq_mu, sum_Icc_mu
-/
lemma sum_Icc_mu_left (a b : α) : ∑ x in Icc a b, mu 𝕜 x b = if a = b then 1 else 0 := by
  rw [mu_eq_mu']; rw [sum_Icc_mu'_left]

end MuEqMu'

section OrderDual
variable (𝕜) [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

@[simp]
/--
lemma `mu_toDual` / 引理 `mu_toDual`

English:
lemma mu_toDual
  given: (a b : α)
  statement: mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a
  proof: by
  let : DecidableLE α := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b => mu 𝕜 (ofDual b) (ofDual a)
      eq_zero_of_not_le' := fun a b hab => apply_eq_zero_of_not_le (by exact hab) _ }
  suffices mu 𝕜 = mud by simp_rw [this, mud, coe_mk, ofDual_toDual]
  suffic

中文:
引理 mu_toDual
  条件: (a b : α)
  结论: mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a
  证明: by
  let : DecidableLE α := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b => mu 𝕜 (ofDual b) (ofDual a)
      eq_zero_of_not_le' := fun a b hab => apply_eq_zero_of_not_le (by exact hab) _ }
  suffices mu 𝕜 = mud by simp_rw [this, mud, coe_mk, ofDual_toDual]
  suffic

Depends on / 依赖: Classical, Classical.decRel, DecidableLE, IncidenceAlgebra, apply_eq_zero_of_not_le, apply_fun, coe_mk, decRel, eq_zero_of_not_le, mu_mul_zeta, mul_apply, mul_assoc, mul_boole, ofDual, ofDual_toDual, one_apply, simp_rw, zeta_apply, zeta_mul_mu
-/
lemma mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a := by
  let : DecidableLE α := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b => mu 𝕜 (ofDual b) (ofDual a)
      eq_zero_of_not_le' := fun a b hab => apply_eq_zero_of_not_le (by exact hab) _ }
  suffices mu 𝕜 = mud by simp_rw [this, mud, coe_mk, ofDual_toDual]
  suffices mud * zeta 𝕜 = 1 by
    rw [← mu_mul_zeta] at this
    apply_fun (· * mu 𝕜) at this
    symm
    simpa [mul_assoc, zeta_mul_mu] using this
  clear a b
  ext a b
  simp only [mul_boole, one_apply, mul_apply, zeta_apply]
  calc
    ∑ x in Icc a b, (if x <= b then mud a x else 0) = ∑ x in Icc a b, mud a x := by
      congr! with x hx; exact if_pos (mem_Icc.1 hx).2
    _ = ∑ x in Icc (ofDual b) (ofDual a), mu 𝕜 x (ofDual a) := by simp [Icc_orderDual_def, mud]
    _ = if ofDual b = ofDual a then 1 else 0 := sum_Icc_mu_left ..
    _ = if a = b then 1 else 0 := by simp [eq_comm]

/--
lemma `mu_ofDual` / 引理 `mu_ofDual`

English:
lemma mu_ofDual
  given: (a b : αᵒᵈ)
  statement: mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a
  proof: (mu_toDual ..).symm

@[simp]

中文:
引理 mu_ofDual
  条件: (a b : αᵒᵈ)
  结论: mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a
  证明: (mu_toDual ..).symm

@[simp]
-/
@[simp] lemma mu_ofDual (a b : αᵒᵈ) : mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a := (mu_toDual ..).symm

@[simp]
/--
lemma `eulerChar_orderDual` / 引理 `eulerChar_orderDual`

English:
lemma eulerChar_orderDual
  given: [BoundedOrder α]
  statement: eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α
  proof: by
  simp [eulerChar, ← mu_toDual 𝕜 (α := α)]

中文:
引理 eulerChar_orderDual
  条件: [BoundedOrder α]
  结论: eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α
  证明: by
  simp [eulerChar, ← mu_toDual 𝕜 (α := α)]

Depends on / 依赖: eulerChar, mu_toDual
-/
lemma eulerChar_orderDual [BoundedOrder α] : eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α := by
  simp [eulerChar, ← mu_toDual 𝕜 (α := α)]

end OrderDual

section InversionTop
variable [Ring 𝕜] [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/--
lemma `moebius_inversion_top` / 引理 `moebius_inversion_top`

English:
lemma moebius_inversion_top
  given: (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Ici x, f y) (x : α)
  proof: by
  let : DecidableLE α := Classical.decRel _
  symm
  calc
    ∑ y in Ici x, mu 𝕜 x y * g y = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, f z := by simp_rw [h]
    _ = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, zeta 𝕜 y z * f z := by
      congr with y
      rw [sum_congr rfl fun z hz => ?_]
      rw [zeta

中文:
引理 moebius_inversion_top
  条件: (f g : α -> 𝕜) (h : 对任意 x, g x = ∑ y in Ici x, f y) (x : α)
  证明: by
  let : DecidableLE α := Classical.decRel _
  symm
  calc
    ∑ y in Ici x, mu 𝕜 x y * g y = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, f z := by simp_rw [h]
    _ = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, zeta 𝕜 y z * f z := by
      congr with y
      rw [sum_congr rfl fun z hz => ?_]
      rw [zeta

Depends on / 依赖: Classical, Classical.decRel, DecidableLE, decRel, if_pos, mem_Ici, mem_Ici.mp, mul_sum, one_mul, simp_rw, sum_congr, sum_sigma, zeta_apply
-/
lemma moebius_inversion_top (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Ici x, f y) (x : α) :
    f x = ∑ y in Ici x, mu 𝕜 x y * g y := by
  let : DecidableLE α := Classical.decRel _
  symm
  calc
    ∑ y in Ici x, mu 𝕜 x y * g y = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, f z := by simp_rw [h]
    _ = ∑ y in Ici x, mu 𝕜 x y * ∑ z in Ici y, zeta 𝕜 y z * f z := by
      congr with y
      rw [sum_congr rfl fun z hz => ?_]
      rw [zeta_apply]; rw [if_pos (mem_Ici.mp ‹_›)]; rw [one_mul]
    _ = ∑ y in Ici x, ∑ z in Ici y, mu 𝕜 x y * zeta 𝕜 y z * f z := by simp [mul_sum]
    _ = ∑ z in Ici x, ∑ y in Icc x z, mu 𝕜 x y * zeta 𝕜 y z * f z := by
      rw [sum_sigma' (Ici x) fun y => Ici y]
      rw [sum_sigma' (Ici x) fun z => Icc x z]
      simp only [mul_boole, zero_mul, ite_mul, zeta_apply]
      apply sum_nbij' (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩) <;>
        aesop (add simp mul_assoc) (add unsafe le_trans)
    _ = ∑ z in Ici x, (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp_rw [mul_apply, sum_mul]
    _ = ∑ y in Ici x, ∑ z in Ici y, (1 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp only [mu_mul_zeta 𝕜, one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici, le_refl,
        ↓reduceIte, ← add_sum_Ioi_eq_sum_Ici, left_eq_add]
      exact sum_eq_zero fun y hy => if_neg (mem_Ioi.mp hy).not_ge
    _ = f x := by
      simp only [one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici,
        ← add_sum_Ioi_eq_sum_Ici, le_refl, ↓reduceIte, add_eq_left]
      exact sum_eq_zero fun y hy => if_neg (mem_Ioi.mp hy).not_ge

end InversionTop

section InversionBot
variable [Ring 𝕜] [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `moebius_inversion_bot` / 引理 `moebius_inversion_bot`

English:
lemma moebius_inversion_bot
  given: (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Iic x, f y) (x : α)
  proof: by
  convert! moebius_inversion_top (α := αᵒᵈ) f g h x using 3
  rw [← mu_toDual]; rfl

中文:
引理 moebius_inversion_bot
  条件: (f g : α -> 𝕜) (h : 对任意 x, g x = ∑ y in Iic x, f y) (x : α)
  证明: by
  convert! moebius_inversion_top (α := αᵒᵈ) f g h x using 3
  rw [← mu_toDual]; rfl

Depends on / 依赖: convert, moebius_inversion_top, mu_toDual
-/
lemma moebius_inversion_bot (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Iic x, f y) (x : α) :
    f x = ∑ y in Iic x, mu 𝕜 y x * g y := by
  convert! moebius_inversion_top (α := αᵒᵈ) f g h x using 3
  rw [← mu_toDual]; rfl

end InversionBot

section Prod

section Preorder

section Ring
variable (𝕜) [Ring 𝕜] [Preorder α] [Preorder β]

section DecidableLe
variable [DecidableLE α] [DecidableLE β]

/--
lemma `zeta_prod_apply` / 引理 `zeta_prod_apply`

English:
lemma zeta_prod_apply
  given: (a b : α × β)
  statement: zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2
  proof: by
  simp [← ite_and, Prod.le_def, and_comm]

中文:
引理 zeta_prod_apply
  条件: (a b : α × β)
  结论: zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2
  证明: by
  simp [← ite_and, Prod.le_def, and_comm]

Depends on / 依赖: Prod.le_def, and_comm, ite_and, le_def
-/
lemma zeta_prod_apply (a b : α × β) : zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2 := by
  simp [← ite_and, Prod.le_def, and_comm]

/--
lemma `zeta_prod_mk` / 引理 `zeta_prod_mk`

English:
lemma zeta_prod_mk
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  proof: zeta_prod_apply _ _ _

中文:
引理 zeta_prod_mk
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  证明: zeta_prod_apply _ _ _

Depends on / 依赖: zeta_prod_apply
-/
lemma zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    zeta 𝕜 (a₁, b₁) (a₂, b₂) = zeta 𝕜 a₁ a₂ * zeta 𝕜 b₁ b₂ := zeta_prod_apply _ _ _

end DecidableLe

variable {𝕜} (f f₁ f₂ : IncidenceAlgebra 𝕜 α) (g g₁ g₂ : IncidenceAlgebra 𝕜 β)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : IncidenceAlgebra 𝕜 (α × β) where
  body: f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def]; rw [not_and_or] at hxy
    obtain hxy | hxy := hxy <;> simp [apply_eq_zero_of_not_le hxy]

中文:
定义 prod
  签名: : IncidenceAlgebra 𝕜 (α × β) where
  定义体: f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def]; rw [not_and_or] at hxy
    obtain hxy | hxy := hxy <;> simp [apply_eq_zero_of_not_le hxy]
-/
protected def prod : IncidenceAlgebra 𝕜 (α × β) where
  toFun x y := f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def]; rw [not_and_or] at hxy
    obtain hxy | hxy := hxy <;> simp [apply_eq_zero_of_not_le hxy]

/--
lemma `prod_mk` / 引理 `prod_mk`

English:
lemma prod_mk
  given: (a₁ a₂ : α) (b₁ b₂ : β)
  statement: f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂
  proof: rfl

中文:
引理 prod_mk
  条件: (a₁ a₂ : α) (b₁ b₂ : β)
  结论: f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂
  证明: rfl
-/
lemma prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂ := rfl
/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: (x y : α × β)
  statement: f.prod g x y = f x.1 y.1 * g x.2 y.2
  proof: rfl

中文:
引理 prod_apply
  条件: (x y : α × β)
  结论: f.prod g x y = f x.1 y.1 * g x.2 y.2
  证明: rfl
-/
@[simp] lemma prod_apply (x y : α × β) : f.prod g x y = f x.1 y.1 * g x.2 y.2 := rfl

/--
lemma `prod_mul_prod'` / 引理 `prod_mul_prod'`

English:
lemma prod_mul_prod'
  statement: [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]
  proof: by
  ext x y; simp [Icc_prod_def, sum_mul_sum, h, sum_product]

@[simp]

中文:
引理 prod_mul_prod'
  结论: [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]
  证明: by
  ext x y; simp [Icc_prod_def, sum_mul_sum, h, sum_product]

@[simp]

Depends on / 依赖: Icc_prod_def, sum_mul_sum, sum_product
-/
lemma prod_mul_prod' [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]
    (h : forall a₁ a₂ a₃ b₁ b₂ b₃,
        f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ b₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)) :
    f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) := by
  ext x y; simp [Icc_prod_def, sum_mul_sum, h, sum_product]

@[simp]
/--
lemma `one_prod_one` / 引理 `one_prod_one`

English:
lemma one_prod_one
  given: [DecidableEq α] [DecidableEq β]
  proof: by
  ext x y; simp [Prod.ext_iff, ← ite_and, and_comm]

@[simp]

中文:
引理 one_prod_one
  条件: [DecidableEq α] [DecidableEq β]
  证明: by
  ext x y; simp [Prod.ext_iff, ← ite_and, and_comm]

@[simp]

Depends on / 依赖: Prod.ext_iff, and_comm, ext_iff, ite_and
-/
lemma one_prod_one [DecidableEq α] [DecidableEq β] :
    (.prod 1 1 : IncidenceAlgebra 𝕜 (α × β)) = 1 := by
  ext x y; simp [Prod.ext_iff, ← ite_and, and_comm]

@[simp]
/--
lemma `zeta_prod_zeta` / 引理 `zeta_prod_zeta`

English:
lemma zeta_prod_zeta
  given: [DecidableLE α] [DecidableLE β]
  proof: by
  ext x y hxy; simp [hxy, hxy.1, hxy.2]

中文:
引理 zeta_prod_zeta
  条件: [DecidableLE α] [DecidableLE β]
  证明: by
  ext x y hxy; simp [hxy, hxy.1, hxy.2]
-/
lemma zeta_prod_zeta [DecidableLE α] [DecidableLE β] :
    (zeta 𝕜).prod (zeta 𝕜) = (zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  ext x y hxy; simp [hxy, hxy.1, hxy.2]

end Ring

section CommRing
variable [CommRing 𝕜] [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (f₁ f₂ : IncidenceAlgebra 𝕜 α) (g₁ g₂ : IncidenceAlgebra 𝕜 β)

@[simp]
/--
lemma `prod_mul_prod` / 引理 `prod_mul_prod`

English:
lemma prod_mul_prod
  statement: f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂)
  proof: prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ => mul_mul_mul_comm ..

中文:
引理 prod_mul_prod
  结论: f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂)
  证明: prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ => mul_mul_mul_comm ..

Depends on / 依赖: mul_mul_mul_comm, prod_mul_prod
-/
lemma prod_mul_prod : f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) :=
  prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ => mul_mul_mul_comm ..

end CommRing
end Preorder

section PartialOrder
variable (𝕜) [Ring 𝕜] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α]
  [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]

/-- The Möbius function on a product order. Based on lemma 2.1.13 of Incidence Algebras by Spiegel
and O'Donnell. -/
@[simp]
/--
lemma `mu_prod_mu` / 引理 `mu_prod_mu`

English:
lemma mu_prod_mu
  statement: (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β))
  proof: by
  refine left_inv_eq_right_inv ?_ zeta_mul_mu
  rw [← zeta_prod_zeta]; rw [prod_mul_prod']; rw [mu_mul_zeta]; rw [mu_mul_zeta]; rw [one_prod_one]
  exact fun _ _ _ _ _ _ => Commute.mul_mul_mul_comm (by simp : _ = _) _ _

@[simp]

中文:
引理 mu_prod_mu
  结论: (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β))
  证明: by
  refine left_inv_eq_right_inv ?_ zeta_mul_mu
  rw [← zeta_prod_zeta]; rw [prod_mul_prod']; rw [mu_mul_zeta]; rw [mu_mul_zeta]; rw [one_prod_one]
  exact fun _ _ _ _ _ _ => Commute.mul_mul_mul_comm (by simp : _ = _) _ _

@[simp]

Depends on / 依赖: Commute, Commute.mul_mul_mul_comm, left_inv_eq_right_inv, mu_mul_zeta, mul_mul_mul_comm, one_prod_one, prod_mul_prod, zeta_mul_mu, zeta_prod_zeta
-/
lemma mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  refine left_inv_eq_right_inv ?_ zeta_mul_mu
  rw [← zeta_prod_zeta]; rw [prod_mul_prod']; rw [mu_mul_zeta]; rw [mu_mul_zeta]; rw [one_prod_one]
  exact fun _ _ _ _ _ _ => Commute.mul_mul_mul_comm (by simp : _ = _) _ _

@[simp]
/--
lemma `eulerChar_prod` / 引理 `eulerChar_prod`

English:
lemma eulerChar_prod
  given: [BoundedOrder α] [BoundedOrder β]
  proof: by simp [eulerChar, ← mu_prod_mu]

中文:
引理 eulerChar_prod
  条件: [BoundedOrder α] [BoundedOrder β]
  证明: by simp [eulerChar, ← mu_prod_mu]

Depends on / 依赖: eulerChar, mu_prod_mu
-/
lemma eulerChar_prod [BoundedOrder α] [BoundedOrder β] :
    eulerChar 𝕜 (α × β) = eulerChar 𝕜 α * eulerChar 𝕜 β := by simp [eulerChar, ← mu_prod_mu]

end PartialOrder
end Prod
end IncidenceAlgebra
