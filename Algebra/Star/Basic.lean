/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.SetLike.Basic

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

@[expose] public section

assert_not_exists Finset Subgroup Rat.instField

open scoped Ring

universe u v w

open MulOpposite

variable {R : Type u}

/--
Definition of `StarMemClass` / `StarMemClass` 的定义

English:
class StarMemClass
  parameters: (S R : Type*) [Star R] [SetLike S R]
  axioms and operations (1):
    - star_mem : forall {s : S} {r : R}, r in s -> star r in s

中文:
类 StarMem类
  参数: (S R : 类型) [对合 R] [集合状 S R]
  公理与运算 (1 个):
    - star_mem : 对任意 {s : S} {r : R}, r in s -> star r in s

Depends on / 依赖: SetLike, star_mem
-/
class StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where
  /-- Closure under star. -/
  star_mem : forall {s : S} {r : R}, r in s -> star r in s

export StarMemClass (star_mem)

attribute [aesop 90% (rule_sets := [SetLike])] star_mem

namespace StarMemClass

variable {S : Type w} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

/--
Instance `instStar` / 实例 `instStar`

English:
instance instStar
  signature: : Star s where
  body: ⟨star (r : R), star_mem r.prop⟩

中文:
实例 instStar
  签名: : 对合 s where
  定义体: ⟨star (r : R), star_mem r.prop⟩

Depends on / 依赖: r.prop, star_mem
-/
instance instStar : Star s where
  star r := ⟨star (r : R), star_mem r.prop⟩

/--
lemma `coe_star` / 引理 `coe_star`

English:
lemma coe_star
  given: (x : s)
  statement: star x = star (x : R)
  proof: rfl

中文:
引理 coe_star
  条件: (x : s)
  结论: star x = star (x : R)
  证明: rfl
-/
@[simp] lemma coe_star (x : s) : star x = star (x : R) := rfl

end StarMemClass

/--
Definition of `InvolutiveStar` / `InvolutiveStar` 的定义

English:
class InvolutiveStar
  parameters: (R : Type u)
  extends: Star R
  axioms and operations (1):
    - star_involutive : Function.Involutive star

中文:
类 InvolutiveStar
  参数: (R : 类型u)
  继承: 对合 R
  公理与运算 (1 个):
    - star_involutive : 函数.对合 star
-/
class InvolutiveStar (R : Type u) extends Star R where
  /-- Involutive condition. -/
  star_involutive : Function.Involutive star

export InvolutiveStar (star_involutive)

@[simp]
/--
theorem `star_star` / 定理 `star_star`

English:
theorem star_star
  given: [InvolutiveStar R] (r : R)
  statement: star (star r) = r
  proof: star_involutive _

中文:
定理 star_star
  条件: [InvolutiveStar R] (r : R)
  结论: star (star r) = r
  证明: star_involutive _

Depends on / 依赖: star_involutive
-/
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _

/--
lemma `star_mem_iff` / 引理 `star_mem_iff`

English:
lemma star_mem_iff
  statement: {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S R]
  proof: ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩

中文:
引理 star_mem_iff
  结论: {S : 类型} [集合状 S R] [InvolutiveStar R] [StarMem类 S R]
  证明: ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩

Depends on / 依赖: star_mem, star_star
-/
lemma star_mem_iff {S : Type*} [SetLike S R] [InvolutiveStar R] [StarMemClass S R]
    {s : S} {x : R} : star x in s ↔ x in s :=
  ⟨fun h => star_star x ▸ star_mem h, fun h => star_mem h⟩

/--
theorem `star_injective` / 定理 `star_injective`

English:
theorem star_injective
  given: [InvolutiveStar R]
  statement: Function.Injective (star : R -> R)
  proof: Function.Involutive.injective star_involutive

@[aesop 5% (rule_sets := [SetLike!])]

中文:
定理 star_injective
  条件: [InvolutiveStar R]
  结论: 函数.单射 (star : R -> R)
  证明: Function.Involutive.injective star_involutive

@[aesop 5% (rule_sets := [SetLike!])]

Depends on / 依赖: Function, Function.Involutive.injective, Involutive, injective, star_involutive
-/
theorem star_injective [InvolutiveStar R] : Function.Injective (star : R -> R) :=
  Function.Involutive.injective star_involutive

@[aesop 5% (rule_sets := [SetLike!])]
/--
theorem `mem_of_star_mem` / 定理 `mem_of_star_mem`

English:
theorem mem_of_star_mem
  statement: {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
  proof: by rw [← star_star r]; exact star_mem hr

@[simp]

中文:
定理 mem_of_star_mem
  结论: {S R : 类型} [InvolutiveStar R] [集合状 S R] [StarMem类 S R]
  证明: by rw [← star_star r]; exact star_mem hr

@[simp]

Depends on / 依赖: star_mem, star_star
-/
theorem mem_of_star_mem {S R : Type*} [InvolutiveStar R] [SetLike S R] [StarMemClass S R]
    {s : S} {r : R} (hr : star r in s) : r in s := by rw [← star_star r]; exact star_mem hr

@[simp]
/--
theorem `star_inj` / 定理 `star_inj`

English:
theorem star_inj
  given: [InvolutiveStar R] {x y : R}
  statement: star x = star y ↔ x = y
  proof: star_injective.eq_iff

中文:
定理 star_inj
  条件: [InvolutiveStar R] {x y : R}
  结论: star x = star y ↔ x = y
  证明: star_injective.eq_iff

Depends on / 依赖: eq_iff, star_injective, star_injective.eq_iff
-/
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff

/-- `star` as an equivalence when it is involutive. -/
@[simps! apply]
/--
Definition of `Equiv.Perm.star` / `Equiv.Perm.star` 的定义

English:
definition Equiv.Perm.star
  signature: [InvolutiveStar R]
  body: star
  invFun := star
  __ : Equiv.Perm R := star_involutive.toPerm _

@[simp]

中文:
定义 等价.置换.star
  签名: [InvolutiveStar R]
  定义体: star
  invFun := star
  __ : Equiv.Perm R := star_involutive.toPerm _

@[simp]
-/
protected def Equiv.Perm.star [InvolutiveStar R] : Equiv.Perm R where
  toFun := star
  invFun := star
  __ : Equiv.Perm R := star_involutive.toPerm _

@[simp]
/--
theorem `Equiv.Perm.symm_star` / 定理 `Equiv.Perm.symm_star`

English:
theorem Equiv.Perm.symm_star
  given: [InvolutiveStar R]
  proof: rfl

中文:
定理 等价.置换.symm_star
  条件: [InvolutiveStar R]
  证明: rfl
-/
theorem Equiv.Perm.symm_star [InvolutiveStar R] :
    (Equiv.Perm.star : R ≃ R).symm = Equiv.Perm.star :=
  rfl

/--
theorem `eq_star_of_eq_star` / 定理 `eq_star_of_eq_star`

English:
theorem eq_star_of_eq_star
  given: [InvolutiveStar R] {r s : R} (h : r = star s)
  statement: s = star r
  proof: by
  simp [h]

中文:
定理 eq_star_of_eq_star
  条件: [InvolutiveStar R] {r s : R} (h : r = star s)
  结论: s = star r
  证明: by
  simp [h]
-/
theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]

/--
theorem `eq_star_iff_eq_star` / 定理 `eq_star_iff_eq_star`

English:
theorem eq_star_iff_eq_star
  given: [InvolutiveStar R] {r s : R}
  statement: r = star s ↔ s = star r
  proof: ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

中文:
定理 eq_star_iff_eq_star
  条件: [InvolutiveStar R] {r s : R}
  结论: r = star s ↔ s = star r
  证明: ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

Depends on / 依赖: eq_star_of_eq_star
-/
theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩

/--
theorem `star_eq_iff_star_eq` / 定理 `star_eq_iff_star_eq`

English:
theorem star_eq_iff_star_eq
  given: [InvolutiveStar R] {r s : R}
  statement: star r = s ↔ star s = r
  proof: eq_comm.trans eq_star_iff_eq_star.trans eq_comm

中文:
定理 star_eq_iff_star_eq
  条件: [InvolutiveStar R] {r s : R}
  结论: star r = s ↔ star s = r
  证明: eq_comm.trans eq_star_iff_eq_star.trans eq_comm

Depends on / 依赖: eq_comm, eq_comm.trans, eq_star_iff_eq_star, eq_star_iff_eq_star.trans
-/
theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
eq_comm.trans eq_star_iff_eq_star.trans eq_comm

/--
Definition of `TrivialStar` / `TrivialStar` 的定义

English:
class TrivialStar
  parameters: (R : Type u) [Star R]
  axioms and operations (1):
    - star_trivial : forall r : R, star r = r

中文:
类 TrivialStar
  参数: (R : 类型u) [对合 R]
  公理与运算 (1 个):
    - star_trivial : 对任意 r : R, star r = r
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial -/
  star_trivial : forall r : R, star r = r

export TrivialStar (star_trivial)

attribute [simp] star_trivial

/--
Definition of `StarMul` / `StarMul` 的定义

English:
class StarMul
  parameters: (R : Type u) [Mul R]
  extends: InvolutiveStar R
  axioms and operations (1):
    - star_mul : forall r s : R, star (r * s) = star s * star r

中文:
类 StarMul
  参数: (R : 类型u) [乘法 R]
  继承: InvolutiveStar R
  公理与运算 (1 个):
    - star_mul : 对任意 r s : R, star (r * s) = star s * star r
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : forall r s : R, star (r * s) = star s * star r

export StarMul (star_mul)

attribute [simp 900] star_mul

section StarMul

variable [Mul R] [StarMul R]

/--
theorem `star_star_mul` / 定理 `star_star_mul`

English:
theorem star_star_mul
  given: (x y : R)
  statement: star (star x * y) = star y * x
  proof: by rw [star_mul, star_star]

中文:
定理 star_star_mul
  条件: (x y : R)
  结论: star (star x * y) = star y * x
  证明: by rw [star_mul, star_star]

Depends on / 依赖: star_mul, star_star
-/
theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]

/--
theorem `star_mul_star` / 定理 `star_mul_star`

English:
theorem star_mul_star
  given: (x y : R)
  statement: star (x * star y) = y * star x
  proof: by rw [star_mul, star_star]

@[simp]

中文:
定理 star_mul_star
  条件: (x y : R)
  结论: star (x * star y) = y * star x
  证明: by rw [star_mul, star_star]

@[simp]

Depends on / 依赖: star_mul, star_star
-/
theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]

@[simp]
/--
theorem `semiconjBy_star_star_star` / 定理 `semiconjBy_star_star_star`

English:
theorem semiconjBy_star_star_star
  given: {x y z : R}
  proof: by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star

@[simp]

中文:
定理 semiconjBy_star_star_star
  条件: {x y z : R}
  证明: by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star

@[simp]

Depends on / 依赖: SemiconjBy, eq_comm, simp_rw, star_inj, star_mul
-/
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star

@[simp]
/--
theorem `commute_star_star` / 定理 `commute_star_star`

English:
theorem commute_star_star
  given: {x y : R}
  statement: Commute (star x) (star y) ↔ Commute x y
  proof: semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star

中文:
定理 commute_star_star
  条件: {x y : R}
  结论: Commute (star x) (star y) ↔ Commute x y
  证明: semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star

Depends on / 依赖: semiconjBy_star_star_star
-/
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star

/--
theorem `commute_star_comm` / 定理 `commute_star_comm`

English:
theorem commute_star_comm
  given: {x y : R}
  statement: Commute (star x) y ↔ Commute x (star y)
  proof: by
  rw [← commute_star_star]; rw [star_star]

alias ⟨Commute.star_right, Commute.star_left⟩ := commute_star_comm

中文:
定理 commute_star_comm
  条件: {x y : R}
  结论: Commute (star x) y ↔ Commute x (star y)
  证明: by
  rw [← commute_star_star]; rw [star_star]

alias ⟨Commute.star_right, Commute.star_left⟩ := commute_star_comm

Depends on / 依赖: commute_star_star, star_star
-/
theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star]; rw [star_star]

alias ⟨Commute.star_right, Commute.star_left⟩ := commute_star_comm

end StarMul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
/--
theorem `star_mul'` / 定理 `star_mul'`

English:
theorem star_mul'
  given: [CommMagma R] [StarMul R] (x y : R)
  statement: star (x * y) = star x * star y
  proof: (star_mul x y).trans (mul_comm _ _)

中文:
定理 star_mul'
  条件: [交换原群 R] [StarMul R] (x y : R)
  结论: star (x * y) = star x * star y
  证明: (star_mul x y).trans (mul_comm _ _)

Depends on / 依赖: mul_comm, star_mul
-/
theorem star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
/--
Definition of `starMulEquiv` / `starMulEquiv` 的定义

English:
definition starMulEquiv
  signature: [Mul R] [StarMul R]
  body: { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

中文:
定义 starMulEquiv
  签名: [乘法 R] [StarMul R]
  定义体: { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

Depends on / 依赖: InvolutiveStar, InvolutiveStar.star_involutive.toPerm, MulOpposite, MulOpposite.op, map_mul, opEquiv, op_mul, star_involutive, star_mul, toPerm
-/
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }

/-- `star` as a `MulAut` for commutative `R`. -/
@[simps apply]
/--
Definition of `starMulAut` / `starMulAut` 的定义

English:
definition starMulAut
  signature: [CommSemigroup R] [StarMul R]
  body: { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }

中文:
定义 starMulAut
  签名: [交换半群 R] [StarMul R]
  定义体: { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }

Depends on / 依赖: InvolutiveStar, InvolutiveStar.star_involutive.toPerm, map_mul, star_involutive, star_mul, toPerm
-/
def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }

variable (R) in
@[simp]
/--
theorem `star_one` / 定理 `star_one`

English:
theorem star_one
  given: [MulOneClass R] [StarMul R]
  statement: star (1 : R) = 1
  proof: op_injective (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

@[simp]

中文:
定理 star_one
  条件: [MulOne类 R] [StarMul R]
  结论: star (1 : R) = 1
  证明: op_injective (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

@[simp]

Depends on / 依赖: map_one, map_one.trans, op_injective, op_one, op_one.symm, starMulEquiv
-/
theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 :=
op_injective (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm

@[simp]
/--
lemma `Pi.star_mulSingle` / 引理 `Pi.star_mulSingle`

English:
lemma Pi.star_mulSingle
  statement: {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, MulOneClass (R i)]
  proof: by
  ext; exact apply_mulSingle (fun _ => star) (fun _ => star_one _) ..

@[simp]

中文:
引理 依赖函数类型.star_mulSingle
  结论: {ι : 类型} {R : ι -> 类型} [DecidableEq ι] [对任意 i, MulOne类 (R i)]
  证明: by
  ext; exact apply_mulSingle (fun _ => star) (fun _ => star_one _) ..

@[simp]

Depends on / 依赖: apply_mulSingle, star_one
-/
lemma Pi.star_mulSingle {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, MulOneClass (R i)]
    [forall i, StarMul (R i)] (i : ι) (r : R i) : star (mulSingle i r) = mulSingle i (star r) := by
  ext; exact apply_mulSingle (fun _ => star) (fun _ => star_one _) ..

@[simp]
/--
theorem `star_pow` / 定理 `star_pow`

English:
theorem star_pow
  given: [Monoid R] [StarMul R] (x : R) (n : Nat)
  statement: star (x ^ n) = star x ^ n
  proof: op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]

中文:
定理 star_pow
  条件: [幺半群 R] [StarMul R] (x : R) (n : 自然数)
  结论: star (x ^ n) = star x ^ n
  证明: op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]

Depends on / 依赖: map_pow, op_injective, op_pow, starMulEquiv, toMonoidHom, toMonoidHom.map_pow
-/
theorem star_pow [Monoid R] [StarMul R] (x : R) (n : Nat) : star (x ^ n) = star x ^ n :=
op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm

@[simp]
/--
theorem `star_inv` / 定理 `star_inv`

English:
theorem star_inv
  given: [Group R] [StarMul R] (x : R)
  statement: star x⁻¹ = (star x)⁻¹
  proof: op_injective ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]

中文:
定理 star_inv
  条件: [群 R] [StarMul R] (x : R)
  结论: star x⁻¹ = (star x)⁻¹
  证明: op_injective ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]

Depends on / 依赖: map_inv, op_injective, op_inv, starMulEquiv, toMonoidHom, toMonoidHom.map_inv
-/
theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
op_injective ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm

@[simp]
/--
theorem `star_zpow` / 定理 `star_zpow`

English:
theorem star_zpow
  given: [Group R] [StarMul R] (x : R) (z : Int)
  statement: star (x ^ z) = star x ^ z
  proof: op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

中文:
定理 star_zpow
  条件: [群 R] [StarMul R] (x : R) (z : 整数)
  结论: star (x ^ z) = star x ^ z
  证明: op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

Depends on / 依赖: map_zpow, op_injective, op_zpow, starMulEquiv, toMonoidHom, toMonoidHom.map_zpow
-/
theorem star_zpow [Group R] [StarMul R] (x : R) (z : Int) : star (x ^ z) = star x ^ z :=
op_injective
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
/--
theorem `star_div` / 定理 `star_div`

English:
theorem star_div
  given: [CommGroup R] [StarMul R] (x y : R)
  statement: star (x / y) = star x / star y
  proof: map_div (starMulAut : R ≃* R) _ _

中文:
定理 star_div
  条件: [交换群 R] [StarMul R] (x y : R)
  结论: star (x / y) = star x / star y
  证明: map_div (starMulAut : R ≃* R) _ _

Depends on / 依赖: map_div, starMulAut
-/
theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _

/--
Definition of `starMulOfComm` / `starMulOfComm` 的定义

English:
abbreviation starMulOfComm
  signature: {R : Type*} [CommMonoid R]
  body: x
  star_involutive _ := rfl
  star_mul := mul_comm

中文:
缩写 starMulOfComm
  签名: {R : 类型} [交换幺半群 R]
  定义体: x
  star_involutive _ := rfl
  star_mul := mul_comm
-/
abbrev starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where
  star x := x
  star_involutive _ := rfl
  star_mul := mul_comm

section

attribute [local instance] starMulOfComm

/--
theorem `star_id_of_comm` / 定理 `star_id_of_comm`

English:
theorem star_id_of_comm
  given: {R : Type*} [CommMonoid R] {x : R}
  statement: star x = x
  proof: rfl

中文:
定理 star_id_of_comm
  条件: {R : 类型} [交换幺半群 R] {x : R}
  结论: star x = x
  证明: rfl
-/
theorem star_id_of_comm {R : Type*} [CommMonoid R] {x : R} : star x = x :=
  rfl

end

/--
Definition of `StarAddMonoid` / `StarAddMonoid` 的定义

English:
class StarAddMonoid
  parameters: (R : Type u) [AddMonoid R]
  extends: InvolutiveStar R
  axioms and operations (1):
    - star_add : forall r s : R, star (r + s) = star r + star s

中文:
类 StarAdd幺半群
  参数: (R : 类型u) [加法幺半群 R]
  继承: InvolutiveStar R
  公理与运算 (1 个):
    - star_add : 对任意 r s : R, star (r + s) = star r + star s
-/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  /-- `star` commutes with addition -/
  star_add : forall r s : R, star (r + s) = star r + star s

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `AddEquiv` -/
@[simps! apply]
/--
Definition of `starAddEquiv` / `starAddEquiv` 的定义

English:
definition starAddEquiv
  signature: [AddMonoid R] [StarAddMonoid R]
  body: Equiv.Perm.star
  map_add' := star_add

@[simp]

中文:
定义 starAddEquiv
  签名: [加法幺半群 R] [StarAdd幺半群 R]
  定义体: Equiv.Perm.star
  map_add' := star_add

@[simp]

Depends on / 依赖: Equiv.Perm.star
-/
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R where
  toEquiv := Equiv.Perm.star
  map_add' := star_add

@[simp]
/--
theorem `toEquiv_starAddEquiv` / 定理 `toEquiv_starAddEquiv`

English:
theorem toEquiv_starAddEquiv
  given: [AddMonoid R] [StarAddMonoid R]
  proof: rfl

@[simp]

中文:
定理 toEquiv_starAddEquiv
  条件: [加法幺半群 R] [StarAdd幺半群 R]
  证明: rfl

@[simp]
-/
theorem toEquiv_starAddEquiv [AddMonoid R] [StarAddMonoid R] :
    (starAddEquiv : R ≃+ R) = (Equiv.Perm.star : R ≃ R) :=
  rfl

@[simp]
/--
theorem `symm_starAddEquiv` / 定理 `symm_starAddEquiv`

English:
theorem symm_starAddEquiv
  given: [AddMonoid R] [StarAddMonoid R]
  proof: rfl

中文:
定理 symm_starAddEquiv
  条件: [加法幺半群 R] [StarAdd幺半群 R]
  证明: rfl
-/
theorem symm_starAddEquiv [AddMonoid R] [StarAddMonoid R] :
    (starAddEquiv : R ≃+ R).symm = starAddEquiv :=
  rfl

variable (R) in
@[simp]
/--
theorem `star_zero` / 定理 `star_zero`

English:
theorem star_zero
  given: [AddMonoid R] [StarAddMonoid R]
  statement: star (0 : R) = 0
  proof: (starAddEquiv : R ≃+ R).map_zero

@[simp]

中文:
定理 star_zero
  条件: [加法幺半群 R] [StarAdd幺半群 R]
  结论: star (0 : R) = 0
  证明: (starAddEquiv : R ≃+ R).map_zero

@[simp]

Depends on / 依赖: map_zero, starAddEquiv
-/
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero

@[simp]
/--
lemma `Pi.star_single` / 引理 `Pi.star_single`

English:
lemma Pi.star_single
  statement: {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, AddMonoid (R i)]
  proof: by
  ext; exact apply_single (fun _ => star) (fun _ => star_zero _) ..

@[simp]

中文:
引理 依赖函数类型.star_single
  结论: {ι : 类型} {R : ι -> 类型} [DecidableEq ι] [对任意 i, 加法幺半群 (R i)]
  证明: by
  ext; exact apply_single (fun _ => star) (fun _ => star_zero _) ..

@[simp]

Depends on / 依赖: apply_single, star_zero
-/
lemma Pi.star_single {ι : Type*} {R : ι -> Type*} [DecidableEq ι] [forall i, AddMonoid (R i)]
    [forall i, StarAddMonoid (R i)] (i : ι) (r : R i) : star (single i r) = single i (star r) := by
  ext; exact apply_single (fun _ => star) (fun _ => star_zero _) ..

@[simp]
/--
theorem `star_eq_zero` / 定理 `star_eq_zero`

English:
theorem star_eq_zero
  given: [AddMonoid R] [StarAddMonoid R] {x : R}
  statement: star x = 0 ↔ x = 0
  proof: starAddEquiv.map_eq_zero_iff (M := R)

中文:
定理 star_eq_zero
  条件: [加法幺半群 R] [StarAdd幺半群 R] {x : R}
  结论: star x = 0 ↔ x = 0
  证明: starAddEquiv.map_eq_zero_iff (M := R)

Depends on / 依赖: map_eq_zero_iff, starAddEquiv, starAddEquiv.map_eq_zero_iff
-/
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff (M := R)

/--
theorem `star_ne_zero` / 定理 `star_ne_zero`

English:
theorem star_ne_zero
  given: [AddMonoid R] [StarAddMonoid R] {x : R}
  statement: star x != 0 ↔ x != 0
  proof: by
  simp only [ne_eq, star_eq_zero]

@[simp]

中文:
定理 star_ne_zero
  条件: [加法幺半群 R] [StarAdd幺半群 R] {x : R}
  结论: star x != 0 ↔ x != 0
  证明: by
  simp only [ne_eq, star_eq_zero]

@[simp]

Depends on / 依赖: ne_eq, star_eq_zero
-/
theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x != 0 ↔ x != 0 := by
  simp only [ne_eq, star_eq_zero]

@[simp]
/--
theorem `star_neg` / 定理 `star_neg`

English:
theorem star_neg
  given: [AddGroup R] [StarAddMonoid R] (r : R)
  statement: star (-r) = -star r
  proof: (starAddEquiv : R ≃+ R).map_neg _

@[simp]

中文:
定理 star_neg
  条件: [加法群 R] [StarAdd幺半群 R] (r : R)
  结论: star (-r) = -star r
  证明: (starAddEquiv : R ≃+ R).map_neg _

@[simp]

Depends on / 依赖: map_neg, starAddEquiv
-/
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _

@[simp]
/--
theorem `star_sub` / 定理 `star_sub`

English:
theorem star_sub
  given: [AddGroup R] [StarAddMonoid R] (r s : R)
  statement: star (r - s) = star r - star s
  proof: (starAddEquiv : R ≃+ R).map_sub _ _

中文:
定理 star_sub
  条件: [加法群 R] [StarAdd幺半群 R] (r s : R)
  结论: star (r - s) = star r - star s
  证明: (starAddEquiv : R ≃+ R).map_sub _ _

Depends on / 依赖: map_sub, starAddEquiv
-/
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _

/--
theorem `star_nsmul` / 定理 `star_nsmul`

English:
theorem star_nsmul
  given: [AddMonoid R] [StarAddMonoid R] (n : Nat) (x : R)
  statement: star (n • x) = n • star x
  proof: (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

中文:
定理 star_nsmul
  条件: [加法幺半群 R] [StarAdd幺半群 R] (n : 自然数) (x : R)
  结论: star (n • x) = n • star x
  证明: (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

Depends on / 依赖: map_nsmul, starAddEquiv, toAddMonoidHom, toAddMonoidHom.map_nsmul
-/
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (n : Nat) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _

/--
theorem `star_zsmul` / 定理 `star_zsmul`

English:
theorem star_zsmul
  given: [AddGroup R] [StarAddMonoid R] (n : Int) (x : R)
  statement: star (n • x) = n • star x
  proof: (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

中文:
定理 star_zsmul
  条件: [加法群 R] [StarAdd幺半群 R] (n : 整数) (x : R)
  结论: star (n • x) = n • star x
  证明: (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

Depends on / 依赖: map_zsmul, starAddEquiv, toAddMonoidHom, toAddMonoidHom.map_zsmul
-/
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (n : Int) (x : R) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _

/--
Definition of `StarRing` / `StarRing` 的定义

English:
class StarRing
  parameters: (R : Type u) [NonUnitalNonAssocSemiring R]
  extends: StarMul R
  axioms and operations (1):
    - star_add : forall r s : R, star (r + s) = star r + star s

中文:
类 对合环
  参数: (R : 类型u) [非幺非结合半环 R]
  继承: StarMul R
  公理与运算 (1 个):
    - star_add : 对任意 r s : R, star (r + s) = star r + star s
-/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : forall r s : R, star (r + s) = star r + star s

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add

/-- `star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
/--
Definition of `starRingEquiv` / `starRingEquiv` 的定义

English:
definition starRingEquiv
  signature: [NonUnitalNonAssocSemiring R] [StarRing R]
  body: { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]

中文:
定义 starRingEquiv
  签名: [非幺非结合半环 R] [对合环 R]
  定义体: { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]

Depends on / 依赖: MulOpposite, MulOpposite.op, MulOpposite.opAddEquiv, opAddEquiv, starAddEquiv, starAddEquiv.trans, starMulEquiv
-/
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }

@[simp, norm_cast]
/--
theorem `star_natCast` / 定理 `star_natCast`

English:
theorem star_natCast
  given: [NonAssocSemiring R] [StarRing R] (n : Nat)
  statement: star (n : R) = n
  proof: (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

@[simp]

中文:
定理 star_natCast
  条件: [非结合半环 R] [对合环 R] (n : 自然数)
  结论: star (n : R) = n
  证明: (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

@[simp]

Depends on / 依赖: congr_arg, map_natCast, starRingEquiv, unop_natCast
-/
theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

@[simp]
/--
theorem `star_ofNat` / 定理 `star_ofNat`

English:
theorem star_ofNat
  given: [NonAssocSemiring R] [StarRing R] (n : Nat) [n.AtLeastTwo]
  proof: star_natCast _

中文:
定理 star_of自然数
  条件: [非结合半环 R] [对合环 R] (n : 自然数) [n.AtLeastTwo]
  证明: star_natCast _

Depends on / 依赖: star_natCast
-/
theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : Nat) [n.AtLeastTwo] :
    star (ofNat(n) : R) = ofNat(n) :=
  star_natCast _

section

@[simp, norm_cast]
/--
theorem `star_intCast` / 定理 `star_intCast`

English:
theorem star_intCast
  given: [NonAssocRing R] [StarRing R] (z : Int)
  statement: star (z : R) = z
  proof: (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

中文:
定理 star_intCast
  条件: [非结合环 R] [对合环 R] (z : 整数)
  结论: star (z : R) = z
  证明: (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

Depends on / 依赖: congr_arg, map_intCast, starRingEquiv, unop_intCast
-/
theorem star_intCast [NonAssocRing R] [StarRing R] (z : Int) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

end

section CommSemiring

variable [CommSemiring R] [StarRing R]

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
/--
Definition of `starRingAut` / `starRingAut` 的定义

English:
definition starRingAut
  signature: : RingAut R
  body: { starAddEquiv, starMulAut (R := R) with toFun := star, invFun := star }

中文:
定义 starRingAut
  签名: : RingAut R
  定义体: { starAddEquiv, starMulAut (R := R) with toFun := star, invFun := star }

Depends on / 依赖: invFun, starAddEquiv, starMulAut
-/
def starRingAut : RingAut R :=
  { starAddEquiv, starMulAut (R := R) with toFun := star, invFun := star }

variable (R) in
/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the scope `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
@[implicit_reducible]
/--
Definition of `starRingEnd` / `starRingEnd` 的定义

English:
definition starRingEnd
  signature: : R ->+* R where
  body: star
  __ := (@starRingAut R _ _).toRingHom

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

中文:
定义 starRingEnd
  签名: : R ->+* R where
  定义体: star
  __ := (@starRingAut R _ _).toRingHom

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _
-/
def starRingEnd : R ->+* R where
  toFun := star
  __ := (@starRingAut R _ _).toRingHom

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

/--
theorem `starRingEnd_apply` / 定理 `starRingEnd_apply`

English:
theorem starRingEnd_apply
  given: (x : R)
  statement: starRingEnd R x = star x
  proof: rfl

中文:
定理 starRingEnd_apply
  条件: (x : R)
  结论: starRingEnd R x = star x
  证明: rfl
-/
theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl

-- Not `@[simp]` because `simp` can already prove it.
/--
theorem `starRingEnd_self_apply` / 定理 `starRingEnd_self_apply`

English:
theorem starRingEnd_self_apply
  given: (x : R)
  statement: starRingEnd R (starRingEnd R x) = x
  proof: star_star x

中文:
定理 starRingEnd_self_apply
  条件: (x : R)
  结论: starRingEnd R (starRingEnd R x) = x
  证明: star_star x

Depends on / 依赖: star_star
-/
theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x

/--
Instance `RingHom.involutiveStar` / 实例 `RingHom.involutiveStar`

English:
instance RingHom.involutiveStar
  signature: {S : Type*} [NonAssocSemiring S]
  body: { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]

中文:
实例 环态射.involutiveStar
  签名: {S : 类型} [非结合半环 S]
  定义体: { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]

Depends on / 依赖: RingHom, RingHom.comp, starRingEnd
-/
instance RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (S ->+* R) where
  toStar := { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]

/--
theorem `RingHom.star_def` / 定理 `RingHom.star_def`

English:
theorem RingHom.star_def
  given: {S : Type*} [NonAssocSemiring S] (f : S ->+* R)
  proof: rfl

中文:
定理 环态射.star_def
  条件: {S : 类型} [非结合半环 S] (f : S ->+* R)
  证明: rfl
-/
theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S ->+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl

/--
theorem `RingHom.star_apply` / 定理 `RingHom.star_apply`

English:
theorem RingHom.star_apply
  given: {S : Type*} [NonAssocSemiring S] (f : S ->+* R) (s : S)
  proof: rfl

中文:
定理 环态射.star_apply
  条件: {S : 类型} [非结合半环 S] (f : S ->+* R) (s : S)
  证明: rfl
-/
theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S ->+* R) (s : S) :
    star f s = star (f s) := rfl

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply

alias RCLike.conj_conj := starRingEnd_self_apply

open scoped ComplexConjugate

/--
lemma `conj_trivial` / 引理 `conj_trivial`

English:
lemma conj_trivial
  given: [TrivialStar R] (a : R)
  statement: conj a = a
  proof: star_trivial _

中文:
引理 conj_trivial
  条件: [TrivialStar R] (a : R)
  结论: conj a = a
  证明: star_trivial _
-/
@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _

end CommSemiring

@[simp]
/--
theorem `star_inv₀` / 定理 `star_inv₀`

English:
theorem star_inv₀
  given: [GroupWithZero R] [StarMul R] (x : R)
  statement: star x⁻¹ = (star x)⁻¹
  proof: op_injective (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp]

中文:
定理 star_inv₀
  条件: [带零群 R] [StarMul R] (x : R)
  结论: star x⁻¹ = (star x)⁻¹
  证明: op_injective (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp]

Depends on / 依赖: op_injective, op_inv, starMulEquiv
-/
theorem star_inv₀ [GroupWithZero R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
op_injective (map_inv₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm

@[simp]
/--
theorem `star_zpow₀` / 定理 `star_zpow₀`

English:
theorem star_zpow₀
  given: [GroupWithZero R] [StarMul R] (x : R) (z : Int)
  statement: star (x ^ z) = star x ^ z
  proof: op_injective (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

中文:
定理 star_zpow₀
  条件: [带零群 R] [StarMul R] (x : R) (z : 整数)
  结论: star (x ^ z) = star x ^ z
  证明: op_injective (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

Depends on / 依赖: op_injective, op_zpow, starMulEquiv
-/
theorem star_zpow₀ [GroupWithZero R] [StarMul R] (x : R) (z : Int) : star (x ^ z) = star x ^ z :=
op_injective (map_zpow₀ (starMulEquiv : R ≃* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
/--
theorem `star_div₀` / 定理 `star_div₀`

English:
theorem star_div₀
  given: [CommGroupWithZero R] [StarMul R] (x y : R)
  statement: star (x / y) = star x / star y
  proof: by
  apply op_injective
  rw [division_def]; rw [op_div]; rw [mul_comm]; rw [star_mul]; rw [star_inv₀]; rw [op_mul]; rw [op_inv]

中文:
定理 star_div₀
  条件: [带零交换群 R] [StarMul R] (x y : R)
  结论: star (x / y) = star x / star y
  证明: by
  apply op_injective
  rw [division_def]; rw [op_div]; rw [mul_comm]; rw [star_mul]; rw [star_inv₀]; rw [op_mul]; rw [op_inv]

Depends on / 依赖: division_def, mul_comm, op_div, op_injective, op_inv, op_mul, star_mul
-/
theorem star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def]; rw [op_div]; rw [mul_comm]; rw [star_mul]; rw [star_inv₀]; rw [op_mul]; rw [op_inv]

/--
Definition of `starRingOfComm` / `starRingOfComm` 的定义

English:
abbreviation starRingOfComm
  signature: {R : Type*} [CommSemiring R]
  body: { starMulOfComm with
    star_add := fun _ _ => rfl }

中文:
缩写 starRingOfComm
  签名: {R : 类型} [交换半环 R]
  定义体: { starMulOfComm with
    star_add := fun _ _ => rfl }

Depends on / 依赖: starMulOfComm, star_add
-/
abbrev starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }

/--
Instance `Nat.instStarRing` / 实例 `Nat.instStarRing`

English:
instance Nat.instStarRing
  signature: : StarRing Nat
  body: starRingOfComm

中文:
实例 自然数.instStarRing
  签名: : 对合环 自然数
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance Nat.instStarRing : StarRing Nat := starRingOfComm
/--
Instance `Int.instStarRing` / 实例 `Int.instStarRing`

English:
instance Int.instStarRing
  signature: : StarRing Int
  body: starRingOfComm

中文:
实例 整数.instStarRing
  签名: : 对合环 整数
  定义体: starRingOfComm

Depends on / 依赖: starRingOfComm
-/
instance Int.instStarRing : StarRing Int := starRingOfComm
/--
Instance `Nat.instTrivialStar` / 实例 `Nat.instTrivialStar`

English:
instance Nat.instTrivialStar
  signature: : TrivialStar Nat
  body: ⟨fun _ => rfl⟩

中文:
实例 自然数.instTrivialStar
  签名: : TrivialStar 自然数
  定义体: ⟨fun _ => rfl⟩
-/
instance Nat.instTrivialStar : TrivialStar Nat := ⟨fun _ => rfl⟩
/--
Instance `Int.instTrivialStar` / 实例 `Int.instTrivialStar`

English:
instance Int.instTrivialStar
  signature: : TrivialStar Int
  body: ⟨fun _ => rfl⟩

中文:
实例 整数.instTrivialStar
  签名: : TrivialStar 整数
  定义体: ⟨fun _ => rfl⟩
-/
instance Int.instTrivialStar : TrivialStar Int := ⟨fun _ => rfl⟩

/--
Definition of `StarModule` / `StarModule` 的定义

English:
class StarModule
  parameters: (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A]
  axioms and operations (1):
    - star_smul : forall (r : R) (a : A), star (r • a) = star r • star a

中文:
类 对合模
  参数: (R : 类型u) (A : 类型v) [对合 R] [对合 A] [标量乘法 R A]
  公理与运算 (1 个):
    - star_smul : 对任意 (r : R) (a : A), star (r • a) = star r • star a
-/
class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  /-- `star` commutes with scalar multiplication -/
  star_smul : forall (r : R) (a : A), star (r • a) = star r • star a

export StarModule (star_smul)

attribute [simp] star_smul

/--
Instance `StarMul.toStarModule` / 实例 `StarMul.toStarModule`

English:
instance StarMul.toStarModule
  signature: [CommMonoid R] [StarMul R]
  body: ⟨star_mul'⟩

中文:
实例 StarMul.toStarModule
  签名: [交换幺半群 R] [StarMul R]
  定义体: ⟨star_mul'⟩

Depends on / 依赖: star_mul
-/
instance StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R :=
  ⟨star_mul'⟩

/--
Instance `StarAddMonoid.toStarModuleNat` / 实例 `StarAddMonoid.toStarModuleNat`

English:
instance StarAddMonoid.toStarModuleNat
  signature: {α} [AddMonoid α] [StarAddMonoid α]
  body: star_nsmul

中文:
实例 StarAdd幺半群.toStarModule自然数
  签名: {α} [加法幺半群 α] [StarAdd幺半群 α]
  定义体: star_nsmul

Depends on / 依赖: star_nsmul
-/
instance StarAddMonoid.toStarModuleNat {α} [AddMonoid α] [StarAddMonoid α] : StarModule Nat α where
  star_smul := star_nsmul

/--
Instance `StarAddMonoid.toStarModuleInt` / 实例 `StarAddMonoid.toStarModuleInt`

English:
instance StarAddMonoid.toStarModuleInt
  signature: {α} [AddGroup α] [StarAddMonoid α]
  body: star_zsmul

中文:
实例 StarAdd幺半群.toStarModule整数
  签名: {α} [加法群 α] [StarAdd幺半群 α]
  定义体: star_zsmul

Depends on / 依赖: star_zsmul
-/
instance StarAddMonoid.toStarModuleInt {α} [AddGroup α] [StarAddMonoid α] : StarModule Int α where
  star_smul := star_zsmul

namespace RingHomInvPair

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R)
  body: ⟨RingHom.ext star_star, RingHom.ext star_star⟩

中文:
实例 [交换半环
  签名: R] [对合环 R] : RingHomInvPair (starRingEnd R) (starRingEnd R)
  定义体: ⟨RingHom.ext star_star, RingHom.ext star_star⟩

Depends on / 依赖: RingHom, RingHom.ext, star_star
-/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

/--
Definition of `StarHomClass` / `StarHomClass` 的定义

English:
class StarHomClass
  parameters: (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S]
  axioms and operations (1):
    - map_star : forall (f : F) (r : R), f (star r) = star (f r)

中文:
类 对合态射类
  参数: (F : 类型) (R S : outParam 类型) [对合 R] [对合 S] [函数状 F R S]
  公理与运算 (1 个):
    - map_star : 对任意 (f : F) (r : R), f (star r) = star (f r)
-/
class StarHomClass (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S] : Prop where
  /-- the maps preserve star -/
  map_star : forall (f : F) (r : R), f (star r) = star (f r)

export StarHomClass (map_star)

end

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul Rˣ
  body: { val := star u
      inv := star ↑u⁻¹
val_inv := (star_mul _ _).symm.trans (congr_arg star u.inv_val).trans star_one _
inv_val := (star_mul _ _).symm.trans (congr_arg star u.val_inv).trans star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]

中文:
实例 :
  签名: StarMul Rˣ
  定义体: { val := star u
      inv := star ↑u⁻¹
val_inv := (star_mul _ _).symm.trans (congr_arg star u.inv_val).trans star_one _
inv_val := (star_mul _ _).symm.trans (congr_arg star u.val_inv).trans star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]

Depends on / 依赖: Units.ext, congr_arg, inv_val, star_involutive, star_mul, star_one, symm.trans, u.inv_val, u.val_inv, val_inv
-/
instance : StarMul Rˣ where
  star u :=
    { val := star u
      inv := star ↑u⁻¹
val_inv := (star_mul _ _).symm.trans (congr_arg star u.inv_val).trans star_one _
inv_val := (star_mul _ _).symm.trans (congr_arg star u.val_inv).trans star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: (u : Rˣ)
  statement: ↑(star u) = (star ↑u : R)
  proof: rfl

@[simp]

中文:
定理 coe_star
  条件: (u : Rˣ)
  结论: ↑(star u) = (star ↑u : R)
  证明: rfl

@[simp]
-/
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl

@[simp]
/--
theorem `coe_star_inv` / 定理 `coe_star_inv`

English:
theorem coe_star_inv
  given: (u : Rˣ)
  statement: ↑(star u)⁻¹ = (star ↑u⁻¹ : R)
  proof: rfl

中文:
定理 coe_star_inv
  条件: (u : Rˣ)
  结论: ↑(star u)⁻¹ = (star ↑u⁻¹ : R)
  证明: rfl
-/
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl

instance {A : Type*} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => star_smul (u : R) a⟩

end Units

@[aesop safe apply]
/--
theorem `IsUnit.star` / 定理 `IsUnit.star`

English:
theorem IsUnit.star
  given: [Monoid R] [StarMul R] {a : R}
  statement: IsUnit a -> IsUnit (star a)

中文:
定理 是单位.star
  条件: [幺半群 R] [StarMul R] {a : R}
  结论: 是单位 a -> 是单位 (star a)
-/
protected theorem IsUnit.star [Monoid R] [StarMul R] {a : R} : IsUnit a -> IsUnit (star a)
  | ⟨u, hu⟩ => ⟨Star.star u, hu ▸ rfl⟩

@[simp, grind =]
/--
theorem `isUnit_star` / 定理 `isUnit_star`

English:
theorem isUnit_star
  given: [Monoid R] [StarMul R] {a : R}
  statement: IsUnit (star a) ↔ IsUnit a
  proof: ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

@[grind _=_]

中文:
定理 isUnit_star
  条件: [幺半群 R] [StarMul R] {a : R}
  结论: 是单位 (star a) ↔ 是单位 a
  证明: ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

@[grind _=_]

Depends on / 依赖: IsUnit, IsUnit.star, h.star, star_star
-/
theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩

@[grind _=_]
/--
theorem `Ring.inverse_star` / 定理 `Ring.inverse_star`

English:
theorem Ring.inverse_star
  given: [Semiring R] [StarRing R] (a : R)
  proof: by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]; rw [← Units.coe_star]; rw [Ring.inverse_unit]; rw [← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha]; rw [Ring.inverse_non_unit _ (mt isUnit_star.mp ha)]; rw [star_zero]

中文:
定理 环.inverse_star
  条件: [半环 R] [对合环 R] (a : R)
  证明: by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]; rw [← Units.coe_star]; rw [Ring.inverse_unit]; rw [← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha]; rw [Ring.inverse_non_unit _ (mt isUnit_star.mp ha)]; rw [star_zero]

Depends on / 依赖: IsUnit, Ring.inverse_non_unit, Ring.inverse_unit, Units.coe_star, Units.coe_star_inv, coe_star, coe_star_inv, inverse_non_unit, inverse_unit, isUnit_star, isUnit_star.mp, star_zero
-/
theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    (star a)⁻¹ʳ = star (a⁻¹ʳ) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit]; rw [← Units.coe_star]; rw [Ring.inverse_unit]; rw [← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha]; rw [Ring.inverse_non_unit _ (mt isUnit_star.mp ha)]; rw [star_zero]

/--
Instance `Invertible.star` / 实例 `Invertible.star`

English:
instance Invertible.star
  signature: {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r]
  body: Star.star (⅟r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]

中文:
实例 可逆.star
  签名: {R : 类型} [MulOne类 R] [StarMul R] (r : R) [可逆 r]
  定义体: Star.star (⅟r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
-/
protected instance Invertible.star {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := Star.star (⅟r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]

/--
theorem `star_invOf` / 定理 `star_invOf`

English:
theorem star_invOf
  statement: {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
  proof: by
  rw [← mul_one (star (⅟r))]; rw [← mul_invOf_self (star r)]; rw [← mul_assoc]; rw [← star_mul]
  simp

中文:
定理 star_invOf
  结论: {R : 类型} [幺半群 R] [StarMul R] (r : R) [可逆 r]
  证明: by
  rw [← mul_one (star (⅟r))]; rw [← mul_invOf_self (star r)]; rw [← mul_assoc]; rw [← star_mul]
  simp

Depends on / 依赖: mul_assoc, mul_invOf_self, mul_one, star_mul
-/
theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟r) = ⅟(star r) := by
  rw [← mul_one (star (⅟r))]; rw [← mul_invOf_self (star r)]; rw [← mul_assoc]; rw [← star_mul]
  simp

section Regular

/--
theorem `IsLeftRegular.star` / 定理 `IsLeftRegular.star`

English:
theorem IsLeftRegular.star
  given: [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x)
  proof: fun a b h => star_injective hx by simpa using congr_arg Star.star h

中文:
定理 IsLeftRegular.star
  条件: [乘法 R] [StarMul R] {x : R} (hx : IsLeftRegular x)
  证明: fun a b h => star_injective hx by simpa using congr_arg Star.star h
-/
protected theorem IsLeftRegular.star [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x) :
    IsRightRegular (star x) :=
fun a b h => star_injective hx by simpa using congr_arg Star.star h

/--
theorem `IsRightRegular.star` / 定理 `IsRightRegular.star`

English:
theorem IsRightRegular.star
  given: [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x)
  proof: fun a b h => star_injective hx by simpa using congr_arg Star.star h

中文:
定理 IsRightRegular.star
  条件: [乘法 R] [StarMul R] {x : R} (hx : IsRightRegular x)
  证明: fun a b h => star_injective hx by simpa using congr_arg Star.star h
-/
protected theorem IsRightRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x) :
    IsLeftRegular (star x) :=
fun a b h => star_injective hx by simpa using congr_arg Star.star h

/--
theorem `IsRegular.star` / 定理 `IsRegular.star`

English:
theorem IsRegular.star
  given: [Mul R] [StarMul R] {x : R} (hx : IsRegular x)
  proof: ⟨hx.right.star, hx.left.star⟩

@[simp]

中文:
定理 是正则.star
  条件: [乘法 R] [StarMul R] {x : R} (hx : 是正则 x)
  证明: ⟨hx.right.star, hx.left.star⟩

@[simp]
-/
protected theorem IsRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRegular x) :
    IsRegular (star x) :=
  ⟨hx.right.star, hx.left.star⟩

@[simp]
/--
theorem `isRightRegular_star_iff` / 定理 `isRightRegular_star_iff`

English:
theorem isRightRegular_star_iff
  given: [Mul R] [StarMul R] {x : R}
  proof: ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]

中文:
定理 isRightRegular_star_iff
  条件: [乘法 R] [StarMul R] {x : R}
  证明: ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]

Depends on / 依赖: h.star, star_star
-/
theorem isRightRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRightRegular (star x) ↔ IsLeftRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
/--
theorem `isLeftRegular_star_iff` / 定理 `isLeftRegular_star_iff`

English:
theorem isLeftRegular_star_iff
  given: [Mul R] [StarMul R] {x : R}
  proof: ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]

中文:
定理 isLeftRegular_star_iff
  条件: [乘法 R] [StarMul R] {x : R}
  证明: ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]

Depends on / 依赖: h.star, star_star
-/
theorem isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsLeftRegular (star x) ↔ IsRightRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
/--
theorem `isRegular_star_iff` / 定理 `isRegular_star_iff`

English:
theorem isRegular_star_iff
  given: [Mul R] [StarMul R] {x : R}
  proof: by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isRightRegular_star_iff]; rw [isLeftRegular_star_iff]; rw [and_comm]

中文:
定理 isRegular_star_iff
  条件: [乘法 R] [StarMul R] {x : R}
  证明: by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isRightRegular_star_iff]; rw [isLeftRegular_star_iff]; rw [and_comm]

Depends on / 依赖: and_comm, isLeftRegular_star_iff, isRegular_iff, isRightRegular_star_iff
-/
theorem isRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRegular (star x) ↔ IsRegular x := by
  rw [isRegular_iff]; rw [isRegular_iff]; rw [isRightRegular_star_iff]; rw [isLeftRegular_star_iff]; rw [and_comm]

end Regular

namespace Function.Injective

variable {S : Type v} (f : R -> S)

/--
Definition of `involutiveStar` / `involutiveStar` 的定义

English:
abbreviation involutiveStar
  signature: [Star R] [InvolutiveStar S] (hf : Injective f)
  body: hf by rw [star, star, star_star]

中文:
缩写 involutiveStar
  签名: [对合 R] [InvolutiveStar S] (hf : 单射 f)
  定义体: hf by rw [star, star, star_star]
-/
protected abbrev involutiveStar [Star R] [InvolutiveStar S] (hf : Injective f)
    (star : forall x, f (star x) = star (f x)) : InvolutiveStar R where
star_involutive r := hf by rw [star, star, star_star]

/--
Definition of `starMul` / `starMul` 的定义

English:
abbreviation starMul
  signature: [Star R] [Mul R] [Mul S] [StarMul S] (hf : Injective f)
  body: hf.involutiveStar _ star
star_mul x y := hf by rw [star, mul, star_mul, mul, star, star]

中文:
缩写 starMul
  签名: [对合 R] [乘法 R] [乘法 S] [StarMul S] (hf : 单射 f)
  定义体: hf.involutiveStar _ star
star_mul x y := hf by rw [star, mul, star_mul, mul, star, star]
-/
protected abbrev starMul [Star R] [Mul R] [Mul S] [StarMul S] (hf : Injective f)
    (star : forall x, f (star x) = star (f x)) (mul : forall x y, f (x * y) = f x * f y) :
    StarMul R where
  toInvolutiveStar := hf.involutiveStar _ star
star_mul x y := hf by rw [star, mul, star_mul, mul, star, star]

/--
Definition of `starAddMonoid` / `starAddMonoid` 的定义

English:
abbreviation starAddMonoid
  signature: [Star R] [AddMonoid R] [AddMonoid S] [StarAddMonoid S]
  body: hf.involutiveStar f star
star_add x y := hf by rw [star, add, star_add, add, star, star]

中文:
缩写 starAddMonoid
  签名: [对合 R] [加法幺半群 R] [加法幺半群 S] [StarAdd幺半群 S]
  定义体: hf.involutiveStar f star
star_add x y := hf by rw [star, add, star_add, add, star, star]
-/
protected abbrev starAddMonoid [Star R] [AddMonoid R] [AddMonoid S] [StarAddMonoid S]
    (hf : Injective f) (star : forall x, f (star x) = star (f x)) (add : forall x y, f (x + y) = f x + f y) :
    StarAddMonoid R where
  toInvolutiveStar := hf.involutiveStar f star
star_add x y := hf by rw [star, add, star_add, add, star, star]

/--
Definition of `starRing` / `starRing` 的定义

English:
abbreviation starRing
  signature: [Star R] [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  body: { hf.starMul f star mul, hf.starAddMonoid f star add with }

中文:
缩写 starRing
  签名: [对合 R] [非幺非结合半环 R] [非幺非结合半环 S]
  定义体: { hf.starMul f star mul, hf.starAddMonoid f star add with }
-/
protected abbrev starRing [Star R] [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    [StarRing S] (hf : Injective f) (star : forall x, f (star x) = star (f x))
    (add : forall x y, f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y) :
    StarRing R :=
  { hf.starMul f star mul, hf.starAddMonoid f star add with }

/--
lemma `starModule` / 引理 `starModule`

English:
lemma starModule
  statement: (𝕜 : Type*) [Star 𝕜] [SMul 𝕜 R]
  proof: hf by rw [star, smul, star_smul, smul, star]

中文:
引理 starModule
  结论: (𝕜 : 类型) [对合 𝕜] [标量乘法 𝕜 R]
  证明: hf by rw [star, smul, star_smul, smul, star]
-/
protected lemma starModule (𝕜 : Type*) [Star 𝕜] [SMul 𝕜 R]
    [Star R] [SMul 𝕜 S] [Star S] [StarModule 𝕜 S] (hf : Injective f)
    (star : forall x, f (star x) = star (f x)) (smul : forall (r : 𝕜) x, f (r • x) = r • f x) :
    StarModule 𝕜 R where
star_smul r x := hf by rw [star, smul, star_smul, smul, star]

end Function.Injective

namespace MulOpposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] : Star Rᵐᵒᵖ where star r
  body: op (star r.unop)

@[simp]

中文:
实例 [对合
  签名: R] : 对合 Rᵐᵒᵖ where star r
  定义体: op (star r.unop)

@[simp]

Depends on / 依赖: r.unop
-/
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)

@[simp]
/--
theorem `unop_star` / 定理 `unop_star`

English:
theorem unop_star
  given: [Star R] (r : Rᵐᵒᵖ)
  statement: unop (star r) = star (unop r)
  proof: rfl

@[simp]

中文:
定理 unop_star
  条件: [对合 R] (r : Rᵐᵒᵖ)
  结论: unop (star r) = star (unop r)
  证明: rfl

@[simp]
-/
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl

@[simp]
/--
theorem `op_star` / 定理 `op_star`

English:
theorem op_star
  given: [Star R] (r : R)
  statement: op (star r) = star (op r)
  proof: rfl

中文:
定理 op_star
  条件: [对合 R] (r : R)
  结论: op (star r) = star (op r)
  证明: rfl
-/
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: R] : InvolutiveStar Rᵐᵒᵖ where
  body: unop_injective (star_star r.unop)

中文:
实例 [InvolutiveStar
  签名: R] : InvolutiveStar Rᵐᵒᵖ where
  定义体: unop_injective (star_star r.unop)

Depends on / 依赖: Nat.cast_mul, cast_mul, even_or_odd, even_two_mul, if_neg, if_pos, mul_div_cancel_left, n.even_or_odd, n.mul_div_cancel_left, n.not_even_two_mul_add_one, not_even_two_mul_add_one, r.unop, right_ne_zero_of_mul, star_star, two_pos, unop_injective
-/
instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ where
  star_involutive r := unop_injective (star_star r.unop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [StarMul R] : StarMul Rᵐᵒᵖ where
  body: unop_injective (star_mul y.unop x.unop)

中文:
实例 [乘法
  签名: R] [StarMul R] : StarMul Rᵐᵒᵖ where
  定义体: unop_injective (star_mul y.unop x.unop)

Depends on / 依赖: W.coeff_pre, W.natDegree_pre, _ne_zero, natDegree_eq_of_le_of_coeff_ne_zero, star_mul, unop_injective, x.unop, y.unop
-/
instance [Mul R] [StarMul R] : StarMul Rᵐᵒᵖ where
  star_mul x y := unop_injective (star_mul y.unop x.unop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  body: unop_injective (star_add x.unop y.unop)

中文:
实例 [加法幺半群
  签名: R] [StarAdd幺半群 R] : StarAdd幺半群 Rᵐᵒᵖ where
  定义体: unop_injective (star_add x.unop y.unop)

Depends on / 依赖: AtLeastTwo, Nat.AtLeastTwo.prop.trans, Nat.div_pos_iff, Nat.pow_le_pow_left, Nat.sub_le_sub_right, W.natDegree_pre, div_pos_iff, pow_le_pow_left, simp_rw, split_ifs, star_add, sub_le_sub_right, true_and, unop_injective, x.unop, y.unop, zero_lt_two
-/
instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] [StarRing R] : StarRing Rᵐᵒᵖ where
  body: unop_injective (star_add x.unop y.unop)

中文:
实例 [非幺半环
  签名: R] [对合环 R] : 对合环 Rᵐᵒᵖ where
  定义体: unop_injective (star_add x.unop y.unop)

Depends on / 依赖: star_add, unop_injective, x.unop, y.unop
-/
instance [NonUnitalSemiring R] [StarRing R] : StarRing Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

instance {M : Type*} [Star R] [Star M] [SMul R M] [StarModule R M] :
    StarModule R Mᵐᵒᵖ where
  star_smul r x := unop_injective (star_smul r x.unop)

end MulOpposite

/--
Instance `StarSemigroup.toOpposite_starModule` / 实例 `StarSemigroup.toOpposite_starModule`

English:
instance StarSemigroup.toOpposite_starModule
  signature: [CommMonoid R] [StarMul R]
  body: ⟨fun r s => star_mul' s r.unop⟩

中文:
实例 StarSemigroup.toOpposite_starModule
  签名: [交换幺半群 R] [StarMul R]
  定义体: ⟨fun r s => star_mul' s r.unop⟩

Depends on / 依赖: W.natDegree_pre, _pos, ne_zero_of_natDegree_gt, r.unop, star_mul
-/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] :
    StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
