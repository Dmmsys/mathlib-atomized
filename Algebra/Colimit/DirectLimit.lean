/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.StarRingHom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of algebraic structures

We introduce all kinds of algebraic instances on `DirectLimit`, and specialize to the cases
of modules and rings, showing that they are indeed colimits in the respective categories.

## Implementation notes

The first 400 lines are boilerplate code that defines algebraic instances on `DirectLimit`
from magma (`Mul`) to `Field`. To make everything "hom-polymorphic", we work with `DirectedSystem`s
of `FunLike`s rather than plain unbundled functions, and we use algebraic hom typeclasses
(e.g. `LinearMapClass`, `RingHomClass`) everywhere.

In `Mathlib/Algebra/Colimit/Module.lean` and `Mathlib/Algebra/Colimit/Ring.lean`,
`Module.DirectLimit`, `AddCommGroup.DirectLimit` and `Ring.DirectLimit`
are defined as quotients of the universal objects (`DirectSum` and `FreeCommRing`).
These definitions are more general and suitable for arbitrary colimits, but do not
immediately provide criteria to determine when two elements in a component are equal
in the direct limit.

On the other hand, the `DirectLimit` in this file is only defined for directed systems
and does not work for general colimits, but the equivalence relation defining `DirectLimit`
is very explicit. For colimits of directed systems there is no need to construct the
universal object for each type of algebraic structure; the same type `DirectLimit` simply
works for all of them. This file is therefore more general than the `Module` and `Ring`
files in terms of the variety of algebraic structures supported.

So far we only show that `DirectLimit` is the colimit in the following categories:

* modules
* non-unital semirings
* rings
* (non-unital) star rings
* R-algebras

but for the other algebraic structures the constructions and proofs will be easy following
the same pattern. Since any two colimits are isomorphic, this allows us to golf proofs of
equality criteria for `Module/AddCommGroup/Ring.DirectLimit`.
-/

@[expose] public section

suppress_compilation

variable {R ι : Type*} [Preorder ι] {G : ι -> Type*} {H : ι -> Type*} {C : Type*}
variable {T : forall ⦃i j : ι⦄, i <= j -> Type*} {f : forall _ _ h, T h}
variable [forall i j (h : i <= j), FunLike (T h) (G i) (G j)] [forall i, FunLike (H i) (G i) C]
variable [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

namespace DirectLimit

section ZeroOne
variable [Nonempty ι] [forall i, One (G i)] [One C] [forall i, OneHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (DirectLimit G f)
  body: map₀ f fun _ => 1

中文:
实例 :
  签名: One (DirectLimit G f)
  定义体: map₀ f fun _ => 1
-/
@[to_additive] instance : One (DirectLimit G f) where
  one := map₀ f fun _ => 1

variable [forall i j h, OneHomClass (T h) (G i) (G j)]

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  given: (i)
  statement: (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧
  proof: map₀_def _ _ (fun _ _ _ => map_one _) _

中文:
定理 one_def
  条件: (i)
  结论: (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧
  证明: map₀_def _ _ (fun _ _ _ => map_one _) _
-/
@[to_additive] theorem one_def (i) : (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => map_one _) _

/--
theorem `exists_eq_one` / 定理 `exists_eq_one`

English:
theorem exists_eq_one
  given: (x)
  proof: by
  rw [one_def x.1]; rw [Quotient.eq]
  exact ⟨fun ⟨i, h, _, eq⟩ => ⟨i, h, eq.trans (map_one _)⟩,
    fun ⟨i, h, eq⟩ => ⟨i, h, h, eq.trans (map_one _).symm⟩⟩

@[to_additive (attr := simp)]

中文:
定理 exists_eq_one
  条件: (x)
  证明: by
  rw [one_def x.1]; rw [Quotient.eq]
  exact ⟨fun ⟨i, h, _, eq⟩ => ⟨i, h, eq.trans (map_one _)⟩,
    fun ⟨i, h, eq⟩ => ⟨i, h, h, eq.trans (map_one _).symm⟩⟩

@[to_additive (attr := simp)]
-/
@[to_additive] theorem exists_eq_one (x) :
    ⟦x⟧ = (1 : DirectLimit G f) ↔ exists i h, f x.1 i h x.2 = 1 := by
  rw [one_def x.1]; rw [Quotient.eq]
  exact ⟨fun ⟨i, h, _, eq⟩ => ⟨i, h, eq.trans (map_one _)⟩,
    fun ⟨i, h, eq⟩ => ⟨i, h, h, eq.trans (map_one _).symm⟩⟩

@[to_additive (attr := simp)]
/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  given: (g : forall i, H i) (h)
  proof: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [one_def]; rw [lift_def]; rw [map_one (g i)]

@[to_additive (attr := simp)]

中文:
定理 lift_one
  条件: (g : 对任意 i, H i) (h)
  证明: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [one_def]; rw [lift_def]; rw [map_one (g i)]

@[to_additive (attr := simp)]

Depends on / 依赖: Nonempty, lift_def, map_one, one_def
-/
theorem lift_one (g : forall i, H i) (h) :
    DirectLimit.lift f (g ·) h (1 : DirectLimit G f) = (1 : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [one_def]; rw [lift_def]; rw [map_one (g i)]

@[to_additive (attr := simp)]
/--
lemma `map₀_one` / 引理 `map₀_one`

English:
lemma map₀_one
  statement: map₀ f (1 : forall i, G i) = 1
  proof: by rw [map₀, Pi.one_apply, one_def]

中文:
引理 map₀_one
  结论: map₀ f (1 : 对任意 i, G i) = 1
  证明: by rw [map₀, Pi.one_apply, one_def]

Depends on / 依赖: Pi.one_apply, one_apply, one_def
-/
lemma map₀_one : map₀ f (1 : forall i, G i) = 1 := by rw [map₀, Pi.one_apply, one_def]

end ZeroOne

section Star
variable [forall i, Star (G i)] [Star C]
variable [forall i j h, StarHomClass (T h) (G i) (G j)] [forall i, StarHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (DirectLimit G f)
  body: .map f f (fun _ x => star x) (fun i j h x => map_star (f i j h) x)

中文:
实例 :
  签名: Star (DirectLimit G f)
  定义体: .map f f (fun _ x => star x) (fun i j h x => map_star (f i j h) x)

Depends on / 依赖: map_star
-/
instance : Star (DirectLimit G f) where
  star := .map f f (fun _ x => star x) (fun i j h x => map_star (f i j h) x)

/--
lemma `star_def` / 引理 `star_def`

English:
lemma star_def
  given: (i : ι) (x : G i)
  proof: by
  rfl

@[simp]

中文:
引理 star_def
  条件: (i : ι) (x : G i)
  证明: by
  rfl

@[simp]
-/
lemma star_def (i : ι) (x : G i) :
    star ⟦⟨i, x⟩⟧ = (⟦⟨i, star x⟩⟧ : DirectLimit G f) := by
  rfl

@[simp]
/--
theorem `lift_star` / 定理 `lift_star`

English:
theorem lift_star
  given: (g : forall i, H i) (h) (x : DirectLimit G f)
  proof: x.induction _ fun i x => by simp_rw [star_def, lift_def, map_star (g i)]

中文:
定理 lift_star
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f)
  证明: x.induction _ fun i x => by simp_rw [star_def, lift_def, map_star (g i)]

Depends on / 依赖: lift_def, map_star, simp_rw, star_def, x.induction
-/
theorem lift_star (g : forall i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (star x) = star (DirectLimit.lift f (g ·) h x) :=
  x.induction _ fun i x => by simp_rw [star_def, lift_def, map_star (g i)]

end Star

section InvolutiveStar
variable [forall i, InvolutiveStar (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveStar (DirectLimit G f)
  body: by
    apply DirectLimit.induction
    intro i x
    rw [star_def]; rw [star_def]; rw [star_star]

中文:
实例 :
  签名: InvolutiveStar (DirectLimit G f)
  定义体: by
    apply DirectLimit.induction
    intro i x
    rw [star_def]; rw [star_def]; rw [star_star]

Depends on / 依赖: DirectLimit, DirectLimit.induction, star_def, star_star
-/
instance : InvolutiveStar (DirectLimit G f) where
  star_involutive := by
    apply DirectLimit.induction
    intro i x
    rw [star_def]; rw [star_def]; rw [star_star]

end InvolutiveStar

section AddMul
variable [forall i, Mul (G i)] [Mul C]
variable [forall i j h, MulHomClass (T h) (G i) (G j)] [forall i, MulHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (DirectLimit G f)
  body: map₂ f f f (fun _ => (· * ·)) fun _ _ _ => map_mul _

中文:
实例 :
  签名: Mul (DirectLimit G f)
  定义体: map₂ f f f (fun _ => (· * ·)) fun _ _ _ => map_mul _
-/
@[to_additive] instance : Mul (DirectLimit G f) where
  mul := map₂ f f f (fun _ => (· * ·)) fun _ _ _ => map_mul _

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (i) (x y : G i)
  proof: map₂_def ..

@[to_additive (attr := simp)]

中文:
定理 mul_def
  条件: (i) (x y : G i)
  证明: map₂_def ..

@[to_additive (attr := simp)]
-/
@[to_additive] theorem mul_def (i) (x y : G i) :
    ⟦⟨i, x⟩⟧ * ⟦⟨i, y⟩⟧ = (⟦⟨i, x * y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

@[to_additive (attr := simp)]
/--
theorem `lift_mul` / 定理 `lift_mul`

English:
theorem lift_mul
  given: (g : forall i, H i) (h) (x y : DirectLimit G f)
  proof: DirectLimit.induction₂ _ (fun i x y => by simp_rw [mul_def, lift_def, map_mul (g i)]) x y

@[to_additive (attr := simp)]

中文:
定理 lift_mul
  条件: (g : 对任意 i, H i) (h) (x y : DirectLimit G f)
  证明: DirectLimit.induction₂ _ (fun i x y => by simp_rw [mul_def, lift_def, map_mul (g i)]) x y

@[to_additive (attr := simp)]

Depends on / 依赖: DirectLimit, DirectLimit.induction, lift_def, map_mul, mul_def, simp_rw
-/
theorem lift_mul (g : forall i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x * y) =
      DirectLimit.lift f (g ·) h x * DirectLimit.lift f (g ·) h y :=
  DirectLimit.induction₂ _ (fun i x y => by simp_rw [mul_def, lift_def, map_mul (g i)]) x y

@[to_additive (attr := simp)]
/--
lemma `map₀_mul` / 引理 `map₀_mul`

English:
lemma map₀_mul
  given: [Nonempty ι] (r s : forall i, G i)
  statement: map₀ f (r * s) = map₀ f r * map₀ f s
  proof: by
  simp_rw [map₀, Pi.mul_apply, mul_def]

中文:
引理 map₀_mul
  条件: [Nonempty ι] (r s : 对任意 i, G i)
  结论: map₀ f (r * s) = map₀ f r * map₀ f s
  证明: by
  simp_rw [map₀, Pi.mul_apply, mul_def]

Depends on / 依赖: Pi.mul_apply, mul_apply, mul_def, simp_rw
-/
lemma map₀_mul [Nonempty ι] (r s : forall i, G i) : map₀ f (r * s) = map₀ f r * map₀ f s := by
  simp_rw [map₀, Pi.mul_apply, mul_def]

end AddMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommMagma (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
  body: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, mul_comm]

中文:
实例 [forall
  签名: i, CommMagma (G i)] [对任意 i j h, MulHomClass (T h) (G i) (G j)] :
  定义体: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, mul_comm]
-/
@[to_additive] instance [forall i, CommMagma (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
    CommMagma (DirectLimit G f) where
  mul_comm := DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, mul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Semigroup (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
  body: DirectLimit.induction₃ _ fun i _ _ _ => by simp_rw [mul_def, mul_assoc]

中文:
实例 [forall
  签名: i, Semigroup (G i)] [对任意 i j h, MulHomClass (T h) (G i) (G j)] :
  定义体: DirectLimit.induction₃ _ fun i _ _ _ => by simp_rw [mul_def, mul_assoc]
-/
@[to_additive] instance [forall i, Semigroup (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
    Semigroup (DirectLimit G f) where
  mul_assoc := DirectLimit.induction₃ _ fun i _ _ _ => by simp_rw [mul_def, mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommSemigroup (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
  body: mul_comm

中文:
实例 [forall
  签名: i, CommSemigroup (G i)] [对任意 i j h, MulHomClass (T h) (G i) (G j)] :
  定义体: mul_comm
-/
@[to_additive] instance [forall i, CommSemigroup (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)] :
    CommSemigroup (DirectLimit G f) where
  mul_comm := mul_comm

section StarMul
variable [forall i, Mul (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)]
variable [forall i, StarMul (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (DirectLimit G f)
  body: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, star_def, star_mul, mul_def]

中文:
实例 :
  签名: StarMul (DirectLimit G f)
  定义体: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, star_def, star_mul, mul_def]

Depends on / 依赖: DirectLimit, DirectLimit.induction, mul_def, simp_rw, star_def, star_mul
-/
instance : StarMul (DirectLimit G f) where
  star_mul := DirectLimit.induction₂ _ fun i _ _ => by simp_rw [mul_def, star_def, star_mul, mul_def]

end StarMul

section SMul
variable [forall i, SMul R (G i)] [SMul R C]
variable [forall i j h, MulActionHomClass (T h) R (G i) (G j)] [forall i, MulActionHomClass (H i) R (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (DirectLimit G f)
  body: map _ _ (fun _ => (r • ·)) fun _ _ _ => map_smul _ r

中文:
实例 :
  签名: SMul R (DirectLimit G f)
  定义体: map _ _ (fun _ => (r • ·)) fun _ _ _ => map_smul _ r
-/
@[to_additive] instance : SMul R (DirectLimit G f) where
  smul r := map _ _ (fun _ => (r • ·)) fun _ _ _ => map_smul _ r

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (i x) (r : R)
  statement: r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_def
  条件: (i x) (r : R)
  结论: r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f)
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: A.hom.hom, RingHom, RingHom.toAlgebra, toAlgebra
-/
@[to_additive] theorem smul_def (i x) (r : R) : r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_smul` / 定理 `lift_smul`

English:
theorem lift_smul
  given: (g : forall i, H i) (h) (r : R) (x : DirectLimit G f)
  proof: x.induction _ fun i x => by simp_rw [smul_def, lift_def, map_smul (g i)]

中文:
定理 lift_smul
  条件: (g : 对任意 i, H i) (h) (r : R) (x : DirectLimit G f)
  证明: x.induction _ fun i x => by simp_rw [smul_def, lift_def, map_smul (g i)]

Depends on / 依赖: lift_def, map_smul, simp_rw, smul_def, x.induction
-/
theorem lift_smul (g : forall i, H i) (h) (r : R) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (r • x) = r • DirectLimit.lift f (g ·) h x :=
  x.induction _ fun i x => by simp_rw [smul_def, lift_def, map_smul (g i)]

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [forall i, Star (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]
  body: DirectLimit.induction _ fun i x => by
    simp_rw [star_def, smul_def, ← star_smul, star_def]

中文:
实例 [Star
  签名: R] [对任意 i, Star (G i)] [对任意 i j h, StarHomClass (T h) (G i) (G j)]
  定义体: DirectLimit.induction _ fun i x => by
    simp_rw [star_def, smul_def, ← star_smul, star_def]

Depends on / 依赖: DirectLimit, DirectLimit.induction, simp_rw, smul_def, star_def, star_smul
-/
instance [Star R] [forall i, Star (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]
    [forall i, SMul R (G i)] [forall i j h, MulActionHomClass (T h) R (G i) (G j)]
    [forall i, StarModule R (G i)] :
    StarModule R (DirectLimit G f) where
  star_smul r := DirectLimit.induction _ fun i x => by
    simp_rw [star_def, smul_def, ← star_smul, star_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [forall i, MulAction R (G i)]
  body: DirectLimit.induction _ fun i _ => by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, mul_smul]

中文:
实例 [Monoid
  签名: R] [对任意 i, MulAction R (G i)]
  定义体: DirectLimit.induction _ fun i _ => by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, mul_smul]
-/
@[to_additive] instance [Monoid R] [forall i, MulAction R (G i)]
    [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulAction R (DirectLimit G f) where
  one_smul := DirectLimit.induction _ fun i _ => by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, mul_smul]

variable [Nonempty ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, MulOneClass (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
  body: DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, mul_one]

中文:
实例 [forall
  签名: i, MulOneClass (G i)] [对任意 i j h, MonoidHomClass (T h) (G i) (G j)] :
  定义体: DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, mul_one]
-/
@[to_additive] instance [forall i, MulOneClass (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
    MulOneClass (DirectLimit G f) where
  one_mul := DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ => by simp_rw [one_def i, mul_def, mul_one]

variable (f) in
/-- `map₀` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `map₀` as an `AddMonoidHom`. -/]
/--
Definition of `map₀MonoidHom` / `map₀MonoidHom` 的定义

English:
definition map₀MonoidHom
  signature: [forall i, MulOneClass (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)]
  body: map₀ _ x
  map_one' := map₀_one
  map_mul' := map₀_mul

中文:
定义 map₀MonoidHom
  签名: [对任意 i, MulOneClass (G i)] [对任意 i j h, MonoidHomClass (T h) (G i) (G j)]
  定义体: map₀ _ x
  map_one' := map₀_one
  map_mul' := map₀_mul
-/
def map₀MonoidHom [forall i, MulOneClass (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
    (forall i, G i) ->* DirectLimit G f where
  toFun x := map₀ _ x
  map_one' := map₀_one
  map_mul' := map₀_mul

section Monoid
variable [forall i, Monoid (G i)] [Monoid C]
variable [forall i j h, MonoidHomClass (T h) (G i) (G j)] [forall i, MonoidHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (DirectLimit G f)
  body: one_mul
  mul_one := mul_one
  npow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.h

中文:
实例 :
  签名: Monoid (DirectLimit G f)
  定义体: one_mul
  mul_one := mul_one
  npow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.h
-/
@[to_additive] instance : Monoid (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  npow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_succ, mul_def]

/--
theorem `npow_def` / 定理 `npow_def`

English:
theorem npow_def
  given: (i x) (n : Nat)
  statement: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 npow_def
  条件: (i x) (n : 自然数)
  结论: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] theorem npow_def (i x) (n : Nat) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_npow` / 定理 `lift_npow`

English:
theorem lift_npow
  given: (g : forall i, H i) (h) (x : DirectLimit G f) (n : Nat)
  proof: x.induction _ fun i x => by simp_rw [npow_def, lift_def, map_pow (g i)]

中文:
定理 lift_npow
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f) (n : 自然数)
  证明: x.induction _ fun i x => by simp_rw [npow_def, lift_def, map_pow (g i)]

Depends on / 依赖: lift_def, map_pow, npow_def, simp_rw, x.induction
-/
theorem lift_npow (g : forall i, H i) (h) (x : DirectLimit G f) (n : Nat) :
    DirectLimit.lift f (g ·) h (x ^ n) = DirectLimit.lift f (g ·) h x ^ n :=
  x.induction _ fun i x => by simp_rw [npow_def, lift_def, map_pow (g i)]

end Monoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommMonoid (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
  body: mul_comm

中文:
实例 [forall
  签名: i, CommMonoid (G i)] [对任意 i j h, MonoidHomClass (T h) (G i) (G j)] :
  定义体: mul_comm
-/
@[to_additive] instance [forall i, CommMonoid (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommMonoid (DirectLimit G f) where
  mul_comm := mul_comm

section StarAddMonoid
variable [forall i, AddMonoid (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [forall i, StarAddMonoid (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarAddMonoid (DirectLimit G f)
  body: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [add_def, star_def, star_add, add_def]

中文:
实例 :
  签名: StarAddMonoid (DirectLimit G f)
  定义体: DirectLimit.induction₂ _ fun i _ _ => by simp_rw [add_def, star_def, star_add, add_def]

Depends on / 依赖: DirectLimit, DirectLimit.induction, add_def, simp_rw, star_add, star_def
-/
instance : StarAddMonoid (DirectLimit G f) where
  star_add := DirectLimit.induction₂ _ fun i _ _ => by simp_rw [add_def, star_def, star_add, add_def]

end StarAddMonoid

section Group
variable [forall i, Group (G i)] [Group C]
variable [forall i j h, MonoidHomClass (T h) (G i) (G j)] [forall i, MonoidHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (DirectLimit G f)
  body: map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, di

中文:
实例 :
  签名: Group (DirectLimit G f)
  定义体: map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, di
-/
@[to_additive] instance : Group (DirectLimit G f) where
  inv := map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow, map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x => by
    simp_rw [HPow.hPow, Pow.pow, map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x => by
    simp_rw [HPow.hPow, Pow.pow, map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_mul_cancel := DirectLimit.induction _ fun i _ => by
    simp_rw [map_def, mul_def, inv_mul_cancel, one_def i]

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (i x)
  statement: (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f)
  proof: rfl

中文:
定理 inv_def
  条件: (i x)
  结论: (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f)
  证明: rfl
-/
@[to_additive] theorem inv_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

/--
theorem `div_def` / 定理 `div_def`

English:
theorem div_def
  given: (i x y)
  statement: ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f)
  proof: map₂_def ..

中文:
定理 div_def
  条件: (i x y)
  结论: ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f)
  证明: map₂_def ..
-/
@[to_additive] theorem div_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

/--
theorem `zpow_def` / 定理 `zpow_def`

English:
theorem zpow_def
  given: (i x) (n : Int)
  statement: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 zpow_def
  条件: (i x) (n : 整数)
  结论: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] theorem zpow_def (i x) (n : Int) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_inv` / 定理 `lift_inv`

English:
theorem lift_inv
  given: (g : forall i, H i) (h) (x : DirectLimit G f)
  proof: x.induction _ fun i x => by simp_rw [inv_def, lift_def, map_inv (g i)]

@[to_additive (attr := simp)]

中文:
定理 lift_inv
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f)
  证明: x.induction _ fun i x => by simp_rw [inv_def, lift_def, map_inv (g i)]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_def, lift_def, map_inv, simp_rw, x.induction
-/
theorem lift_inv (g : forall i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹ :=
  x.induction _ fun i x => by simp_rw [inv_def, lift_def, map_inv (g i)]

@[to_additive (attr := simp)]
/--
theorem `lift_div` / 定理 `lift_div`

English:
theorem lift_div
  given: (g : forall i, H i) (h) (x y : DirectLimit G f)
  proof: DirectLimit.induction₂ _ (fun i x y => by simp_rw [div_def, lift_def, map_div (g i)]) x y

@[to_additive (attr := simp)]

中文:
定理 lift_div
  条件: (g : 对任意 i, H i) (h) (x y : DirectLimit G f)
  证明: DirectLimit.induction₂ _ (fun i x y => by simp_rw [div_def, lift_def, map_div (g i)]) x y

@[to_additive (attr := simp)]

Depends on / 依赖: DirectLimit, DirectLimit.induction, div_def, lift_def, map_div, simp_rw
-/
theorem lift_div (g : forall i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x / y) =
      (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·) h y) :=
  DirectLimit.induction₂ _ (fun i x y => by simp_rw [div_def, lift_def, map_div (g i)]) x y

@[to_additive (attr := simp)]
/--
theorem `lift_zpow` / 定理 `lift_zpow`

English:
theorem lift_zpow
  given: (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int)
  proof: x.induction _ fun i x => by simp_rw [zpow_def, lift_def, map_zpow (g i)]

中文:
定理 lift_zpow
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f) (z : 整数)
  证明: x.induction _ fun i x => by simp_rw [zpow_def, lift_def, map_zpow (g i)]

Depends on / 依赖: lift_def, map_zpow, simp_rw, x.induction, zpow_def
-/
theorem lift_zpow (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int) :
    DirectLimit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z :=
  x.induction _ fun i x => by simp_rw [zpow_def, lift_def, map_zpow (g i)]

end Group

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommGroup (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
  body: mul_comm

中文:
实例 [forall
  签名: i, CommGroup (G i)] [对任意 i j h, MonoidHomClass (T h) (G i) (G j)] :
  定义体: mul_comm
-/
@[to_additive] instance [forall i, CommGroup (G i)] [forall i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommGroup (DirectLimit G f) where
  mul_comm := mul_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, MulZeroClass (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)]
  body: DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, mul_zero]

中文:
实例 [forall
  签名: i, MulZeroClass (G i)] [对任意 i j h, MulHomClass (T h) (G i) (G j)]
  定义体: DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, mul_zero]

Depends on / 依赖: DirectLimit, DirectLimit.induction, mul_def, simp_rw, zero_def, zero_mul
-/
instance [forall i, MulZeroClass (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)]
    [forall i j h, ZeroHomClass (T h) (G i) (G j)] :
    MulZeroClass (DirectLimit G f) where
  zero_mul := DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ => by simp_rw [zero_def i, mul_def, mul_zero]

section MulZeroOneClass

variable [forall i, MulZeroOneClass (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulZeroOneClass (DirectLimit G f)
  body: zero_mul
  mul_zero := mul_zero

中文:
实例 :
  签名: MulZeroOneClass (DirectLimit G f)
  定义体: zero_mul
  mul_zero := mul_zero

Depends on / 依赖: zero_mul
-/
instance : MulZeroOneClass (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  body: ⟨0, 1, fun h => have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

中文:
实例 [forall
  签名: i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  定义体: ⟨0, 1, fun h => have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

Depends on / 依赖: Quotient, Quotient.eq.mp
-/
instance [forall i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  exists_pair_ne := ⟨0, 1, fun h => have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

end MulZeroOneClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SemigroupWithZero (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)]
  body: zero_mul
  mul_zero := mul_zero

中文:
实例 [forall
  签名: i, SemigroupWithZero (G i)] [对任意 i j h, MulHomClass (T h) (G i) (G j)]
  定义体: zero_mul
  mul_zero := mul_zero

Depends on / 依赖: zero_mul
-/
instance [forall i, SemigroupWithZero (G i)] [forall i j h, MulHomClass (T h) (G i) (G j)]
    [forall i j h, ZeroHomClass (T h) (G i) (G j)] :
    SemigroupWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, MonoidWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  body: zero_mul
  mul_zero := mul_zero

中文:
实例 [forall
  签名: i, MonoidWithZero (G i)] [对任意 i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  定义体: zero_mul
  mul_zero := mul_zero

Depends on / 依赖: zero_mul
-/
instance [forall i, MonoidWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    MonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommMonoidWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  body: zero_mul
  mul_zero := mul_zero

中文:
实例 [forall
  签名: i, CommMonoidWithZero (G i)] [对任意 i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  定义体: zero_mul
  mul_zero := mul_zero

Depends on / 依赖: zero_mul
-/
instance [forall i, CommMonoidWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommMonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

section GroupWithZero

variable [forall i, GroupWithZero (G i)] [GroupWithZero C]
variable [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]
variable [forall i, MonoidWithZeroHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GroupWithZero (DirectLimit G f)
  body: map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv₀ _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div₀ _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def,

中文:
实例 :
  签名: GroupWithZero (DirectLimit G f)
  定义体: map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv₀ _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div₀ _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def,
-/
instance : GroupWithZero (DirectLimit G f) where
  inv := map _ _ (fun _ => (·⁻¹)) fun _ _ _ => map_inv₀ _
  div := map₂ _ _ _ (fun _ => (· / ·)) fun _ _ _ => map_div₀ _
  zpow n := map _ _ (fun _ => (· ^ n)) fun _ _ _ x => map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ => show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ => by
    simp_rw [HPow.hPow, Pow.pow, map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x => by
    simp_rw [HPow.hPow, Pow.pow, map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x => by
    simp_rw [HPow.hPow, Pow.pow, map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [inv_zero]
  mul_inv_cancel := DirectLimit.induction _ fun i x ne => by
    have : x != 0 := by rintro rfl; exact ne (zero_def i).symm
    simp_rw [map_def, mul_def, mul_inv_cancel₀ this, one_def i]

/--
theorem `inv₀_def` / 定理 `inv₀_def`

English:
theorem inv₀_def
  given: (i x)
  statement: (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f)
  proof: rfl

中文:
定理 inv₀_def
  条件: (i x)
  结论: (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f)
  证明: rfl
-/
theorem inv₀_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl

/--
theorem `div₀_def` / 定理 `div₀_def`

English:
theorem div₀_def
  given: (i x y)
  statement: ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f)
  proof: map₂_def ..

中文:
定理 div₀_def
  条件: (i x y)
  结论: ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f)
  证明: map₂_def ..

Depends on / 依赖: IsLimit, Under.piFan, Under.piFanIsLimit, piFanIsLimit, piFanTensorProductIsLimit, preservesLimit_of_preserves_limit_cone
-/
theorem div₀_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

/--
theorem `zpow₀_def` / 定理 `zpow₀_def`

English:
theorem zpow₀_def
  given: (i x) (n : Int)
  statement: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  proof: rfl

@[simp]

中文:
定理 zpow₀_def
  条件: (i x) (n : 整数)
  结论: ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f)
  证明: rfl

@[simp]
-/
theorem zpow₀_def (i x) (n : Int) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) := rfl

@[simp]
/--
theorem `lift_inv₀` / 定理 `lift_inv₀`

English:
theorem lift_inv₀
  given: (g : forall i, H i) (h) (x : DirectLimit G f)
  proof: x.induction _ fun i x => by simp_rw [inv₀_def, lift_def, map_inv₀ (g i)]

@[simp]

中文:
定理 lift_inv₀
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f)
  证明: x.induction _ fun i x => by simp_rw [inv₀_def, lift_def, map_inv₀ (g i)]

@[simp]

Depends on / 依赖: lift_def, simp_rw, x.induction
-/
theorem lift_inv₀ (g : forall i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹ :=
  x.induction _ fun i x => by simp_rw [inv₀_def, lift_def, map_inv₀ (g i)]

@[simp]
/--
theorem `lift_div₀` / 定理 `lift_div₀`

English:
theorem lift_div₀
  given: (g : forall i, H i) (h) (x y : DirectLimit G f)
  proof: DirectLimit.induction₂ _ (fun i x y => by simp_rw [div₀_def, lift_def, map_div₀ (g i)]) x y

@[simp]

中文:
定理 lift_div₀
  条件: (g : 对任意 i, H i) (h) (x y : DirectLimit G f)
  证明: DirectLimit.induction₂ _ (fun i x y => by simp_rw [div₀_def, lift_def, map_div₀ (g i)]) x y

@[simp]

Depends on / 依赖: DirectLimit, DirectLimit.induction, lift_def, simp_rw
-/
theorem lift_div₀ (g : forall i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x / y) =
      (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·) h y) :=
  DirectLimit.induction₂ _ (fun i x y => by simp_rw [div₀_def, lift_def, map_div₀ (g i)]) x y

@[simp]
/--
theorem `lift_zpow₀` / 定理 `lift_zpow₀`

English:
theorem lift_zpow₀
  given: (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int)
  proof: x.induction _ fun i x => by simp_rw [zpow₀_def, lift_def, map_zpow₀ (g i)]

中文:
定理 lift_zpow₀
  条件: (g : 对任意 i, H i) (h) (x : DirectLimit G f) (z : 整数)
  证明: x.induction _ fun i x => by simp_rw [zpow₀_def, lift_def, map_zpow₀ (g i)]

Depends on / 依赖: lift_def, simp_rw, x.induction
-/
theorem lift_zpow₀ (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int) :
    DirectLimit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z :=
  x.induction _ fun i x => by simp_rw [zpow₀_def, lift_def, map_zpow₀ (g i)]

end GroupWithZero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommGroupWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  body: inferInstance
  mul_comm := mul_comm

中文:
实例 [forall
  签名: i, CommGroupWithZero (G i)] [对任意 i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
  定义体: inferInstance
  mul_comm := mul_comm
-/
instance [forall i, CommGroupWithZero (G i)] [forall i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommGroupWithZero (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  mul_comm := mul_comm

section AddMonoidWithOne

variable [forall i, AddMonoidWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoidWithOne (DirectLimit G f)
  body: map₀ _ fun _ => n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]

中文:
实例 :
  签名: AddMonoidWithOne (DirectLimit G f)
  定义体: map₀ _ fun _ => n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]
-/
instance : AddMonoidWithOne (DirectLimit G f) where
  natCast n := map₀ _ fun _ => n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]

/--
theorem `natCast_def` / 定理 `natCast_def`

English:
theorem natCast_def
  given: [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Nat) (i)
  proof: map₀_def _ _ (fun _ _ _ => map_natCast' _ (map_one _) _) _

中文:
定理 natCast_def
  条件: [对任意 i j h, OneHomClass (T h) (G i) (G j)] (n : 自然数) (i)
  证明: map₀_def _ _ (fun _ _ _ => map_natCast' _ (map_one _) _) _

Depends on / 依赖: map_natCast, map_one
-/
theorem natCast_def [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Nat) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => map_natCast' _ (map_one _) _) _

end AddMonoidWithOne

section AddGroupWithOne

variable [forall i, AddGroupWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroupWithOne (DirectLimit G f)
  body: inferInstance
  intCast n := map₀ _ fun _ => n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

中文:
实例 :
  签名: AddGroupWithOne (DirectLimit G f)
  定义体: inferInstance
  intCast n := map₀ _ fun _ => n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

Depends on / 依赖: Under.equalizerForkIsLimit, equalizerForkIsLimit, f.toUnder, g.toUnder, toUnder
-/
instance : AddGroupWithOne (DirectLimit G f) where
  __ : AddGroup _ := inferInstance
  intCast n := map₀ _ fun _ => n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

/--
theorem `intCast_def` / 定理 `intCast_def`

English:
theorem intCast_def
  given: [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Int) (i)
  proof: map₀_def _ _ (fun _ _ _ => map_intCast' _ (map_one _) _) _

中文:
定理 intCast_def
  条件: [对任意 i j h, OneHomClass (T h) (G i) (G j)] (n : 整数) (i)
  证明: map₀_def _ _ (fun _ _ _ => map_intCast' _ (map_one _) _) _

Depends on / 依赖: map_intCast, map_one
-/
theorem intCast_def [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Int) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => map_intCast' _ (map_one _) _) _

end AddGroupWithOne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommMonoidWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)] :
  body: add_comm

中文:
实例 [forall
  签名: i, AddCommMonoidWithOne (G i)] [对任意 i j h, AddMonoidHomClass (T h) (G i) (G j)] :
  定义体: add_comm

Depends on / 依赖: add_comm
-/
instance [forall i, AddCommMonoidWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommMonoidWithOne (DirectLimit G f) where
  add_comm := add_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommGroupWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)] :
  body: inferInstance
  add_comm := add_comm

中文:
实例 [forall
  签名: i, AddCommGroupWithOne (G i)] [对任意 i j h, AddMonoidHomClass (T h) (G i) (G j)] :
  定义体: inferInstance
  add_comm := add_comm
-/
instance [forall i, AddCommGroupWithOne (G i)] [forall i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommGroupWithOne (DirectLimit G f) where
  __ : AddGroupWithOne _ := inferInstance
  add_comm := add_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
  body: DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero

中文:
实例 [forall
  签名: i, NonUnitalNonAssocSemiring (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
  定义体: DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero

Depends on / 依赖: DirectLimit, DirectLimit.induction, add_def, left_distrib, mul_def, mul_zero, right_distrib, simp_rw, zero_mul
-/
instance [forall i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocSemiring (DirectLimit G f) where
  left_distrib := DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ => by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
  body: star_add

中文:
实例 [forall
  签名: i, NonUnitalNonAssocSemiring (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
  定义体: star_add

Depends on / 依赖: star_add
-/
instance [forall i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
    [forall i, StarRing (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)] :
    StarRing (DirectLimit G f) where
  star_add := star_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
  body: mul_assoc

中文:
实例 [forall
  签名: i, NonUnitalSemiring (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
  定义体: mul_assoc

Depends on / 依赖: mul_assoc
-/
instance [forall i, NonUnitalSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalSemiring (DirectLimit G f) where
  mul_assoc := mul_assoc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonAssocSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
  body: one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

中文:
实例 [forall
  签名: i, NonAssocSemiring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
  定义体: one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

Depends on / 依赖: one_mul
-/
instance [forall i, NonAssocSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocSemiring (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Semiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, Semiring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, Semiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    Semiring (DirectLimit G f) where

variable (f) in
/-- `map₀` as a `RingHom`. -/
@[simps]
/--
Definition of `map₀RingHom` / `map₀RingHom` 的定义

English:
definition map₀RingHom
  signature: [forall i, NonAssocSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)]
  body: map₀ _ r
  __ := map₀AddMonoidHom f
  __ := map₀MonoidHom f

中文:
定义 map₀RingHom
  签名: [对任意 i, NonAssocSemiring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)]
  定义体: map₀ _ r
  __ := map₀AddMonoidHom f
  __ := map₀MonoidHom f
-/
def map₀RingHom [forall i, NonAssocSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    (forall i, G i) ->+* DirectLimit G f where
  toFun r := map₀ _ r
  __ := map₀AddMonoidHom f
  __ := map₀MonoidHom f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalNonAssocCommSemiring (G i)]

中文:
实例 [forall
  签名: i, NonUnitalNonAssocCommSemiring (G i)]
-/
instance [forall i, NonUnitalNonAssocCommSemiring (G i)]
    [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocCommSemiring (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalCommSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonUnitalCommSemiring (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonUnitalCommSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalCommSemiring (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonAssocCommSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonAssocCommSemiring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonAssocCommSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocCommSemiring (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, CommSemiring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, CommSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    CommSemiring (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalNonAssocRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonUnitalNonAssocRing (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonUnitalNonAssocRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonUnitalRing (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonUnitalRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonAssocRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonAssocRing (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonAssocRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Ring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where

中文:
实例 [forall
  签名: i, Ring (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where
-/
instance [forall i, Ring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalNonAssocCommRing (G i)]

中文:
实例 [forall
  签名: i, NonUnitalNonAssocCommRing (G i)]
-/
instance [forall i, NonUnitalNonAssocCommRing (G i)]
    [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocCommRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalCommRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonUnitalCommRing (G i)] [对任意 i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonUnitalCommRing (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalCommRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonAssocCommRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, NonAssocCommRing (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, NonAssocCommRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocCommRing (DirectLimit G f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, CommRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :

中文:
实例 [forall
  签名: i, CommRing (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
-/
instance [forall i, CommRing (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    CommRing (DirectLimit G f) where

section Action

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Zero (G i)] [forall i, SMulZeroClass R (G i)]
  body: (smul_def _ _ _).trans by rw [smul_zero]; rfl

中文:
实例 [forall
  签名: i, Zero (G i)] [对任意 i, SMulZeroClass R (G i)]
  定义体: (smul_def _ _ _).trans by rw [smul_zero]; rfl

Depends on / 依赖: smul_def, smul_zero
-/
instance [forall i, Zero (G i)] [forall i, SMulZeroClass R (G i)]
    [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulZeroClass R (DirectLimit G f) where
smul_zero r := (smul_def _ _ _).trans by rw [smul_zero]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [forall i, Zero (G i)] [forall i, SMulWithZero R (G i)]
  body: DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i]

中文:
实例 [Zero
  签名: R] [对任意 i, Zero (G i)] [对任意 i, SMulWithZero R (G i)]
  定义体: DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i]

Depends on / 依赖: DirectLimit, DirectLimit.induction, simp_rw, smul_def, zero_def, zero_smul
-/
instance [Zero R] [forall i, Zero (G i)] [forall i, SMulWithZero R (G i)]
    [forall i j h, MulActionHomClass (T h) R (G i) (G j)]
    [forall i j h, ZeroHomClass (T h) (G i) (G j)] :
    SMulWithZero R (DirectLimit G f) where
  zero_smul := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddZeroClass (G i)] [forall i, DistribSMul R (G i)]
  body: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [add_def, smul_def, smul_add, add_def]

中文:
实例 [forall
  签名: i, AddZeroClass (G i)] [对任意 i, DistribSMul R (G i)]
  定义体: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [add_def, smul_def, smul_add, add_def]

Depends on / 依赖: DirectLimit, DirectLimit.induction, add_def, simp_rw, smul_add, smul_def
-/
instance [forall i, AddZeroClass (G i)] [forall i, DistribSMul R (G i)]
    [forall i j h, AddMonoidHomClass (T h) (G i) (G j)]
    [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    DistribSMul R (DirectLimit G f) where
  smul_add r := DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [add_def, smul_def, smul_add, add_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [forall i, AddMonoid (G i)] [forall i, DistribMulAction R (G i)]
  body: have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

中文:
实例 [Monoid
  签名: R] [对任意 i, AddMonoid (G i)] [对任意 i, DistribMulAction R (G i)]
  定义体: have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

Depends on / 依赖: MulActionHomClass, smul_add, smul_zero
-/
instance [Monoid R] [forall i, AddMonoid (G i)] [forall i, DistribMulAction R (G i)]
    [forall i j h, DistribMulActionHomClass (T h) R (G i) (G j)] :
    DistribMulAction R (DirectLimit G f) :=
  have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [forall i, Monoid (G i)] [forall i, MulDistribMulAction R (G i)]
  body: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
smul_one r := (smul_def _ _ _).trans by rw [smul_one]; rfl

中文:
实例 [Monoid
  签名: R] [对任意 i, Monoid (G i)] [对任意 i, MulDistribMulAction R (G i)]
  定义体: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
smul_one r := (smul_def _ _ _).trans by rw [smul_one]; rfl

Depends on / 依赖: DirectLimit, DirectLimit.induction, MulDistribMulAction, MulDistribMulAction.smul_mul, mul_def, simp_rw, smul_def, smul_mul, smul_one
-/
instance [Monoid R] [forall i, Monoid (G i)] [forall i, MulDistribMulAction R (G i)]
    [forall i j h, MonoidHomClass (T h) (G i) (G j)]
    [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulDistribMulAction R (DirectLimit G f) where
  smul_mul r := DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
smul_one r := (smul_def _ _ _).trans by rw [smul_one]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [forall i, AddCommMonoid (G i)] [forall i, Module R (G i)]
  body: have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i] }

中文:
实例 [Semiring
  签名: R] [对任意 i, AddCommMonoid (G i)] [对任意 i, Module R (G i)]
  定义体: have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i] }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, DirectLimit, DirectLimit.induction, DistribMulActionHomClass, MagmaCat, add_def, add_smul, simp_rw, smul_def, zero_def, zero_smul
-/
instance [Semiring R] [forall i, AddCommMonoid (G i)] [forall i, Module R (G i)]
    [forall i j h, LinearMapClass (T h) R (G i) (G j)] :
    Module R (DirectLimit G f) :=
  have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ => by simp_rw [smul_def, zero_smul, zero_def i] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Mul (G i)] [forall i, SMul R (G i)] [forall i, IsScalarTower R (G i) (G i)]
  body: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, smul_mul_assoc]

中文:
实例 [forall
  签名: i, Mul (G i)] [对任意 i, SMul R (G i)] [对任意 i, IsScalarTower R (G i) (G i)]
  定义体: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, smul_mul_assoc]

Depends on / 依赖: DirectLimit, DirectLimit.induction, mul_def, simp_rw, smul_def, smul_eq_mul, smul_mul_assoc
-/
instance [forall i, Mul (G i)] [forall i, SMul R (G i)] [forall i, IsScalarTower R (G i) (G i)]
    [forall i j h, MulHomClass (T h) (G i) (G j)] [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    IsScalarTower R (DirectLimit G f) (DirectLimit G f) where
  smul_assoc r := DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, smul_mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Mul (G i)] [forall i, SMul R (G i)] [forall i, SMulCommClass R (G i) (G i)]
  body: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, mul_smul_comm]

中文:
实例 [forall
  签名: i, Mul (G i)] [对任意 i, SMul R (G i)] [对任意 i, SMulCommClass R (G i) (G i)]
  定义体: DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, mul_smul_comm]

Depends on / 依赖: DirectLimit, DirectLimit.induction, f.hom, mul_def, mul_smul_comm, simp_rw, smul_def, smul_eq_mul
-/
instance [forall i, Mul (G i)] [forall i, SMul R (G i)] [forall i, SMulCommClass R (G i) (G i)]
    [forall i j h, MulHomClass (T h) (G i) (G j)] [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulCommClass R (DirectLimit G f) (DirectLimit G f) where
  smul_comm r := DirectLimit.induction₂ _ fun i _ _ => by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, mul_smul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Mul (G i)] [forall i, SMul R (G i)] [forall i, SMulCommClass (G i) R (G i)]
  body: have _ (i) : SMulCommClass R (G i) (G i) := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

中文:
实例 [forall
  签名: i, Mul (G i)] [对任意 i, SMul R (G i)] [对任意 i, SMulCommClass (G i) R (G i)]
  定义体: have _ (i) : SMulCommClass R (G i) (G i) := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance [forall i, Mul (G i)] [forall i, SMul R (G i)] [forall i, SMulCommClass (G i) R (G i)]
    [forall i j h, MulHomClass (T h) (G i) (G j)] [forall i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulCommClass (DirectLimit G f) R (DirectLimit G f) :=
  have _ (i) : SMulCommClass R (G i) (G i) := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

end Action

section DivisionSemiring
variable [forall i, DivisionSemiring (G i)] [DivisionSemiring C]
variable [forall i j h, RingHomClass (T h) (G i) (G j)] [forall i, RingHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisionSemiring (DirectLimit G f)
  body: inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := map₀ _ fun _ => q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ :=

中文:
实例 :
  签名: DivisionSemiring (DirectLimit G f)
  定义体: inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := map₀ _ fun _ => q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ :=
-/
instance : DivisionSemiring (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := map₀ _ fun _ => q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ := DirectLimit.induction _ fun i x => show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ => map_nnratCast _ _) i, mul_def, NNRat.smul_def]

/--
theorem `nnratCast_def` / 定理 `nnratCast_def`

English:
theorem nnratCast_def
  given: (q : Rat>=0) (i)
  statement: (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
  proof: map₀_def _ _ (fun _ _ _ => map_nnratCast _ _) _

@[simp]

中文:
定理 nnratCast_def
  条件: (q : Rat>=0) (i)
  结论: (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
  证明: map₀_def _ _ (fun _ _ _ => map_nnratCast _ _) _

@[simp]

Depends on / 依赖: map_nnratCast
-/
theorem nnratCast_def (q : Rat>=0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => map_nnratCast _ _) _

@[simp]
/--
theorem `lift_nnratCast` / 定理 `lift_nnratCast`

English:
theorem lift_nnratCast
  given: (g : forall i, H i) (h) (q : Rat>=0)
  proof: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [nnratCast_def]; rw [lift_def]; rw [map_nnratCast (g i)]

中文:
定理 lift_nnratCast
  条件: (g : 对任意 i, H i) (h) (q : Rat>=0)
  证明: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [nnratCast_def]; rw [lift_def]; rw [map_nnratCast (g i)]

Depends on / 依赖: Nonempty, lift_def, map_nnratCast, nnratCast_def
-/
theorem lift_nnratCast (g : forall i, H i) (h) (q : Rat>=0) :
    DirectLimit.lift f (g ·) h (q : DirectLimit G f) = (q : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [nnratCast_def]; rw [lift_def]; rw [map_nnratCast (g i)]

end DivisionSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Semifield (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
  body: inferInstance
  mul_comm := mul_comm

中文:
实例 [forall
  签名: i, Semifield (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
  定义体: inferInstance
  mul_comm := mul_comm
-/
instance [forall i, Semifield (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    Semifield (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  mul_comm := mul_comm

section DivisionRing
variable [forall i, DivisionRing (G i)] [DivisionRing C]
variable [forall i j h, RingHomClass (T h) (G i) (G j)] [forall i, RingHomClass (H i) (G i) C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisionRing (DirectLimit G f)
  body: inferInstance
  __ : Ring _ := inferInstance
  ratCast q := map₀ _ fun _ => q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induc

中文:
实例 :
  签名: DivisionRing (DirectLimit G f)
  定义体: inferInstance
  __ : Ring _ := inferInstance
  ratCast q := map₀ _ fun _ => q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induc
-/
instance : DivisionRing (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  __ : Ring _ := inferInstance
  ratCast q := map₀ _ fun _ => q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := map _ _ (fun _ => (q • ·)) fun _ _ _ x => by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induction _ fun i x => show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ => map_ratCast _ _) i, mul_def, Rat.smul_def]

/--
theorem `ratCast_def` / 定理 `ratCast_def`

English:
theorem ratCast_def
  given: (q : Rat) (i)
  statement: (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
  proof: map₀_def _ _ (fun _ _ _ => map_ratCast _ _) _

@[simp]

中文:
定理 ratCast_def
  条件: (q : Rat) (i)
  结论: (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
  证明: map₀_def _ _ (fun _ _ _ => map_ratCast _ _) _

@[simp]

Depends on / 依赖: map_ratCast
-/
theorem ratCast_def (q : Rat) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => map_ratCast _ _) _

@[simp]
/--
theorem `lift_ratCast` / 定理 `lift_ratCast`

English:
theorem lift_ratCast
  given: (g : forall i, H i) (h) (q : Rat)
  proof: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [ratCast_def]; rw [lift_def]; rw [map_ratCast (g i)]

中文:
定理 lift_ratCast
  条件: (g : 对任意 i, H i) (h) (q : Rat)
  证明: by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [ratCast_def]; rw [lift_def]; rw [map_ratCast (g i)]

Depends on / 依赖: Nonempty, lift_def, map_ratCast, ratCast_def
-/
theorem lift_ratCast (g : forall i, H i) (h) (q : Rat) :
    DirectLimit.lift f (g ·) h (q : DirectLimit G f) = (q : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [ratCast_def]; rw [lift_def]; rw [map_ratCast (g i)]

end DivisionRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Field (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
  body: inferInstance
  mul_comm := mul_comm

中文:
实例 [forall
  签名: i, Field (G i)] [对任意 i j h, RingHomClass (T h) (G i) (G j)] :
  定义体: inferInstance
  mul_comm := mul_comm
-/
instance [forall i, Field (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] :
    Field (DirectLimit G f) where
  __ : DivisionRing _ := inferInstance
  mul_comm := mul_comm

section Algebra

variable [CommSemiring R]
variable [forall i, Semiring (G i)]
variable [forall i, Algebra R (G i)] [forall i j h, AlgHomClass (T h) R (G i) (G j)]

/--
lemma `map₀_algebraMap` / 引理 `map₀_algebraMap`

English:
lemma map₀_algebraMap
  given: (i : ι) (r : R)
  proof: map₀_def _ _ (fun _ _ _ => AlgHomClass.commutes _ _) i

中文:
引理 map₀_algebraMap
  条件: (i : ι) (r : R)
  证明: map₀_def _ _ (fun _ _ _ => AlgHomClass.commutes _ _) i

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, commutes
-/
lemma map₀_algebraMap (i : ι) (r : R) :
    map₀ f (fun i => algebraMap R (G i) r) = ⟦⟨i, algebraMap R (G i) r⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => AlgHomClass.commutes _ _) i

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (DirectLimit G f)
  body: map₀RingHom (f := f).comp (algebraMap R (forall i, G i))
  commutes' r := DirectLimit.induction f fun i _ => by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [map₀_algebraMap i]; rw [mul_def]; rw [mul_def]; rw [Algebra.commutes]
  smul_def' r := DirectLimit.induction _ fun i _ => by
    dsimp [P

中文:
实例 :
  签名: Algebra R (DirectLimit G f)
  定义体: map₀RingHom (f := f).comp (algebraMap R (forall i, G i))
  commutes' r := DirectLimit.induction f fun i _ => by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [map₀_algebraMap i]; rw [mul_def]; rw [mul_def]; rw [Algebra.commutes]
  smul_def' r := DirectLimit.induction _ fun i _ => by
    dsimp [P

Depends on / 依赖: algebraMap
-/
instance : Algebra R (DirectLimit G f) where
  algebraMap := map₀RingHom (f := f).comp (algebraMap R (forall i, G i))
  commutes' r := DirectLimit.induction f fun i _ => by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [map₀_algebraMap i]; rw [mul_def]; rw [mul_def]; rw [Algebra.commutes]
  smul_def' r := DirectLimit.induction _ fun i _ => by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [smul_def]; rw [map₀_algebraMap i]; rw [mul_def]; rw [Algebra.smul_def']

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  given: (i : ι) (r : R)
  proof: map₀_algebraMap i r

中文:
引理 algebraMap_def
  条件: (i : ι) (r : R)
  证明: map₀_algebraMap i r
-/
lemma algebraMap_def (i : ι) (r : R) :
    algebraMap R (DirectLimit G f) r = ⟦⟨i, algebraMap R (G i) r⟩⟧ :=
  map₀_algebraMap i r

end Algebra

end DirectLimit

namespace DirectLimit

namespace Module

variable [Semiring R] [forall i, AddCommMonoid (G i)] [forall i, Module R (G i)]
variable [forall i j h, LinearMapClass (T h) R (G i) (G j)]
variable (R ι G f) [Nonempty ι]

/-- The canonical map from a component to the direct limit. -/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: ⟦⟨i, x⟩⟧
  map_add' _ _ := (add_def ..).symm
  map_smul' _ _ := (smul_def ..).symm

中文:
定义 of
  签名: (i)
  定义体: ⟦⟨i, x⟩⟧
  map_add' _ _ := (add_def ..).symm
  map_smul' _ _ := (smul_def ..).symm
-/
def of (i) : G i ->ₗ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_add' _ _ := (add_def ..).symm
  map_smul' _ _ := (smul_def ..).symm

variable {R ι G f}

/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j hij x}
  statement: of R ι G f j (f i j hij x) = of R ι G f i x
  proof: .symm eq_of_le ..

中文:
定理 of_f
  条件: {i j hij x}
  结论: of R ι G f j (f i j hij x) = of R ι G f i x
  证明: .symm eq_of_le ..

Depends on / 依赖: eq_of_le
-/
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x := .symm eq_of_le ..

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_add' := lift_add _ _
  map_smul' := lift_smul _ _

中文:
定义 lift
  签名: (g : 对任意 i, G i ->ₗ[R] P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_add' := lift_add _ _
  map_smul' := lift_smul _ _

Depends on / 依赖: DirectLimit, _root_, _root_.DirectLimit.lift
-/
def lift (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->ₗ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_add' := lift_add _ _
  map_smul' := lift_smul _ _

variable (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: lift R ι G f g Hg ∘ₗ of R ι G f i = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: lift R ι G f g Hg ∘ₗ of R ι G f i = g i
  证明: rfl
-/
theorem lift_comp_of {i} : lift R ι G f g Hg ∘ₗ of R ι G f i = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: {i} (x)
  statement: lift R ι G f g Hg (of R ι G f i x) = g i x
  proof: rfl

@[ext]

中文:
定理 lift_of
  条件: {i} (x)
  结论: lift R ι G f g Hg (of R ι G f i x) = g i x
  证明: rfl

@[ext]
-/
theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x := rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  结论: {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: DirectLimit, DirectLimit.induction
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P}
    (h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Module

namespace NonUnitalRing
variable [forall i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
nonrec def of (i) : G i ->ₙ+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_mul' _ _ := (mul_def ..).symm
  map_zero' := (zero_def i).symm
  map_add' _ _ := (add_def ..).symm

/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: by simp

中文:
定理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: by simp
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := by simp

variable (P : Type*) [NonUnitalNonAssocSemiring P]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another
NonUnitalNonAsssocSemiRing that respect the directed system structure
(i.e. make some diagram commute) give rise to a unique map out of the direct limit.
-/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  body: _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_mul' := lift_mul _ _
  map_zero' := lift_zero _ _
  map_add' := lift_add _ _

中文:
定义 lift
  定义体: _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_mul' := lift_mul _ _
  map_zero' := lift_zero _ _
  map_add' := lift_add _ _

Depends on / 依赖: DirectLimit, _root_, _root_.DirectLimit.lift
-/
noncomputable def lift
    (g : forall i, (G i) ->ₙ+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->ₙ+* P where
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_mul' := lift_mul _ _
  map_zero' := lift_zero _ _
  map_add' := lift_add _ _

variable (g : forall i, G i ->ₙ+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: (lift G f P g Hg).comp (of G f i) = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: (lift G f P g Hg).comp (of G f i) = g i
  证明: rfl
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: rfl

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: rfl

@[ext]
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {g₁ g₂ : DirectLimit G f ->ₙ+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i))
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  条件: {g₁ g₂ : DirectLimit G f ->ₙ+* P} (h : 对任意 i, g₁.comp (of G f i) = g₂.comp (of G f i))
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, DirectLimit, DirectLimit.induction, Semigrp
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->ₙ+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)):
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalRing

namespace Ring

variable [forall i, NonAssocSemiring (G i)] [forall i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
nonrec def of (i) : G i ->+* DirectLimit G f where
  __ := NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm

/--
theorem `of_f` / 定理 `of_f`

English:
theorem of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: .symm eq_of_le ..

中文:
定理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: .symm eq_of_le ..

Depends on / 依赖: eq_of_le
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm eq_of_le ..

variable (P : Type*) [NonAssocSemiring P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_one' := lift_one _ _

中文:
定义 lift
  签名: (g : 对任意 i, G i ->+* P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_one' := lift_one _ _

Depends on / 依赖: NonUnitalRing, NonUnitalRing.lift, f.hom, toNonUnitalRingHom
-/
def lift (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->+* P where
  __ := (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  map_one' := lift_one _ _

variable (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: (lift G f P g Hg).comp (of G f i) = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: (lift G f P g Hg).comp (of G f i) = g i
  证明: rfl
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: rfl

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: rfl

@[ext]
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i))
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  条件: {g₁ g₂ : DirectLimit G f ->+* P} (h : 对任意 i, g₁.comp (of G f i) = g₂.comp (of G f i))
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: DirectLimit, DirectLimit.induction
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Ring

namespace NonUnitalStarRing

variable [forall i, NonUnitalNonAssocSemiring (G i)] [forall i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [forall i, StarRing (G i)] [forall i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_star' _ := (star_def ..).symm

中文:
定义 of
  签名: (i)
  定义体: NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_star' _ := (star_def ..).symm

Depends on / 依赖: NonUnitalRing, NonUnitalRing.of
-/
noncomputable def of (i) : G i ->⋆ₙ+* DirectLimit G f where
  __ := NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_star' _ := (star_def ..).symm

/--
lemma `of_f` / 引理 `of_f`

English:
lemma of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: .symm eq_of_le ..

中文:
引理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: .symm eq_of_le ..

Depends on / 依赖: eq_of_le
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm eq_of_le ..

variable (P : Type*) [NonUnitalNonAssocSemiring P] [StarRing P]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another StarRing
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  body: (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_star' := lift_star _ _

中文:
定义 lift
  定义体: (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_star' := lift_star _ _

Depends on / 依赖: NonUnitalRing, NonUnitalRing.lift, toNonUnitalRingHom
-/
noncomputable def lift
    (g : forall i, (G i) ->⋆ₙ+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->⋆ₙ+* P where
  __ := (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x => (Hg i j hij x).symm)
  map_star' := lift_star _ _

variable (g : forall i, G i ->⋆ₙ+* P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: (lift G f P g Hg).comp (of G f i) = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: (lift G f P g Hg).comp (of G f i) = g i
  证明: rfl
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: rfl

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: rfl

@[ext]
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : DirectLimit G f ->⋆ₙ+* P}
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  结论: {g₁ g₂ : DirectLimit G f ->⋆ₙ+* P}
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: DirectLimit, DirectLimit.induction
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->⋆ₙ+* P}
    (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalStarRing

namespace Algebra

variable [CommSemiring R]
variable [forall i, Semiring (G i)] [forall i, Algebra R (G i)]
variable [forall i j h, AlgHomClass (T h) R (G i) (G j)]
variable [Nonempty ι]

set_option backward.isDefEq.respectTransparency.types false in
variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: ⟦⟨i, x⟩⟧
  __ := (DirectLimit.Ring.of G f i)
  commutes' r := by rw [algebraMap_def i]

中文:
定义 of
  签名: (i)
  定义体: ⟦⟨i, x⟩⟧
  __ := (DirectLimit.Ring.of G f i)
  commutes' r := by rw [algebraMap_def i]
-/
def of (i) : G i ->ₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  __ := (DirectLimit.Ring.of G f i)
  commutes' r := by rw [algebraMap_def i]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `of_f` / 引理 `of_f`

English:
lemma of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: .symm eq_of_le ..

中文:
引理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: .symm eq_of_le ..

Depends on / 依赖: eq_of_le
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm eq_of_le ..

variable (P : Type*) [Semiring P] [Algebra R P]

set_option backward.isDefEq.respectTransparency.types false in
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->ₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.Ring.lift G f P (g := fun i => (g i).toRingHom) (Hg := Hg)
  commutes' r := by
    let i := Classical.arbitrary ι
    rw [algebraMap_def i r]; rw [lift_def]; rw [AlgHom.commutes]

中文:
定义 lift
  签名: (g : 对任意 i, G i ->ₐ[R] P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.Ring.lift G f P (g := fun i => (g i).toRingHom) (Hg := Hg)
  commutes' r := by
    let i := Classical.arbitrary ι
    rw [algebraMap_def i r]; rw [lift_def]; rw [AlgHom.commutes]

Depends on / 依赖: DirectLimit, _root_, _root_.DirectLimit.lift
-/
def lift (g : forall i, G i ->ₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->ₐ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.Ring.lift G f P (g := fun i => (g i).toRingHom) (Hg := Hg)
  commutes' r := by
    let i := Classical.arbitrary ι
    rw [algebraMap_def i r]; rw [lift_def]; rw [AlgHom.commutes]

variable (g : forall i, G i ->ₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: (lift G f P g Hg).comp (of G f i) = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: (lift G f P g Hg).comp (of G f i) = g i
  证明: rfl
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: rfl

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: rfl
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : DirectLimit G f ->ₐ[R] P}
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  结论: {g₁ g₂ : DirectLimit G f ->ₐ[R] P}
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: DirectLimit, DirectLimit.induction
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->ₐ[R] P}
    (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Algebra

namespace NonUnitalAlgebra

variable [CommSemiring R]
variable [forall i, NonUnitalNonAssocSemiring (G i)] [forall i, DistribMulAction R (G i)]
variable [forall i j h, NonUnitalAlgHomClass (T h) R (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (i)
  body: ⟦⟨i, x⟩⟧
  __ := (DirectLimit.NonUnitalRing.of G f i)
  map_smul' m x := by rw [smul_def, MonoidHom.id_apply]

中文:
定义 of
  签名: (i)
  定义体: ⟦⟨i, x⟩⟧
  __ := (DirectLimit.NonUnitalRing.of G f i)
  map_smul' m x := by rw [smul_def, MonoidHom.id_apply]
-/
def of (i) : G i ->ₙₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  __ := (DirectLimit.NonUnitalRing.of G f i)
  map_smul' m x := by rw [smul_def, MonoidHom.id_apply]

/--
lemma `of_f` / 引理 `of_f`

English:
lemma of_f
  given: {i j} (hij) (x)
  statement: of G f j (f i j hij x) = of G f i x
  proof: .symm eq_of_le ..

中文:
引理 of_f
  条件: {i j} (hij) (x)
  结论: of G f j (f i j hij x) = of G f i x
  证明: .symm eq_of_le ..

Depends on / 依赖: eq_of_le
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm eq_of_le ..

variable (P : Type*) [NonUnitalNonAssocSemiring P] [DistribMulAction R P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps toFun]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (g : forall i, G i ->ₙₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)
  body: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.NonUnitalRing.lift G f P (g := fun i => (g i)) (Hg := Hg)
  map_smul' m := by apply lift_smul

中文:
定义 lift
  签名: (g : 对任意 i, G i ->ₙₐ[R] P) (Hg : 对任意 i j hij x, g j (f i j hij x) = g i x)
  定义体: _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.NonUnitalRing.lift G f P (g := fun i => (g i)) (Hg := Hg)
  map_smul' m := by apply lift_smul

Depends on / 依赖: DirectLimit, _root_, _root_.DirectLimit.lift
-/
def lift (g : forall i, G i ->ₙₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f ->ₙₐ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x => (Hg i j h x).symm
  __ := DirectLimit.NonUnitalRing.lift G f P (g := fun i => (g i)) (Hg := Hg)
  map_smul' m := by apply lift_smul

variable (g : forall i, G i ->ₙₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x) = g i x)

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: {i}
  statement: (lift G f P g Hg).comp (of G f i) = g i
  proof: rfl

中文:
定理 lift_comp_of
  条件: {i}
  结论: (lift G f P g Hg).comp (of G f i) = g i
  证明: rfl
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (i x)
  statement: lift G f P g Hg (of G f i x) = g i x
  proof: rfl

@[ext]

中文:
定理 lift_of
  条件: (i x)
  结论: lift G f P g Hg (of G f i x) = g i x
  证明: rfl

@[ext]
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {g₁ g₂ : DirectLimit G f ->ₙₐ[R] P}
  proof: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

中文:
定理 hom_ext
  结论: {g₁ g₂ : DirectLimit G f ->ₙₐ[R] P}
  证明: by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

Depends on / 依赖: DirectLimit, DirectLimit.induction
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f ->ₙₐ[R] P}
    (h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalAlgebra

end DirectLimit
