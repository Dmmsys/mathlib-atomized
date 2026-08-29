/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.FreeNonUnitalNonAssocAlgebra
public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Free Lie algebras

Given a commutative ring `R` and a type `X` we construct the free Lie algebra on `X` with
coefficients in `R` together with its universal property.

## Main definitions

  * `FreeLieAlgebra`
  * `FreeLieAlgebra.lift`
  * `FreeLieAlgebra.of`
  * `FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`

## Implementation details

### Quotient of free non-unital, non-associative algebra

We follow [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) and construct
the free Lie algebra as a quotient of the free non-unital, non-associative algebra. Since we do not
currently have definitions of ideals, lattices of ideals, and quotients for
`NonUnitalNonAssocSemiring`, we construct our quotient using the low-level `Quot` function on
an inductively-defined relation.

### Alternative construction (needs PBW)

An alternative construction of the free Lie algebra on `X` is to start with the free unital
associative algebra on `X`, regard it as a Lie algebra via the ring commutator, and take its
smallest Lie subalgebra containing `X`. I.e.:
`LieSubalgebra.lieSpan R (FreeAlgebra R X) (Set.range (FreeAlgebra.ι R))`.

However with this definition there does not seem to be an easy proof that the required universal
property holds, and I don't know of a proof that avoids invoking the Poincaré–Birkhoff–Witt theorem.
A related MathOverflow question is [this one](https://mathoverflow.net/questions/396680/).

## Tags

lie algebra, free algebra, non-unital, non-associative, universal property, forgetful functor,
adjoint functor
-/

@[expose] public section


universe u v w

noncomputable section

variable (R : Type u) (X : Type v) [CommRing R]

/- We save characters by using Bourbaki's name `lib` (as in «libre») for
`FreeNonUnitalNonAssocAlgebra` in this file. -/
local notation "lib" => FreeNonUnitalNonAssocAlgebra

local notation "lib.lift" => FreeNonUnitalNonAssocAlgebra.lift

local notation "lib.of" => FreeNonUnitalNonAssocAlgebra.of

local notation "lib.lift_of_apply" => FreeNonUnitalNonAssocAlgebra.lift_of_apply

local notation "lib.lift_comp_of" => FreeNonUnitalNonAssocAlgebra.lift_comp_of

namespace FreeLieAlgebra

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: : lib R X -> lib R X -> Prop
  constructors (6):
    - lie_self: (a : lib R X) : Rel (a * a) 0
    - leibniz_lie: (a b c : lib R X) : Rel (a * (b * c)) (a * b * c + b * (a * c))
    - smul: (t : R) {a b : lib R X} : Rel a b -> Rel (t • a) (t • b)
    - add_right: {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a + c) (b + c)
    - mul_left: (a : lib R X) {b c : lib R X} : Rel b c -> Rel (a * b) (a * c)
    - mul_right: {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a * c) (b * c)

中文:
归纳类型 Rel
  参数: : lib R X -> lib R X -> 命题
  构造子 (6 个):
    - lie_self: (a : lib R X) : Rel (a * a) 0
    - leibniz_lie: (a b c : lib R X) : Rel (a * (b * c)) (a * b * c + b * (a * c))
    - smul: (t : R) {a b : lib R X} : Rel a b -> Rel (t • a) (t • b)
    - add_right: {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a + c) (b + c)
    - mul_left: (a : lib R X) {b c : lib R X} : Rel b c -> Rel (a * b) (a * c)
    - mul_right: {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a * c) (b * c)
-/
inductive Rel : lib R X -> lib R X -> Prop
  | lie_self (a : lib R X) : Rel (a * a) 0
  | leibniz_lie (a b c : lib R X) : Rel (a * (b * c)) (a * b * c + b * (a * c))
  | smul (t : R) {a b : lib R X} : Rel a b -> Rel (t • a) (t • b)
  | add_right {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a + c) (b + c)
  | mul_left (a : lib R X) {b c : lib R X} : Rel b c -> Rel (a * b) (a * c)
  | mul_right {a b : lib R X} (c : lib R X) : Rel a b -> Rel (a * c) (b * c)

variable {R X}

/--
theorem `Rel.addLeft` / 定理 `Rel.addLeft`

English:
theorem Rel.addLeft
  given: (a : lib R X) {b c : lib R X} (h : Rel R X b c)
  statement: Rel R X (a + b) (a + c)
  proof: by
  rw [add_comm _ b]; rw [add_comm _ c]; exact h.add_right _

中文:
定理 Rel.addLeft
  条件: (a : lib R X) {b c : lib R X} (h : Rel R X b c)
  结论: Rel R X (a + b) (a + c)
  证明: by
  rw [add_comm _ b]; rw [add_comm _ c]; exact h.add_right _

Depends on / 依赖: add_comm, add_right, h.add_right
-/
theorem Rel.addLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a + b) (a + c) := by
  rw [add_comm _ b]; rw [add_comm _ c]; exact h.add_right _

/--
theorem `Rel.neg` / 定理 `Rel.neg`

English:
theorem Rel.neg
  given: {a b : lib R X} (h : Rel R X a b)
  statement: Rel R X (-a) (-b)
  proof: by
  simpa only [neg_one_smul] using h.smul (-1)

中文:
定理 Rel.neg
  条件: {a b : lib R X} (h : Rel R X a b)
  结论: Rel R X (-a) (-b)
  证明: by
  simpa only [neg_one_smul] using h.smul (-1)
-/
theorem Rel.neg {a b : lib R X} (h : Rel R X a b) : Rel R X (-a) (-b) := by
  simpa only [neg_one_smul] using h.smul (-1)

/--
theorem `Rel.subLeft` / 定理 `Rel.subLeft`

English:
theorem Rel.subLeft
  given: (a : lib R X) {b c : lib R X} (h : Rel R X b c)
  statement: Rel R X (a - b) (a - c)
  proof: by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a

中文:
定理 Rel.subLeft
  条件: (a : lib R X) {b c : lib R X} (h : Rel R X b c)
  结论: Rel R X (a - b) (a - c)
  证明: by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a

Depends on / 依赖: addLeft, h.neg.addLeft, sub_eq_add_neg
-/
theorem Rel.subLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a - b) (a - c) := by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a

/--
theorem `Rel.subRight` / 定理 `Rel.subRight`

English:
theorem Rel.subRight
  given: {a b : lib R X} (c : lib R X) (h : Rel R X a b)
  statement: Rel R X (a - c) (b - c)
  proof: by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

中文:
定理 Rel.subRight
  条件: {a b : lib R X} (c : lib R X) (h : Rel R X a b)
  结论: Rel R X (a - c) (b - c)
  证明: by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

Depends on / 依赖: add_right, h.add_right, sub_eq_add_neg
-/
theorem Rel.subRight {a b : lib R X} (c : lib R X) (h : Rel R X a b) : Rel R X (a - c) (b - c) := by
  simpa only [sub_eq_add_neg] using h.add_right (-c)

/--
theorem `Rel.smulOfTower` / 定理 `Rel.smulOfTower`

English:
theorem Rel.smulOfTower
  statement: {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
  proof: by
  rw [← smul_one_smul R t a]; rw [← smul_one_smul R t b]
  exact h.smul _

中文:
定理 Rel.smulOfTower
  结论: {S : 类型} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
  证明: by
  rw [← smul_one_smul R t a]; rw [← smul_one_smul R t b]
  exact h.smul _

Depends on / 依赖: h.smul, smul_one_smul
-/
theorem Rel.smulOfTower {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
    (a b : lib R X) (h : Rel R X a b) : Rel R X (t • a) (t • b) := by
  rw [← smul_one_smul R t a]; rw [← smul_one_smul R t b]
  exact h.smul _

end FreeLieAlgebra

/--
Definition of `FreeLieAlgebra` / `FreeLieAlgebra` 的定义

English:
definition FreeLieAlgebra
  body: Quot (FreeLieAlgebra.Rel R X)

中文:
定义 FreeLieAlgebra
  定义体: Quot (FreeLieAlgebra.Rel R X)

Depends on / 依赖: FreeLieAlgebra, FreeLieAlgebra.Rel
-/
def FreeLieAlgebra :=
  Quot (FreeLieAlgebra.Rel R X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FreeLieAlgebra R X)
  body: by rw [FreeLieAlgebra]; infer_instance

中文:
实例 :
  签名: Inhabited (FreeLieAlgebra R X)
  定义体: by rw [FreeLieAlgebra]; infer_instance

Depends on / 依赖: FreeLieAlgebra, infer_instance
-/
instance : Inhabited (FreeLieAlgebra R X) := by rw [FreeLieAlgebra]; infer_instance

namespace FreeLieAlgebra

instance {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] :
    SMul S (FreeLieAlgebra R X) where smul t := Quot.map (t • ·) (Rel.smulOfTower t)

instance {S : Type*} [Monoid S] [DistribMulAction S R] [DistribMulAction Sᵐᵒᵖ R]
    [IsScalarTower S R R] [IsCentralScalar S R] : IsCentralScalar S (FreeLieAlgebra R X) where
  op_smul_eq_smul t := Quot.ind fun a => congr_arg (Quot.mk _) (op_smul_eq_smul t a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (FreeLieAlgebra R X)
  body: Quot.mk _ 0

中文:
实例 :
  签名: Zero (FreeLieAlgebra R X)
  定义体: Quot.mk _ 0

Depends on / 依赖: Quot.mk
-/
instance : Zero (FreeLieAlgebra R X) where zero := Quot.mk _ 0

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (FreeLieAlgebra R X)
  body: Quot.map₂ (· + ·) (fun _ _ _ => Rel.addLeft _) fun _ _ _ => Rel.add_right _

中文:
实例 :
  签名: Add (FreeLieAlgebra R X)
  定义体: Quot.map₂ (· + ·) (fun _ _ _ => Rel.addLeft _) fun _ _ _ => Rel.add_right _

Depends on / 依赖: Quot.map, Rel.addLeft, Rel.add_right, addLeft, add_right
-/
instance : Add (FreeLieAlgebra R X) where
  add := Quot.map₂ (· + ·) (fun _ _ _ => Rel.addLeft _) fun _ _ _ => Rel.add_right _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (FreeLieAlgebra R X)
  body: Quot.map Neg.neg fun _ _ => Rel.neg

中文:
实例 :
  签名: Neg (FreeLieAlgebra R X)
  定义体: Quot.map Neg.neg fun _ _ => Rel.neg

Depends on / 依赖: Neg.neg, Quot.map, Rel.neg
-/
instance : Neg (FreeLieAlgebra R X) where neg := Quot.map Neg.neg fun _ _ => Rel.neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (FreeLieAlgebra R X)
  body: Quot.map₂ Sub.sub (fun _ _ _ => Rel.subLeft _) fun _ _ _ => Rel.subRight _

中文:
实例 :
  签名: Sub (FreeLieAlgebra R X)
  定义体: Quot.map₂ Sub.sub (fun _ _ _ => Rel.subLeft _) fun _ _ _ => Rel.subRight _

Depends on / 依赖: Quot.map, Rel.subLeft, Rel.subRight, Sub.sub, subLeft, subRight
-/
instance : Sub (FreeLieAlgebra R X) where
  sub := Quot.map₂ Sub.sub (fun _ _ _ => Rel.subLeft _) fun _ _ _ => Rel.subRight _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup (FreeLieAlgebra R X)
  body: Function.Surjective.addGroup (Quot.mk _) Quot.mk_surjective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: AddGroup (FreeLieAlgebra R X)
  定义体: Function.Surjective.addGroup (Quot.mk _) Quot.mk_surjective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Function, Function.Surjective.addGroup, Quot.mk, Quot.mk_surjective, Surjective, addGroup, mk_surjective
-/
instance : AddGroup (FreeLieAlgebra R X) :=
  Function.Surjective.addGroup (Quot.mk _) Quot.mk_surjective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommSemigroup (FreeLieAlgebra R X)
  body: Function.Surjective.addCommSemigroup (Quot.mk _) Quot.mk_surjective fun _ _ => rfl

中文:
实例 :
  签名: AddCommSemigroup (FreeLieAlgebra R X)
  定义体: Function.Surjective.addCommSemigroup (Quot.mk _) Quot.mk_surjective fun _ _ => rfl

Depends on / 依赖: Function, Function.Surjective.addCommSemigroup, Quot.mk, Quot.mk_surjective, Surjective, addCommSemigroup, mk_surjective
-/
instance : AddCommSemigroup (FreeLieAlgebra R X) :=
  Function.Surjective.addCommSemigroup (Quot.mk _) Quot.mk_surjective fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (FreeLieAlgebra R X)
  body: { (inferInstance : AddGroup (FreeLieAlgebra R X)),
    (inferInstance : AddCommSemigroup (FreeLieAlgebra R X)) with }

中文:
实例 :
  签名: AddCommGroup (FreeLieAlgebra R X)
  定义体: { (inferInstance : AddGroup (FreeLieAlgebra R X)),
    (inferInstance : AddCommSemigroup (FreeLieAlgebra R X)) with }

Depends on / 依赖: AddCommSemigroup, AddGroup, FreeLieAlgebra
-/
instance : AddCommGroup (FreeLieAlgebra R X) :=
  { (inferInstance : AddGroup (FreeLieAlgebra R X)),
    (inferInstance : AddCommSemigroup (FreeLieAlgebra R X)) with }

instance {S : Type*} [Semiring S] [Module S R] [IsScalarTower S R R] :
    Module S (FreeLieAlgebra R X) :=
  Function.Surjective.module S ⟨⟨Quot.mk (Rel R X), rfl⟩, fun _ _ => rfl⟩
    Quot.mk_surjective (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (FreeLieAlgebra R X)
  body: Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_left _) fun _ _ _ => Rel.mul_right _
  add_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [add_mul]
  lie_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [mul_add]
  lie_self := by rintro ⟨a⟩; exact Quot.sound (

中文:
实例 :
  签名: LieRing (FreeLieAlgebra R X)
  定义体: Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_left _) fun _ _ _ => Rel.mul_right _
  add_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [add_mul]
  lie_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [mul_add]
  lie_self := by rintro ⟨a⟩; exact Quot.sound (

Depends on / 依赖: Quot.map, Rel.mul_left, Rel.mul_right, mul_left, mul_right
-/
instance : LieRing (FreeLieAlgebra R X) where
  bracket := Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_left _) fun _ _ _ => Rel.mul_right _
  add_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [add_mul]
  lie_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [mul_add]
  lie_self := by rintro ⟨a⟩; exact Quot.sound (Rel.lie_self a)
  leibniz_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact Quot.sound (Rel.leibniz_lie a b c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra R (FreeLieAlgebra R X)
  body: by
    rintro t ⟨a⟩ ⟨c⟩
    change Quot.mk _ (a • t • c) = Quot.mk _ (t • a • c)
    rw [← smul_comm]

中文:
实例 :
  签名: LieAlgebra R (FreeLieAlgebra R X)
  定义体: by
    rintro t ⟨a⟩ ⟨c⟩
    change Quot.mk _ (a • t • c) = Quot.mk _ (t • a • c)
    rw [← smul_comm]

Depends on / 依赖: Quot.mk, smul_comm
-/
instance : LieAlgebra R (FreeLieAlgebra R X) where
  lie_smul := by
    rintro t ⟨a⟩ ⟨c⟩
    change Quot.mk _ (a • t • c) = Quot.mk _ (t • a • c)
    rw [← smul_comm]

variable {X}

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : X -> FreeLieAlgebra R X
  body: fun x => Quot.mk _ (lib.of R x)

中文:
定义 of
  签名: : X -> FreeLieAlgebra R X
  定义体: fun x => Quot.mk _ (lib.of R x)

Depends on / 依赖: Quot.mk, lib.of
-/
def of : X -> FreeLieAlgebra R X := fun x => Quot.mk _ (lib.of R x)

variable {L : Type w} [LieRing L] [LieAlgebra R L]

/--
Definition of `liftAux` / `liftAux` 的定义

English:
definition liftAux
  signature: (f : X -> CommutatorRing L)
  body: lib.lift R f

中文:
定义 liftAux
  签名: (f : X -> CommutatorRing L)
  定义体: lib.lift R f

Depends on / 依赖: lib.lift
-/
def liftAux (f : X -> CommutatorRing L) :=
  lib.lift R f

/--
theorem `liftAux_map_smul` / 定理 `liftAux_map_smul`

English:
theorem liftAux_map_smul
  given: (f : X -> L) (t : R) (a : lib R X)
  proof: map_smul _ t a

中文:
定理 liftAux_map_smul
  条件: (f : X -> L) (t : R) (a : lib R X)
  证明: map_smul _ t a

Depends on / 依赖: map_smul
-/
theorem liftAux_map_smul (f : X -> L) (t : R) (a : lib R X) :
    liftAux R f (t • a) = t • liftAux R f a :=
  map_smul _ t a

/--
theorem `liftAux_map_add` / 定理 `liftAux_map_add`

English:
theorem liftAux_map_add
  given: (f : X -> L) (a b : lib R X)
  proof: map_add _ a b

中文:
定理 liftAux_map_add
  条件: (f : X -> L) (a b : lib R X)
  证明: map_add _ a b

Depends on / 依赖: map_add
-/
theorem liftAux_map_add (f : X -> L) (a b : lib R X) :
    liftAux R f (a + b) = liftAux R f a + liftAux R f b :=
  map_add _ a b

/--
theorem `liftAux_map_mul` / 定理 `liftAux_map_mul`

English:
theorem liftAux_map_mul
  given: (f : X -> L) (a b : lib R X)
  proof: map_mul _ a b

中文:
定理 liftAux_map_mul
  条件: (f : X -> L) (a b : lib R X)
  证明: map_mul _ a b

Depends on / 依赖: map_mul
-/
theorem liftAux_map_mul (f : X -> L) (a b : lib R X) :
    liftAux R f (a * b) = ⁅liftAux R f a, liftAux R f b⁆ :=
  map_mul _ a b

/--
theorem `liftAux_spec` / 定理 `liftAux_spec`

English:
theorem liftAux_spec
  given: (f : X -> L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b)
  proof: by
  induction h with
  | lie_self a' => simp only [liftAux_map_mul, map_zero, lie_self]
  | leibniz_lie a' b' c' =>
    simp only [liftAux_map_mul, liftAux_map_add, sub_add_cancel, lie_lie]
  | smul b' _ h₂ => simp only [liftAux_map_smul, h₂]
  | add_right c' _ h₂ => simp only [liftAux_map_add, h₂]

中文:
定理 liftAux_spec
  条件: (f : X -> L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b)
  证明: by
  induction h with
  | lie_self a' => simp only [liftAux_map_mul, map_zero, lie_self]
  | leibniz_lie a' b' c' =>
    simp only [liftAux_map_mul, liftAux_map_add, sub_add_cancel, lie_lie]
  | smul b' _ h₂ => simp only [liftAux_map_smul, h₂]
  | add_right c' _ h₂ => simp only [liftAux_map_add, h₂]

Depends on / 依赖: add_right, leibniz_lie, lie_lie, lie_self, liftAux_map_add, liftAux_map_mul, liftAux_map_smul, map_zero, mul_left, mul_right, sub_add_cancel
-/
theorem liftAux_spec (f : X -> L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b) :
    liftAux R f a = liftAux R f b := by
  induction h with
  | lie_self a' => simp only [liftAux_map_mul, map_zero, lie_self]
  | leibniz_lie a' b' c' =>
    simp only [liftAux_map_mul, liftAux_map_add, sub_add_cancel, lie_lie]
  | smul b' _ h₂ => simp only [liftAux_map_smul, h₂]
  | add_right c' _ h₂ => simp only [liftAux_map_add, h₂]
  | mul_left c' _ h₂ => simp only [liftAux_map_mul, h₂]
  | mul_right c' _ h₂ => simp only [liftAux_map_mul, h₂]

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : lib R X ->ₙₐ[R] CommutatorRing (FreeLieAlgebra R X) where
  body: Quot.mk (Rel R X)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 mk
  签名: : lib R X ->ₙₐ[R] CommutatorRing (FreeLieAlgebra R X) where
  定义体: Quot.mk (Rel R X)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: Quot.mk
-/
def mk : lib R X ->ₙₐ[R] CommutatorRing (FreeLieAlgebra R X) where
  toFun := Quot.mk (Rel R X)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (X -> L) ≃ (FreeLieAlgebra R X ->ₗ⁅R⁆ L) where
  body: { toFun := fun c => Quot.liftOn c (liftAux R f) (liftAux_spec R f)
      map_add' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_add]; rfl
      map_smul' := by rintro t ⟨a⟩; rw [← liftAux_map_smul]; rfl
      map_lie' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_mul]; rfl }
  invFun F := F ∘ of R
  left_inv f 

中文:
定义 lift
  签名: : (X -> L) ≃ (FreeLieAlgebra R X ->ₗ⁅R⁆ L) where
  定义体: { toFun := fun c => Quot.liftOn c (liftAux R f) (liftAux_spec R f)
      map_add' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_add]; rfl
      map_smul' := by rintro t ⟨a⟩; rw [← liftAux_map_smul]; rfl
      map_lie' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_mul]; rfl }
  invFun F := F ∘ of R
  left_inv f 

Depends on / 依赖: F.toNonUnitalAlgHom.comp, Function, Function.comp_apply, LieHom, LieHom.coe_mk, NonUnitalAlgHom, NonUnitalAlgHom.congr_fun, Quot.liftOn, coe_mk, comp_apply, congr_fun, invFun, left_inv, lib.lift_comp_of, lib.lift_of_apply, liftAux, liftAux_map_add, liftAux_map_mul, liftAux_map_smul, liftAux_spec
-/
def lift : (X -> L) ≃ (FreeLieAlgebra R X ->ₗ⁅R⁆ L) where
  toFun f :=
    { toFun := fun c => Quot.liftOn c (liftAux R f) (liftAux_spec R f)
      map_add' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_add]; rfl
      map_smul' := by rintro t ⟨a⟩; rw [← liftAux_map_smul]; rfl
      map_lie' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_mul]; rfl }
  invFun F := F ∘ of R
  left_inv f := by
    ext x
    simp only [liftAux, of, LieHom.coe_mk, Function.comp_apply, lib.lift_of_apply]
  right_inv F := by
    ext ⟨a⟩
    let F' := F.toNonUnitalAlgHom.comp (mk R)
    exact NonUnitalAlgHom.congr_fun (lib.lift_comp_of R F') a

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  statement: (lift R).symm F = F ∘ of R
  proof: rfl

中文:
定理 lift_symm_apply
  条件: (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  结论: (lift R).symm F = F ∘ of R
  证明: rfl
-/
theorem lift_symm_apply (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L) : (lift R).symm F = F ∘ of R := rfl

variable {R}

@[simp]
/--
theorem `of_comp_lift` / 定理 `of_comp_lift`

English:
theorem of_comp_lift
  given: (f : X -> L)
  statement: lift R f ∘ of R = f
  proof: (lift R).left_inv f

@[simp]

中文:
定理 of_comp_lift
  条件: (f : X -> L)
  结论: lift R f ∘ of R = f
  证明: (lift R).left_inv f

@[simp]

Depends on / 依赖: left_inv
-/
theorem of_comp_lift (f : X -> L) : lift R f ∘ of R = f := (lift R).left_inv f

@[simp]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (f : X -> L) (g : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  statement: g ∘ of R = f ↔ g = lift R f
  proof: (lift R).symm_apply_eq

@[simp]

中文:
定理 lift_unique
  条件: (f : X -> L) (g : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  结论: g ∘ of R = f ↔ g = lift R f
  证明: (lift R).symm_apply_eq

@[simp]

Depends on / 依赖: symm_apply_eq
-/
theorem lift_unique (f : X -> L) (g : FreeLieAlgebra R X ->ₗ⁅R⁆ L) : g ∘ of R = f ↔ g = lift R f :=
  (lift R).symm_apply_eq

@[simp]
/--
theorem `lift_of_apply` / 定理 `lift_of_apply`

English:
theorem lift_of_apply
  given: (f : X -> L) (x)
  statement: lift R f (of R x) = f x
  proof: by
  rw [← @Function.comp_apply _ _ _ (lift R f) (of R) x]; rw [of_comp_lift]

@[simp]

中文:
定理 lift_of_apply
  条件: (f : X -> L) (x)
  结论: lift R f (of R x) = f x
  证明: by
  rw [← @Function.comp_apply _ _ _ (lift R f) (of R) x]; rw [of_comp_lift]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, of_comp_lift
-/
theorem lift_of_apply (f : X -> L) (x) : lift R f (of R x) = f x := by
  rw [← @Function.comp_apply _ _ _ (lift R f) (of R) x]; rw [of_comp_lift]

@[simp]
/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  statement: lift R (F ∘ of R) = F
  proof: by
  rw [← lift_symm_apply]; exact (lift R).apply_symm_apply F

@[ext]

中文:
定理 lift_comp_of
  条件: (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L)
  结论: lift R (F ∘ of R) = F
  证明: by
  rw [← lift_symm_apply]; exact (lift R).apply_symm_apply F

@[ext]

Depends on / 依赖: apply_symm_apply, lift_symm_apply
-/
theorem lift_comp_of (F : FreeLieAlgebra R X ->ₗ⁅R⁆ L) : lift R (F ∘ of R) = F := by
  rw [← lift_symm_apply]; exact (lift R).apply_symm_apply F

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {F₁ F₂ : FreeLieAlgebra R X ->ₗ⁅R⁆ L} (h : forall x, F₁ (of R x) = F₂ (of R x))
  proof: have h' : (lift R).symm F₁ = (lift R).symm F₂ := by ext; simp [h]
  (lift R).symm.injective h'

中文:
定理 hom_ext
  条件: {F₁ F₂ : FreeLieAlgebra R X ->ₗ⁅R⁆ L} (h : 对任意 x, F₁ (of R x) = F₂ (of R x))
  证明: have h' : (lift R).symm F₁ = (lift R).symm F₂ := by ext; simp [h]
  (lift R).symm.injective h'

Depends on / 依赖: injective, symm.injective
-/
theorem hom_ext {F₁ F₂ : FreeLieAlgebra R X ->ₗ⁅R⁆ L} (h : forall x, F₁ (of R x) = F₂ (of R x)) :
    F₁ = F₂ :=
  have h' : (lift R).symm F₁ = (lift R).symm F₂ := by ext; simp [h]
  (lift R).symm.injective h'

variable (R X)
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The universal enveloping algebra of the free Lie algebra is just the free unital associative
algebra. -/
@[simps!]
/--
Definition of `universalEnvelopingEquivFreeAlgebra` / `universalEnvelopingEquivFreeAlgebra` 的定义

English:
definition universalEnvelopingEquivFreeAlgebra
  signature: :
  body: AlgEquiv.ofAlgHom (UniversalEnvelopingAlgebra.lift R <| FreeLieAlgebra.lift R <| FreeAlgebra.ι R)
    (FreeAlgebra.lift R <| UniversalEnvelopingAlgebra.ι R ∘ FreeLieAlgebra.of R) (by ext; simp)
    (by ext; simp)

中文:
定义 universalEnvelopingEquivFreeAlgebra
  签名: :
  定义体: AlgEquiv.ofAlgHom (UniversalEnvelopingAlgebra.lift R <| FreeLieAlgebra.lift R <| FreeAlgebra.ι R)
    (FreeAlgebra.lift R <| UniversalEnvelopingAlgebra.ι R ∘ FreeLieAlgebra.of R) (by ext; simp)
    (by ext; simp)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, FreeAlgebra, FreeAlgebra.lift, FreeLieAlgebra, FreeLieAlgebra.lift, FreeLieAlgebra.of, UniversalEnvelopingAlgebra, UniversalEnvelopingAlgebra.lift, ofAlgHom
-/
def universalEnvelopingEquivFreeAlgebra :
    UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) ≃ₐ[R] FreeAlgebra R X :=
  AlgEquiv.ofAlgHom (UniversalEnvelopingAlgebra.lift R <| FreeLieAlgebra.lift R <| FreeAlgebra.ι R)
    (FreeAlgebra.lift R <| UniversalEnvelopingAlgebra.ι R ∘ FreeLieAlgebra.of R) (by ext; simp)
    (by ext; simp)

end FreeLieAlgebra
