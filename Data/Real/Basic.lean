/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.

The fact that the real numbers are a (trivial) \*-ring has similarly been deferred to
`Mathlib/Data/Real/Star.lean`.
-/

@[expose] public section


assert_not_exists Finset Module Submonoid FloorRing

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
@[wikidata Q12916, wikidata Q2584477]
/--
Definition of `Real` / `Real` 的定义

English:
structure Real
  parameters: where ofCauchy
  (no additional axioms)

中文:
结构 实数
  参数: where ofCauchy
  (无附加公理)
-/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : Rat -> Rat)

@[inherit_doc]
notation "Real" => Real

namespace CauSeq.Completion

-- this can't go in `Data.Real.CauSeqCompletion` as the structure on `ℚ` isn't available
@[simp]
/--
theorem `ofRat_rat` / 定理 `ofRat_rat`

English:
theorem ofRat_rat
  given: {abv : Rat -> Rat} [IsAbsoluteValue abv] (q : Rat)
  proof: rfl

中文:
定理 ofRat_rat
  条件: {abv : 有理数 -> 有理数} [是绝对值 abv] (q : 有理数)
  证明: rfl
-/
theorem ofRat_rat {abv : Rat -> Rat} [IsAbsoluteValue abv] (q : Rat) :
    ofRat (q : Rat) = (q : Cauchy abv) :=
  rfl

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x : Real}

/--
theorem `ext_cauchy_iff` / 定理 `ext_cauchy_iff`

English:
theorem ext_cauchy_iff
  statement: forall {x y : Real}, x = y ↔ x.cauchy = y.cauchy

中文:
定理 ext_cauchy_iff
  结论: 对任意 {x y : 实数}, x = y ↔ x.cauchy = y.cauchy
-/
theorem ext_cauchy_iff : forall {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [ofCauchy.injEq]

/--
theorem `ext_cauchy` / 定理 `ext_cauchy`

English:
theorem ext_cauchy
  given: {x y : Real}
  statement: x.cauchy = y.cauchy -> x = y
  proof: ext_cauchy_iff.2

中文:
定理 ext_cauchy
  条件: {x y : 实数}
  结论: x.cauchy = y.cauchy -> x = y
  证明: ext_cauchy_iff.2

Depends on / 依赖: ext_cauchy_iff
-/
theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy -> x = y :=
  ext_cauchy_iff.2

/--
Definition of `equivCauchy` / `equivCauchy` 的定义

English:
definition equivCauchy
  signature: : Real ≃ CauSeq.Completion.Cauchy (abs : Rat -> Rat)
  body: ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

中文:
定义 equivCauchy
  签名: : 实数 ≃ CauSeq.完备化.Cauchy (abs : 有理数 -> 有理数)
  定义体: ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

Depends on / 依赖: Real.cauchy, Real.ofCauchy, cauchy, ofCauchy
-/
def equivCauchy : Real ≃ CauSeq.Completion.Cauchy (abs : Rat -> Rat) :=
  ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

set_option backward.privateInPublic true in
-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : Real :=
  ⟨0⟩

set_option backward.privateInPublic true in
private irreducible_def one : Real :=
  ⟨1⟩

set_option backward.privateInPublic true in
private irreducible_def add : Real -> Real -> Real
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private irreducible_def neg : Real -> Real
  | ⟨a⟩ => ⟨-a⟩

set_option backward.privateInPublic true in
private irreducible_def mul : Real -> Real -> Real
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

set_option backward.privateInPublic true in
private noncomputable irreducible_def inv' : Real -> Real
  | ⟨a⟩ => ⟨a⁻¹⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Real
  body: ⟨zero⟩

中文:
实例 :
  签名: 零 实数
  定义体: ⟨zero⟩
-/
instance : Zero Real :=
  ⟨zero⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Real
  body: ⟨one⟩

中文:
实例 :
  签名: 幺 实数
  定义体: ⟨one⟩
-/
instance : One Real :=
  ⟨one⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add Real
  body: ⟨add⟩

中文:
实例 :
  签名: 加法 实数
  定义体: ⟨add⟩
-/
instance : Add Real :=
  ⟨add⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg Real
  body: ⟨neg⟩

中文:
实例 :
  签名: 取负 实数
  定义体: ⟨neg⟩
-/
instance : Neg Real :=
  ⟨neg⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul Real
  body: ⟨mul⟩

中文:
实例 :
  签名: 乘法 实数
  定义体: ⟨mul⟩
-/
instance : Mul Real :=
  ⟨mul⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub Real
  body: ⟨fun a b => a + -b⟩

中文:
实例 :
  签名: 减法 实数
  定义体: ⟨fun a b => a + -b⟩
-/
instance : Sub Real :=
  ⟨fun a b => a + -b⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv Real
  body: ⟨inv'⟩

中文:
实例 :
  签名: 取逆 实数
  定义体: ⟨inv'⟩
-/
noncomputable instance : Inv Real :=
  ⟨inv'⟩

/--
theorem `ofCauchy_zero` / 定理 `ofCauchy_zero`

English:
theorem ofCauchy_zero
  statement: (⟨0⟩ : Real) = 0
  proof: zero_def.symm

中文:
定理 ofCauchy_zero
  结论: (⟨0⟩ : 实数) = 0
  证明: zero_def.symm

Depends on / 依赖: zero_def, zero_def.symm
-/
theorem ofCauchy_zero : (⟨0⟩ : Real) = 0 :=
  zero_def.symm

/--
theorem `ofCauchy_one` / 定理 `ofCauchy_one`

English:
theorem ofCauchy_one
  statement: (⟨1⟩ : Real) = 1
  proof: one_def.symm

中文:
定理 ofCauchy_one
  结论: (⟨1⟩ : 实数) = 1
  证明: one_def.symm

Depends on / 依赖: one_def, one_def.symm
-/
theorem ofCauchy_one : (⟨1⟩ : Real) = 1 :=
  one_def.symm

/--
theorem `ofCauchy_add` / 定理 `ofCauchy_add`

English:
theorem ofCauchy_add
  given: (a b)
  statement: (⟨a + b⟩ : Real) = ⟨a⟩ + ⟨b⟩
  proof: (add_def _ _).symm

中文:
定理 ofCauchy_add
  条件: (a b)
  结论: (⟨a + b⟩ : 实数) = ⟨a⟩ + ⟨b⟩
  证明: (add_def _ _).symm

Depends on / 依赖: add_def
-/
theorem ofCauchy_add (a b) : (⟨a + b⟩ : Real) = ⟨a⟩ + ⟨b⟩ :=
  (add_def _ _).symm

/--
theorem `ofCauchy_neg` / 定理 `ofCauchy_neg`

English:
theorem ofCauchy_neg
  given: (a)
  statement: (⟨-a⟩ : Real) = -⟨a⟩
  proof: (neg_def _).symm

中文:
定理 ofCauchy_neg
  条件: (a)
  结论: (⟨-a⟩ : 实数) = -⟨a⟩
  证明: (neg_def _).symm

Depends on / 依赖: neg_def
-/
theorem ofCauchy_neg (a) : (⟨-a⟩ : Real) = -⟨a⟩ :=
  (neg_def _).symm

/--
theorem `ofCauchy_sub` / 定理 `ofCauchy_sub`

English:
theorem ofCauchy_sub
  given: (a b)
  statement: (⟨a - b⟩ : Real) = ⟨a⟩ - ⟨b⟩
  proof: by
  rw [sub_eq_add_neg]; rw [ofCauchy_add]; rw [ofCauchy_neg]
  rfl

中文:
定理 ofCauchy_sub
  条件: (a b)
  结论: (⟨a - b⟩ : 实数) = ⟨a⟩ - ⟨b⟩
  证明: by
  rw [sub_eq_add_neg]; rw [ofCauchy_add]; rw [ofCauchy_neg]
  rfl

Depends on / 依赖: ofCauchy_add, ofCauchy_neg, sub_eq_add_neg
-/
theorem ofCauchy_sub (a b) : (⟨a - b⟩ : Real) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg]; rw [ofCauchy_add]; rw [ofCauchy_neg]
  rfl

/--
theorem `ofCauchy_mul` / 定理 `ofCauchy_mul`

English:
theorem ofCauchy_mul
  given: (a b)
  statement: (⟨a * b⟩ : Real) = ⟨a⟩ * ⟨b⟩
  proof: (mul_def _ _).symm

中文:
定理 ofCauchy_mul
  条件: (a b)
  结论: (⟨a * b⟩ : 实数) = ⟨a⟩ * ⟨b⟩
  证明: (mul_def _ _).symm

Depends on / 依赖: mul_def
-/
theorem ofCauchy_mul (a b) : (⟨a * b⟩ : Real) = ⟨a⟩ * ⟨b⟩ :=
  (mul_def _ _).symm

/--
theorem `ofCauchy_inv` / 定理 `ofCauchy_inv`

English:
theorem ofCauchy_inv
  given: {f}
  statement: (⟨f⁻¹⟩ : Real) = ⟨f⟩⁻¹
  proof: show _ = inv' _ by rw [inv']

中文:
定理 ofCauchy_inv
  条件: {f}
  结论: (⟨f⁻¹⟩ : 实数) = ⟨f⟩⁻¹
  证明: show _ = inv' _ by rw [inv']
-/
theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : Real) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']

/--
theorem `cauchy_zero` / 定理 `cauchy_zero`

English:
theorem cauchy_zero
  statement: (0 : Real).cauchy = 0
  proof: show zero.cauchy = 0 by rw [zero_def]

中文:
定理 cauchy_zero
  结论: (0 : 实数).cauchy = 0
  证明: show zero.cauchy = 0 by rw [zero_def]

Depends on / 依赖: cauchy, zero.cauchy, zero_def
-/
theorem cauchy_zero : (0 : Real).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero_def]

/--
theorem `cauchy_one` / 定理 `cauchy_one`

English:
theorem cauchy_one
  statement: (1 : Real).cauchy = 1
  proof: show one.cauchy = 1 by rw [one_def]

中文:
定理 cauchy_one
  结论: (1 : 实数).cauchy = 1
  证明: show one.cauchy = 1 by rw [one_def]

Depends on / 依赖: cauchy, one.cauchy, one_def
-/
theorem cauchy_one : (1 : Real).cauchy = 1 :=
  show one.cauchy = 1 by rw [one_def]

/--
theorem `cauchy_add` / 定理 `cauchy_add`

English:
theorem cauchy_add
  statement: forall a b, (a + b : Real).cauchy = a.cauchy + b.cauchy

中文:
定理 cauchy_add
  结论: 对任意 a b, (a + b : 实数).cauchy = a.cauchy + b.cauchy
-/
theorem cauchy_add : forall a b, (a + b : Real).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add_def]

/--
theorem `cauchy_neg` / 定理 `cauchy_neg`

English:
theorem cauchy_neg
  statement: forall a, (-a : Real).cauchy = -a.cauchy

中文:
定理 cauchy_neg
  结论: 对任意 a, (-a : 实数).cauchy = -a.cauchy
-/
theorem cauchy_neg : forall a, (-a : Real).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg_def]

/--
theorem `cauchy_mul` / 定理 `cauchy_mul`

English:
theorem cauchy_mul
  statement: forall a b, (a * b : Real).cauchy = a.cauchy * b.cauchy

中文:
定理 cauchy_mul
  结论: 对任意 a b, (a * b : 实数).cauchy = a.cauchy * b.cauchy
-/
theorem cauchy_mul : forall a b, (a * b : Real).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul_def]

/--
theorem `cauchy_sub` / 定理 `cauchy_sub`

English:
theorem cauchy_sub
  statement: forall a b, (a - b : Real).cauchy = a.cauchy - b.cauchy

中文:
定理 cauchy_sub
  结论: 对任意 a b, (a - b : 实数).cauchy = a.cauchy - b.cauchy
-/
theorem cauchy_sub : forall a b, (a - b : Real).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg]; rw [← cauchy_neg]; rw [← cauchy_add]
    rfl

/--
theorem `cauchy_inv` / 定理 `cauchy_inv`

English:
theorem cauchy_inv
  statement: forall f, (f⁻¹ : Real).cauchy = f.cauchy⁻¹

中文:
定理 cauchy_inv
  结论: 对任意 f, (f⁻¹ : 实数).cauchy = f.cauchy⁻¹
-/
theorem cauchy_inv : forall f, (f⁻¹ : Real).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast Real where natCast n
  body: ⟨n⟩

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 实数 where natCast n
  定义体: ⟨n⟩
-/
instance instNatCast : NatCast Real where natCast n := ⟨n⟩
/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast Real where intCast z
  body: ⟨z⟩

中文:
实例 inst整数Cast
  签名: : 整数嵌入 实数 where intCast z
  定义体: ⟨z⟩
-/
instance instIntCast : IntCast Real where intCast z := ⟨z⟩
/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast Real where nnratCast q
  body: ⟨q⟩

中文:
实例 instNNRatCast
  签名: : 非负有理数嵌入 实数 where nnratCast q
  定义体: ⟨q⟩
-/
instance instNNRatCast : NNRatCast Real where nnratCast q := ⟨q⟩
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: : RatCast Real where ratCast q
  body: ⟨q⟩

中文:
实例 instRatCast
  签名: : 有理数嵌入 实数 where ratCast q
  定义体: ⟨q⟩
-/
instance instRatCast : RatCast Real where ratCast q := ⟨q⟩

/--
lemma `ofCauchy_natCast` / 引理 `ofCauchy_natCast`

English:
lemma ofCauchy_natCast
  given: (n : Nat)
  statement: (⟨n⟩ : Real) = n
  proof: rfl

中文:
引理 ofCauchy_natCast
  条件: (n : 自然数)
  结论: (⟨n⟩ : 实数) = n
  证明: rfl
-/
lemma ofCauchy_natCast (n : Nat) : (⟨n⟩ : Real) = n := rfl
/--
lemma `ofCauchy_intCast` / 引理 `ofCauchy_intCast`

English:
lemma ofCauchy_intCast
  given: (z : Int)
  statement: (⟨z⟩ : Real) = z
  proof: rfl

中文:
引理 ofCauchy_intCast
  条件: (z : 整数)
  结论: (⟨z⟩ : 实数) = z
  证明: rfl
-/
lemma ofCauchy_intCast (z : Int) : (⟨z⟩ : Real) = z := rfl
/--
lemma `ofCauchy_nnratCast` / 引理 `ofCauchy_nnratCast`

English:
lemma ofCauchy_nnratCast
  given: (q : Rat>=0)
  statement: (⟨q⟩ : Real) = q
  proof: rfl

中文:
引理 ofCauchy_nnratCast
  条件: (q : 有理数>=0)
  结论: (⟨q⟩ : 实数) = q
  证明: rfl
-/
lemma ofCauchy_nnratCast (q : Rat>=0) : (⟨q⟩ : Real) = q := rfl
/--
lemma `ofCauchy_ratCast` / 引理 `ofCauchy_ratCast`

English:
lemma ofCauchy_ratCast
  given: (q : Rat)
  statement: (⟨q⟩ : Real) = q
  proof: rfl

中文:
引理 ofCauchy_ratCast
  条件: (q : 有理数)
  结论: (⟨q⟩ : 实数) = q
  证明: rfl
-/
lemma ofCauchy_ratCast (q : Rat) : (⟨q⟩ : Real) = q := rfl

/--
lemma `cauchy_natCast` / 引理 `cauchy_natCast`

English:
lemma cauchy_natCast
  given: (n : Nat)
  statement: (n : Real).cauchy = n
  proof: rfl

中文:
引理 cauchy_natCast
  条件: (n : 自然数)
  结论: (n : 实数).cauchy = n
  证明: rfl
-/
lemma cauchy_natCast (n : Nat) : (n : Real).cauchy = n := rfl
/--
lemma `cauchy_intCast` / 引理 `cauchy_intCast`

English:
lemma cauchy_intCast
  given: (z : Int)
  statement: (z : Real).cauchy = z
  proof: rfl

中文:
引理 cauchy_intCast
  条件: (z : 整数)
  结论: (z : 实数).cauchy = z
  证明: rfl
-/
lemma cauchy_intCast (z : Int) : (z : Real).cauchy = z := rfl
/--
lemma `cauchy_nnratCast` / 引理 `cauchy_nnratCast`

English:
lemma cauchy_nnratCast
  given: (q : Rat>=0)
  statement: (q : Real).cauchy = q
  proof: rfl

中文:
引理 cauchy_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : 实数).cauchy = q
  证明: rfl
-/
lemma cauchy_nnratCast (q : Rat>=0) : (q : Real).cauchy = q := rfl
/--
lemma `cauchy_ratCast` / 引理 `cauchy_ratCast`

English:
lemma cauchy_ratCast
  given: (q : Rat)
  statement: (q : Real).cauchy = q
  proof: rfl

中文:
引理 cauchy_ratCast
  条件: (q : 有理数)
  结论: (q : 实数).cauchy = q
  证明: rfl
-/
lemma cauchy_ratCast (q : Rat) : (q : Real).cauchy = q := rfl

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing Real where
  body: ⟨n⟩
  intCast z := ⟨z⟩
  npow := @npowRec Real ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec Real ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg Real _⟩ (@nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]

中文:
实例 commRing
  签名: : 交换环 实数 where
  定义体: ⟨n⟩
  intCast z := ⟨z⟩
  npow := @npowRec Real ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec Real ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg Real _⟩ (@nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]
-/
instance commRing : CommRing Real where
  natCast n := ⟨n⟩
  intCast z := ⟨z⟩
  npow := @npowRec Real ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec Real ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg Real _⟩ (@nsmulRec Real ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]

/-- `Real.equivCauchy` as a ring equivalence. -/
@[simps]
/--
Definition of `ringEquivCauchy` / `ringEquivCauchy` 的定义

English:
definition ringEquivCauchy
  signature: : Real ≃+* CauSeq.Completion.Cauchy (abs : Rat -> Rat)
  body: { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }

中文:
定义 ringEquivCauchy
  签名: : 实数 ≃+* CauSeq.完备化.Cauchy (abs : 有理数 -> 有理数)
  定义体: { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }

Depends on / 依赖: cauchy, cauchy_add, cauchy_mul, equivCauchy, invFun, map_add, map_mul, ofCauchy
-/
def ringEquivCauchy : Real ≃+* CauSeq.Completion.Cauchy (abs : Rat -> Rat) :=
  { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }


/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: : Ring Real
  body: by infer_instance

中文:
实例 instRing
  签名: : 环 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance instRing : Ring Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring Real
  body: by infer_instance

中文:
实例 :
  签名: 交换半环 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommSemiring Real := by infer_instance

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: : Semiring Real
  body: by infer_instance

中文:
实例 semiring
  签名: : 半环 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance semiring : Semiring Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero Real
  body: by infer_instance

中文:
实例 :
  签名: 带零交换幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommMonoidWithZero Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZero Real
  body: by infer_instance

中文:
实例 :
  签名: 带零幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : MonoidWithZero Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法交换群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddCommGroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddGroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid Real
  body: by infer_instance

中文:
实例 :
  签名: 加法交换幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddCommMonoid Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid Real
  body: by infer_instance

中文:
实例 :
  签名: 加法幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddMonoid Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddLeftCancelSemigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法左消去半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddLeftCancelSemigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddRightCancelSemigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法右消去半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddRightCancelSemigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommSemigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法交换半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddCommSemigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSemigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 加法半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : AddSemigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid Real
  body: by infer_instance

中文:
实例 :
  签名: 交换幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommMonoid Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid Real
  body: by infer_instance

中文:
实例 :
  签名: 幺半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Monoid Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 交换半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : CommSemigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semigroup Real
  body: by infer_instance

中文:
实例 :
  签名: 半群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Semigroup Real := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Real
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 实数
  定义体: ⟨0⟩
-/
instance : Inhabited Real :=
  ⟨0⟩

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : CauSeq Rat abs)
  body: ⟨CauSeq.Completion.mk x⟩

中文:
定义 mk
  签名: (x : CauSeq 有理数 abs)
  定义体: ⟨CauSeq.Completion.mk x⟩

Depends on / 依赖: CauSeq, CauSeq.Completion.mk, Completion
-/
def mk (x : CauSeq Rat abs) : Real :=
  ⟨CauSeq.Completion.mk x⟩

/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: {f g : CauSeq Rat abs}
  statement: mk f = mk g ↔ f ≈ g
  proof: ext_cauchy_iff.trans CauSeq.Completion.mk_eq

中文:
定理 mk_eq
  条件: {f g : CauSeq 有理数 abs}
  结论: mk f = mk g ↔ f ≈ g
  证明: ext_cauchy_iff.trans CauSeq.Completion.mk_eq

Depends on / 依赖: CauSeq, CauSeq.Completion.mk_eq, Completion, ext_cauchy_iff, ext_cauchy_iff.trans, mk_eq
-/
theorem mk_eq {f g : CauSeq Rat abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans CauSeq.Completion.mk_eq

set_option backward.privateInPublic true in
private irreducible_def lt : Real -> Real -> Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg =>
propext
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT Real
  body: ⟨lt⟩

中文:
实例 :
  签名: LT 实数
  定义体: ⟨lt⟩
-/
instance : LT Real :=
  ⟨lt⟩

/--
theorem `lt_cauchy` / 定理 `lt_cauchy`

English:
theorem lt_cauchy
  given: {f g}
  statement: (⟨⟦f⟧⟩ : Real) < ⟨⟦g⟧⟩ ↔ f < g
  proof: show lt _ _ ↔ _ by rw [lt_def]; rfl

@[simp]

中文:
定理 lt_cauchy
  条件: {f g}
  结论: (⟨⟦f⟧⟩ : 实数) < ⟨⟦g⟧⟩ ↔ f < g
  证明: show lt _ _ ↔ _ by rw [lt_def]; rfl

@[simp]

Depends on / 依赖: lt_def
-/
theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : Real) < ⟨⟦g⟧⟩ ↔ f < g :=
  show lt _ _ ↔ _ by rw [lt_def]; rfl

@[simp]
/--
theorem `mk_lt` / 定理 `mk_lt`

English:
theorem mk_lt
  given: {f g : CauSeq Rat abs}
  statement: mk f < mk g ↔ f < g
  proof: lt_cauchy

中文:
定理 mk_lt
  条件: {f g : CauSeq 有理数 abs}
  结论: mk f < mk g ↔ f < g
  证明: lt_cauchy

Depends on / 依赖: lt_cauchy
-/
theorem mk_lt {f g : CauSeq Rat abs} : mk f < mk g ↔ f < g :=
  lt_cauchy

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk 0 = 0
  proof: by rw [← ofCauchy_zero]; rfl

中文:
定理 mk_zero
  结论: mk 0 = 0
  证明: by rw [← ofCauchy_zero]; rfl

Depends on / 依赖: ofCauchy_zero
-/
theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl

/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  statement: mk 1 = 1
  proof: by rw [← ofCauchy_one]; rfl

中文:
定理 mk_one
  结论: mk 1 = 1
  证明: by rw [← ofCauchy_one]; rfl

Depends on / 依赖: ofCauchy_one
-/
theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl

/--
theorem `mk_add` / 定理 `mk_add`

English:
theorem mk_add
  given: {f g : CauSeq Rat abs}
  statement: mk (f + g) = mk f + mk g
  proof: by simp [mk, ← ofCauchy_add]

中文:
定理 mk_add
  条件: {f g : CauSeq 有理数 abs}
  结论: mk (f + g) = mk f + mk g
  证明: by simp [mk, ← ofCauchy_add]

Depends on / 依赖: ofCauchy_add
-/
theorem mk_add {f g : CauSeq Rat abs} : mk (f + g) = mk f + mk g := by simp [mk, ← ofCauchy_add]

/--
theorem `mk_mul` / 定理 `mk_mul`

English:
theorem mk_mul
  given: {f g : CauSeq Rat abs}
  statement: mk (f * g) = mk f * mk g
  proof: by simp [mk, ← ofCauchy_mul]

中文:
定理 mk_mul
  条件: {f g : CauSeq 有理数 abs}
  结论: mk (f * g) = mk f * mk g
  证明: by simp [mk, ← ofCauchy_mul]

Depends on / 依赖: ofCauchy_mul
-/
theorem mk_mul {f g : CauSeq Rat abs} : mk (f * g) = mk f * mk g := by simp [mk, ← ofCauchy_mul]

/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: {f : CauSeq Rat abs}
  statement: mk (-f) = -mk f
  proof: by simp [mk, ← ofCauchy_neg]

@[simp]

中文:
定理 mk_neg
  条件: {f : CauSeq 有理数 abs}
  结论: mk (-f) = -mk f
  证明: by simp [mk, ← ofCauchy_neg]

@[simp]

Depends on / 依赖: ofCauchy_neg
-/
theorem mk_neg {f : CauSeq Rat abs} : mk (-f) = -mk f := by simp [mk, ← ofCauchy_neg]

@[simp]
/--
theorem `mk_pos` / 定理 `mk_pos`

English:
theorem mk_pos
  given: {f : CauSeq Rat abs}
  statement: 0 < mk f ↔ Pos f
  proof: by
  rw [← mk_zero]; rw [mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

中文:
定理 mk_pos
  条件: {f : CauSeq 有理数 abs}
  结论: 0 < mk f ↔ Pos f
  证明: by
  rw [← mk_zero]; rw [mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

Depends on / 依赖: congr_arg, iff_of_eq, mk_lt, mk_zero, sub_zero
-/
theorem mk_pos {f : CauSeq Rat abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero]; rw [mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

/--
lemma `mk_const` / 引理 `mk_const`

English:
lemma mk_const
  given: {x : Rat}
  statement: mk (const abs x) = x
  proof: rfl

中文:
引理 mk_const
  条件: {x : 有理数}
  结论: mk (const abs x) = x
  证明: rfl
-/
lemma mk_const {x : Rat} : mk (const abs x) = x := rfl

set_option backward.privateInPublic true in
private irreducible_def le (x y : Real) : Prop :=
  x < y ∨ x = y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE Real
  body: ⟨le⟩

中文:
实例 :
  签名: LE 实数
  定义体: ⟨le⟩
-/
instance : LE Real :=
  ⟨le⟩

/--
theorem `le_def'` / 定理 `le_def'`

English:
theorem le_def'
  given: {x y : Real}
  statement: x <= y ↔ x < y ∨ x = y
  proof: iff_of_eq le_def _ _

@[simp]

中文:
定理 le_def'
  条件: {x y : 实数}
  结论: x <= y ↔ x < y ∨ x = y
  证明: iff_of_eq le_def _ _

@[simp]
-/
private theorem le_def' {x y : Real} : x <= y ↔ x < y ∨ x = y :=
iff_of_eq le_def _ _

@[simp]
/--
theorem `mk_le` / 定理 `mk_le`

English:
theorem mk_le
  given: {f g : CauSeq Rat abs}
  statement: mk f <= mk g ↔ f <= g
  proof: by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]

中文:
定理 mk_le
  条件: {f g : CauSeq 有理数 abs}
  结论: mk f <= mk g ↔ f <= g
  证明: by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]

Depends on / 依赖: le_def, mk_eq, mk_lt
-/
theorem mk_le {f g : CauSeq Rat abs} : mk f <= mk g ↔ f <= g := by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]
/--
theorem `ind_mk` / 定理 `ind_mk`

English:
theorem ind_mk
  given: {C : Real -> Prop} (x : Real) (h : forall y, C (mk y))
  statement: C x
  proof: by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _

中文:
定理 ind_mk
  条件: {C : 实数 -> 命题} (x : 实数) (h : 对任意 y, C (mk y))
  结论: C x
  证明: by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _
-/
protected theorem ind_mk {C : Real -> Prop} (x : Real) (h : forall y, C (mk y)) : C x := by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder Real where
  body: by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm

中文:
实例 partialOrder
  签名: : 偏序 实数 where
  定义体: by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm

Depends on / 依赖: CauSeq, CauSeq.le_antisymm, Real.ind_mk, ind_mk, le_antisymm, le_refl, le_trans, lt_iff_le_not_ge, mk_eq, mk_le
-/
instance partialOrder : PartialOrder Real where
  lt_iff_le_not_ge a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder Real
  body: by infer_instance

中文:
实例 :
  签名: 预序 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Preorder Real := by infer_instance

/--
theorem `ratCast_lt` / 定理 `ratCast_lt`

English:
theorem ratCast_lt
  given: {x y : Rat}
  statement: (x : Real) < (y : Real) ↔ x < y
  proof: by
  rw [← mk_const]; rw [← mk_const]; rw [mk_lt]
  exact const_lt

中文:
定理 ratCast_lt
  条件: {x y : 有理数}
  结论: (x : 实数) < (y : 实数) ↔ x < y
  证明: by
  rw [← mk_const]; rw [← mk_const]; rw [mk_lt]
  exact const_lt

Depends on / 依赖: const_lt, mk_const, mk_lt
-/
theorem ratCast_lt {x y : Rat} : (x : Real) < (y : Real) ↔ x < y := by
  rw [← mk_const]; rw [← mk_const]; rw [mk_lt]
  exact const_lt

/--
theorem `zero_lt_one` / 定理 `zero_lt_one`

English:
theorem zero_lt_one
  statement: (0 : Real) < 1
  proof: by
  convert! ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]

中文:
定理 zero_lt_one
  结论: (0 : 实数) < 1
  证明: by
  convert! ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]
-/
protected theorem zero_lt_one : (0 : Real) < 1 := by
  convert! ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: : Nontrivial Real where
  body: ⟨0, 1, Real.zero_lt_one.ne⟩

中文:
实例 instNontrivial
  签名: : 非平凡 实数 where
  定义体: ⟨0, 1, Real.zero_lt_one.ne⟩

Depends on / 依赖: Real.zero_lt_one.ne, zero_lt_one
-/
instance instNontrivial : Nontrivial Real where
  exists_pair_ne := ⟨0, 1, Real.zero_lt_one.ne⟩

/--
Instance `instZeroLEOneClass` / 实例 `instZeroLEOneClass`

English:
instance instZeroLEOneClass
  signature: : ZeroLEOneClass Real where
  body: le_of_lt Real.zero_lt_one

中文:
实例 instZeroLEOneClass
  签名: : ZeroLEOne类 实数 where
  定义体: le_of_lt Real.zero_lt_one

Depends on / 依赖: Real.zero_lt_one, le_of_lt, zero_lt_one
-/
instance instZeroLEOneClass : ZeroLEOneClass Real where
  zero_le_one := le_of_lt Real.zero_lt_one

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid Real where
  body: by
    simp only [le_iff_eq_or_lt]
    rintro a b ⟨rfl, h⟩
    · simp only [lt_self_iff_false, or_false, forall_const]
    · refine fun c => Or.inr ?_
      induction a using Real.ind_mk with | _ a =>
      induction b using Real.ind_mk with | _ b =>
      induction c using Real.ind_mk with | _ c =>
      simp only [mk_lt, ← mk_add] at *
      change Pos _ at *
      rwa [add_sub_add_right_eq_sub]

中文:
实例 instIsOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 实数 where
  定义体: by
    simp only [le_iff_eq_or_lt]
    rintro a b ⟨rfl, h⟩
    · simp only [lt_self_iff_false, or_false, forall_const]
    · refine fun c => Or.inr ?_
      induction a using Real.ind_mk with | _ a =>
      induction b using Real.ind_mk with | _ b =>
      induction c using Real.ind_mk with | _ c =>
      simp only [mk_lt, ← mk_add] at *
      change Pos _ at *
      rwa [add_sub_add_right_eq_sub]

Depends on / 依赖: Or.inr, Real.ind_mk, add_sub_add_right_eq_sub, forall_const, ind_mk, le_iff_eq_or_lt, lt_self_iff_false, mk_add, mk_lt, or_false
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid Real where
  add_le_add_left := by
    simp only [le_iff_eq_or_lt]
    rintro a b ⟨rfl, h⟩
    · simp only [lt_self_iff_false, or_false, forall_const]
    · refine fun c => Or.inr ?_
      induction a using Real.ind_mk with | _ a =>
      induction b using Real.ind_mk with | _ b =>
      induction c using Real.ind_mk with | _ c =>
      simp only [mk_lt, ← mk_add] at *
      change Pos _ at *
      rwa [add_sub_add_right_eq_sub]

/--
Instance `instIsStrictOrderedRing` / 实例 `instIsStrictOrderedRing`

English:
instance instIsStrictOrderedRing
  signature: : IsStrictOrderedRing Real
  body: .of_mul_pos fun a b => by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos

中文:
实例 instIsStrictOrderedRing
  签名: : 是StrictOrdered环 实数
  定义体: .of_mul_pos fun a b => by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos

Depends on / 依赖: CauSeq, CauSeq.mul_pos, Real.ind_mk, ind_mk, mk_lt, mk_mul, mk_pos, mul_pos, of_mul_pos
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing Real :=
  .of_mul_pos fun a b => by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos

/--
Instance `instIsOrderedRing` / 实例 `instIsOrderedRing`

English:
instance instIsOrderedRing
  signature: : IsOrderedRing Real
  body: inferInstance

中文:
实例 instIsOrderedRing
  签名: : 是Ordered环 实数
  定义体: inferInstance
-/
instance instIsOrderedRing : IsOrderedRing Real :=
  inferInstance

/--
Instance `instIsOrderedCancelAddMonoid` / 实例 `instIsOrderedCancelAddMonoid`

English:
instance instIsOrderedCancelAddMonoid
  signature: : IsOrderedCancelAddMonoid Real
  body: inferInstance

中文:
实例 instIsOrderedCancelAddMonoid
  签名: : 是OrderedCancelAdd幺半群 实数
  定义体: inferInstance
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid Real :=
  inferInstance

set_option backward.privateInPublic true in
private irreducible_def sup : Real -> Real -> Real
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy => sup_equiv_sup hx hy) x y⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max Real
  body: ⟨sup⟩

中文:
实例 :
  签名: 最大值 实数
  定义体: ⟨sup⟩
-/
instance : Max Real :=
  ⟨sup⟩

/--
theorem `ofCauchy_sup` / 定理 `ofCauchy_sup`

English:
theorem ofCauchy_sup
  given: (a b)
  statement: (⟨⟦a ⊔ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩
  proof: show _ = sup _ _ by
    rw [sup_def]
    rfl

@[simp]

中文:
定理 ofCauchy_sup
  条件: (a b)
  结论: (⟨⟦a ⊔ b⟧⟩ : 实数) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩
  证明: show _ = sup _ _ by
    rw [sup_def]
    rfl

@[simp]

Depends on / 依赖: sup_def
-/
theorem ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup_def]
    rfl

@[simp]
/--
theorem `mk_sup` / 定理 `mk_sup`

English:
theorem mk_sup
  given: (a b)
  statement: (mk (a ⊔ b) : Real) = mk a ⊔ mk b
  proof: ofCauchy_sup _ _

中文:
定理 mk_sup
  条件: (a b)
  结论: (mk (a ⊔ b) : 实数) = mk a ⊔ mk b
  证明: ofCauchy_sup _ _

Depends on / 依赖: ofCauchy_sup
-/
theorem mk_sup (a b) : (mk (a ⊔ b) : Real) = mk a ⊔ mk b :=
  ofCauchy_sup _ _

set_option backward.privateInPublic true in
private irreducible_def inf : Real -> Real -> Real
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy => inf_equiv_inf hx hy) x y⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min Real
  body: ⟨inf⟩

中文:
实例 :
  签名: 最小值 实数
  定义体: ⟨inf⟩
-/
instance : Min Real :=
  ⟨inf⟩

/--
theorem `ofCauchy_inf` / 定理 `ofCauchy_inf`

English:
theorem ofCauchy_inf
  given: (a b)
  statement: (⟨⟦a ⊓ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩
  proof: show _ = inf _ _ by
    rw [inf_def]
    rfl

@[simp]

中文:
定理 ofCauchy_inf
  条件: (a b)
  结论: (⟨⟦a ⊓ b⟧⟩ : 实数) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩
  证明: show _ = inf _ _ by
    rw [inf_def]
    rfl

@[simp]

Depends on / 依赖: inf_def
-/
theorem ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : Real) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf_def]
    rfl

@[simp]
/--
theorem `mk_inf` / 定理 `mk_inf`

English:
theorem mk_inf
  given: (a b)
  statement: (mk (a ⊓ b) : Real) = mk a ⊓ mk b
  proof: ofCauchy_inf _ _

中文:
定理 mk_inf
  条件: (a b)
  结论: (mk (a ⊓ b) : 实数) = mk a ⊓ mk b
  证明: ofCauchy_inf _ _

Depends on / 依赖: ofCauchy_inf
-/
theorem mk_inf (a b) : (mk (a ⊓ b) : Real) = mk a ⊓ mk b :=
  ofCauchy_inf _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice Real
  body: (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm

中文:
实例 :
  签名: Distrib格 实数
  定义体: (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm
-/
instance : DistribLattice Real where
  sup := (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_sup]; rw [mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    rw [← mk_inf]; rw [mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm

-- Extra instances to short-circuit type class resolution
/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice Real
  body: inferInstance

中文:
实例 lattice
  签名: : 格 实数
  定义体: inferInstance
-/
instance lattice : Lattice Real :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf Real
  body: inferInstance

中文:
实例 :
  签名: SemilatticeInf 实数
  定义体: inferInstance
-/
instance : SemilatticeInf Real :=
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup Real
  body: inferInstance

中文:
实例 :
  签名: SemilatticeSup 实数
  定义体: inferInstance
-/
instance : SemilatticeSup Real :=
  inferInstance

/--
Instance `leTotal_R` / 实例 `leTotal_R`

English:
instance leTotal_R
  signature: : @Std.Total Real (· <= ·)
  body: ⟨by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using CauSeq.le_total ..⟩

中文:
实例 leTotal_R
  签名: : @Std.全 实数 (· <= ·)
  定义体: ⟨by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using CauSeq.le_total ..⟩

Depends on / 依赖: CauSeq, CauSeq.le_total, Real.ind_mk, ind_mk, le_total
-/
instance leTotal_R : @Std.Total Real (· <= ·) :=
  ⟨by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using CauSeq.le_total ..⟩

open scoped Classical in
/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder Real
  body: Lattice.toLinearOrder Real

中文:
实例 linearOrder
  签名: : 线性序 实数
  定义体: Lattice.toLinearOrder Real

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
noncomputable instance linearOrder : LinearOrder Real :=
  Lattice.toLinearOrder Real

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain Real
  body: IsStrictOrderedRing.isDomain

中文:
实例 :
  签名: 是整环 实数
  定义体: IsStrictOrderedRing.isDomain

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.isDomain, isDomain
-/
instance : IsDomain Real := IsStrictOrderedRing.isDomain

/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: : DivInvMonoid Real where

中文:
实例 instDivInvMonoid
  签名: : 除逆幺半群 实数 where
-/
noncomputable instance instDivInvMonoid : DivInvMonoid Real where

/--
lemma `ofCauchy_div` / 引理 `ofCauchy_div`

English:
lemma ofCauchy_div
  given: (f g)
  statement: (⟨f / g⟩ : Real) = (⟨f⟩ : Real) / (⟨g⟩ : Real)
  proof: by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

中文:
引理 ofCauchy_div
  条件: (f g)
  结论: (⟨f / g⟩ : 实数) = (⟨f⟩ : 实数) / (⟨g⟩ : 实数)
  证明: by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

Depends on / 依赖: div_eq_mul_inv, ofCauchy_inv, ofCauchy_mul, simp_rw
-/
lemma ofCauchy_div (f g) : (⟨f / g⟩ : Real) = (⟨f⟩ : Real) / (⟨g⟩ : Real) := by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field Real where
  body: by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast]; rw [NNRat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast]; rw [Rat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_intCast]

中文:
实例 instField
  签名: : 域 实数 where
  定义体: by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast]; rw [NNRat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast]; rw [Rat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_intCast]

Depends on / 依赖: CauSeq, CauSeq.Completion.inv_mul_cancel, Completion, NNRat.cast_def, Rat.cast_, cast_, cast_def, inv_mul_cancel, inv_zero, mul_comm, nnqsmul, nnqsmul_def, nnratCast_def, ofCauchy, ofCauchy.injEq, ofCauchy_div, ofCauchy_inv, ofCauchy_mul, ofCauchy_natCast, ofCauchy_nnratCast
-/
noncomputable instance instField : Field Real where
  mul_inv_cancel := by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast]; rw [NNRat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast]; rw [Rat.cast_def]; rw [ofCauchy_div]; rw [ofCauchy_natCast]; rw [ofCauchy_intCast]

-- Extra instances to short-circuit type class resolution
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivisionRing Real
  body: by infer_instance

中文:
实例 :
  签名: 除环 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance : DivisionRing Real := by infer_instance

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: (a b : Real)
  body: by infer_instance

中文:
实例 decidableLT
  签名: (a b : 实数)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance decidableLT (a b : Real) : Decidable (a < b) := by infer_instance

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: (a b : Real)
  body: by infer_instance

中文:
实例 decidableLE
  签名: (a b : 实数)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance decidableLE (a b : Real) : Decidable (a <= b) := by infer_instance

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: (a b : Real)
  body: by infer_instance

中文:
实例 decidableEq
  签名: (a b : 实数)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance decidableEq (a b : Real) : Decidable (a = b) := by infer_instance

/-- Show an underlying Cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr Real where
  reprPrec r p := Repr.addAppParen ("Real.ofCauchy " ++ repr r.cauchy) p

/--
theorem `le_mk_of_forall_le` / 定理 `le_mk_of_forall_le`

English:
theorem le_mk_of_forall_le
  given: {f : CauSeq Rat abs}
  statement: (exists i, forall j >= i, x <= f j) -> x <= mk f
  proof: by
  intro h
  induction x using Real.ind_mk
  apply le_of_not_gt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_ge (H _ le_rfl).1
  rw [← mk_const]; rw [mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this

中文:
定理 le_mk_of_对任意_le
  条件: {f : CauSeq 有理数 abs}
  结论: (存在 i, 对任意 j >= i, x <= f j) -> x <= mk f
  证明: by
  intro h
  induction x using Real.ind_mk
  apply le_of_not_gt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_ge (H _ le_rfl).1
  rw [← mk_const]; rw [mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this

Depends on / 依赖: Real.ind_mk, abs_lt, add_le_add, exists_forall_ge_and, f.cauchy, half_pos, ind_mk, le_of_lt, le_of_not_gt, le_rfl, mk_const, mk_lt, not_lt_of_ge, sub_add_sub_cancel, sub_apply, sub_eq_add_neg, sub_self_div_two
-/
theorem le_mk_of_forall_le {f : CauSeq Rat abs} : (exists i, forall j >= i, x <= f j) -> x <= mk f := by
  intro h
  induction x using Real.ind_mk
  apply le_of_not_gt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_ge (H _ le_rfl).1
  rw [← mk_const]; rw [mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this

/--
theorem `mk_le_of_forall_le` / 定理 `mk_le_of_forall_le`

English:
theorem mk_le_of_forall_le
  given: {f : CauSeq Rat abs} {x : Real} (h : exists i, forall j >= i, (f j : Real) <= x)
  proof: by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff]; rw [← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩

中文:
定理 mk_le_of_对任意_le
  条件: {f : CauSeq 有理数 abs} {x : 实数} (h : 存在 i, 对任意 j >= i, (f j : 实数) <= x)
  证明: by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff]; rw [← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩

Depends on / 依赖: le_mk_of_forall_le, mk_neg, neg_le_neg_iff
-/
theorem mk_le_of_forall_le {f : CauSeq Rat abs} {x : Real} (h : exists i, forall j >= i, (f j : Real) <= x) :
    mk f <= x := by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff]; rw [← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩

/--
theorem `mk_near_of_forall_near` / 定理 `mk_near_of_forall_near`

English:
theorem mk_near_of_forall_near
  statement: {f : CauSeq Rat abs} {x : Real} {ε : Real}
  proof: abs_sub_le_iff.2
⟨sub_le_iff_le_add'.2
mk_le_of_forall_le
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
sub_le_comm.1
le_mk_of_forall_le H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩

中文:
定理 mk_near_of_对任意_near
  结论: {f : CauSeq 有理数 abs} {x : 实数} {ε : 实数}
  证明: abs_sub_le_iff.2
⟨sub_le_iff_le_add'.2
mk_le_of_forall_le
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
sub_le_comm.1
le_mk_of_forall_le H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩

Depends on / 依赖: H.imp, abs_sub_le_iff, le_mk_of_forall_le, mk_le_of_forall_le, sub_le_comm, sub_le_iff_le_add
-/
theorem mk_near_of_forall_near {f : CauSeq Rat abs} {x : Real} {ε : Real}
    (H : exists i, forall j >= i, |(f j : Real) - x| <= ε) : |mk f - x| <= ε :=
  abs_sub_le_iff.2
⟨sub_le_iff_le_add'.2
mk_le_of_forall_le
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
sub_le_comm.1
le_mk_of_forall_le H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩

/--
lemma `mul_add_one_le_add_one_pow` / 引理 `mul_add_one_le_add_one_pow`

English:
lemma mul_add_one_le_add_one_pow
  given: {a : Real} (ha : 0 <= a) (b : Nat)
  statement: a * b + 1 <= (a + 1) ^ b
  proof: by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  clear ha
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    calc
      a * ↑(b + 1) + 1 = (0 + 1) ^ b * a + (a * b + 1) := by
        simp [mul_add, add_assoc, add_left_comm]
      _ <= (a + 1) ^ b * a + (a + 1) ^ b := by
        gcongr
        · norm_num
        · exact hb ha'
      _ = (a + 1) ^ (b + 1) := by simp [pow_succ, mul_add]

中文:
引理 mul_add_one_le_add_one_pow
  条件: {a : 实数} (ha : 0 <= a) (b : 自然数)
  结论: a * b + 1 <= (a + 1) ^ b
  证明: by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  clear ha
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    calc
      a * ↑(b + 1) + 1 = (0 + 1) ^ b * a + (a * b + 1) := by
        simp [mul_add, add_assoc, add_left_comm]
      _ <= (a + 1) ^ b * a + (a + 1) ^ b := by
        gcongr
        · norm_num
        · exact hb ha'
      _ = (a + 1) ^ (b + 1) := by simp [pow_succ, mul_add]

Depends on / 依赖: add_assoc, add_left_comm, eq_or_lt, generalizing, ha.eq_or_lt, mul_add, pow_succ
-/
lemma mul_add_one_le_add_one_pow {a : Real} (ha : 0 <= a) (b : Nat) : a * b + 1 <= (a + 1) ^ b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  clear ha
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    calc
      a * ↑(b + 1) + 1 = (0 + 1) ^ b * a + (a * b + 1) := by
        simp [mul_add, add_assoc, add_left_comm]
      _ <= (a + 1) ^ b * a + (a + 1) ^ b := by
        gcongr
        · norm_num
        · exact hb ha'
      _ = (a + 1) ^ (b + 1) := by simp [pow_succ, mul_add]

end Real

/--
Definition of `IsPowMul` / `IsPowMul` 的定义

English:
definition IsPowMul
  signature: {R : Type*} [Pow R Nat] (f : R -> Real)
  body: forall (a : R) {n : Nat}, 1 <= n -> f (a ^ n) = f a ^ n

中文:
定义 IsPowMul
  签名: {R : 类型} [幂 R 自然数] (f : R -> 实数)
  定义体: forall (a : R) {n : Nat}, 1 <= n -> f (a ^ n) = f a ^ n
-/
def IsPowMul {R : Type*} [Pow R Nat] (f : R -> Real) :=
  forall (a : R) {n : Nat}, 1 <= n -> f (a ^ n) = f a ^ n

/--
lemma `IsPowMul.map_one_le_one` / 引理 `IsPowMul.map_one_le_one`

English:
lemma IsPowMul.map_one_le_one
  given: {R : Type*} [Monoid R] {f : R -> Real} (hf : IsPowMul f)
  proof: by
  have hf1 : (f 1) ^ 2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

中文:
引理 IsPowMul.map_one_le_one
  条件: {R : 类型} [幺半群 R] {f : R -> 实数} (hf : IsPowMul f)
  证明: by
  have hf1 : (f 1) ^ 2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

Depends on / 依赖: conv_rhs, eq_zero_or_one_of_sq_eq_self, one_le_two, one_pow, zero_le_one
-/
lemma IsPowMul.map_one_le_one {R : Type*} [Monoid R] {f : R -> Real} (hf : IsPowMul f) :
    f 1 <= 1 := by
  have hf1 : (f 1) ^ 2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

/--
Definition of `RingHom.IsBoundedWrt` / `RingHom.IsBoundedWrt` 的定义

English:
definition RingHom.IsBoundedWrt
  signature: {α : Type*} [Ring α] {β : Type*} [Ring β] (nα : α -> Real) (nβ : β -> Real)
  body: exists C : Real, 0 < C ∧ forall x : α, nβ (f x) <= C * nα x

中文:
定义 环态射.IsBoundedWrt
  签名: {α : 类型} [环 α] {β : 类型} [环 β] (nα : α -> 实数) (nβ : β -> 实数)
  定义体: exists C : Real, 0 < C ∧ forall x : α, nβ (f x) <= C * nα x
-/
def RingHom.IsBoundedWrt {α : Type*} [Ring α] {β : Type*} [Ring β] (nα : α -> Real) (nβ : β -> Real)
    (f : α ->+* β) : Prop :=
  exists C : Real, 0 < C ∧ forall x : α, nβ (f x) <= C * nα x
