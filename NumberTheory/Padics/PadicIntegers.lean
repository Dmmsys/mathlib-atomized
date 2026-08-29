/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

@[expose] public section


open Padic Metric IsLocalRing

noncomputable section

variable (p : Nat) [hp : Fact p.Prime]

/--
Definition of `PadicInt` / `PadicInt` 的定义

English:
definition PadicInt
  signature: : Type
  body: {x : Rat_[p] // ‖x‖ <= 1}

中文:
定义 Padic整数
  签名: : 类型
  定义体: {x : Rat_[p] // ‖x‖ <= 1}

Depends on / 依赖: Rat_
-/
def PadicInt : Type := {x : Rat_[p] // ‖x‖ <= 1}

/-- The ring of `p`-adic integers. -/
notation "Int_[" p "]" => PadicInt p

namespace PadicInt
variable {p} {x y : Int_[p]}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Int_[p] Rat_[p]
  body: ⟨Subtype.val⟩

中文:
实例 :
  签名: Coe 整数_[p] Rat_[p]
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance : Coe Int_[p] Rat_[p] :=
  ⟨Subtype.val⟩

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : Int_[p]}
  statement: (x : Rat_[p]) = y -> x = y
  proof: Subtype.ext

中文:
定理 ext
  条件: {x y : 整数_[p]}
  结论: (x : Rat_[p]) = y -> x = y
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem ext {x y : Int_[p]} : (x : Rat_[p]) = y -> x = y :=
  Subtype.ext

variable (p)

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: : Subring Rat_[p] where
  body: { x : Rat_[p] | ‖x‖ <= 1 }
  zero_mem' := by simp
  one_mem' := by simp
add_mem' hx hy := (Padic.nonarchimedean _ _).trans max_le_iff.2 ⟨hx, hy⟩
mul_mem' hx hy := (padicNormE.mul _ _).trans_le mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]

中文:
定义 subring
  签名: : 子环 Rat_[p] where
  定义体: { x : Rat_[p] | ‖x‖ <= 1 }
  zero_mem' := by simp
  one_mem' := by simp
add_mem' hx hy := (Padic.nonarchimedean _ _).trans max_le_iff.2 ⟨hx, hy⟩
mul_mem' hx hy := (padicNormE.mul _ _).trans_le mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]

Depends on / 依赖: Rat_
-/
def subring : Subring Rat_[p] where
  carrier := { x : Rat_[p] | ‖x‖ <= 1 }
  zero_mem' := by simp
  one_mem' := by simp
add_mem' hx hy := (Padic.nonarchimedean _ _).trans max_le_iff.2 ⟨hx, hy⟩
mul_mem' hx hy := (padicNormE.mul _ _).trans_le mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]
/--
theorem `mem_subring_iff` / 定理 `mem_subring_iff`

English:
theorem mem_subring_iff
  given: {x : Rat_[p]}
  statement: x in subring p ↔ ‖x‖ <= 1
  proof: Iff.rfl

中文:
定理 mem_subring_iff
  条件: {x : Rat_[p]}
  结论: x in subring p ↔ ‖x‖ <= 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_subring_iff {x : Rat_[p]} : x in subring p ↔ ‖x‖ <= 1 := Iff.rfl

variable {p}

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: : CommRing Int_[p]
  body: inferInstanceAs CommRing (subring p)

中文:
实例 instCommRing
  签名: : 交换环 整数_[p]
  定义体: inferInstanceAs CommRing (subring p)

Depends on / 依赖: CommRing, subring
-/
instance instCommRing : CommRing Int_[p] := inferInstanceAs CommRing (subring p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Int_[p]
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 整数_[p]
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited Int_[p] := ⟨0⟩

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: {h}
  statement: (⟨0, h⟩ : Int_[p]) = (0 : Int_[p])
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_zero
  条件: {h}
  结论: (⟨0, h⟩ : 整数_[p]) = (0 : 整数_[p])
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_zero {h} : (⟨0, h⟩ : Int_[p]) = (0 : Int_[p]) := rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (z1 z2 : Int_[p])
  statement: ((z1 + z2 : Int_[p]) : Rat_[p]) = z1 + z2
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (z1 z2 : 整数_[p])
  结论: ((z1 + z2 : 整数_[p]) : Rat_[p]) = z1 + z2
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (z1 z2 : Int_[p]) : ((z1 + z2 : Int_[p]) : Rat_[p]) = z1 + z2 := rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (z1 z2 : Int_[p])
  statement: ((z1 * z2 : Int_[p]) : Rat_[p]) = z1 * z2
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (z1 z2 : 整数_[p])
  结论: ((z1 * z2 : 整数_[p]) : Rat_[p]) = z1 * z2
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (z1 z2 : Int_[p]) : ((z1 * z2 : Int_[p]) : Rat_[p]) = z1 * z2 := rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (z1 : Int_[p])
  statement: ((-z1 : Int_[p]) : Rat_[p]) = -z1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (z1 : 整数_[p])
  结论: ((-z1 : 整数_[p]) : Rat_[p]) = -z1
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (z1 : Int_[p]) : ((-z1 : Int_[p]) : Rat_[p]) = -z1 := rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (z1 z2 : Int_[p])
  statement: ((z1 - z2 : Int_[p]) : Rat_[p]) = z1 - z2
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  条件: (z1 z2 : 整数_[p])
  结论: ((z1 - z2 : 整数_[p]) : Rat_[p]) = z1 - z2
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub (z1 z2 : Int_[p]) : ((z1 - z2 : Int_[p]) : Rat_[p]) = z1 - z2 := rfl

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : Int_[p]) : Rat_[p]) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ((1 : 整数_[p]) : Rat_[p]) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ((1 : Int_[p]) : Rat_[p]) = 1 := rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : Int_[p]) : Rat_[p]) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: ((0 : 整数_[p]) : Rat_[p]) = 0
  证明: rfl
-/
theorem coe_zero : ((0 : Int_[p]) : Rat_[p]) = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coe_eq_zero` / 引理 `coe_eq_zero`

English:
lemma coe_eq_zero
  statement: (x : Rat_[p]) = 0 ↔ x = 0
  proof: by rw [← coe_zero, Subtype.coe_inj]

中文:
引理 coe_eq_zero
  结论: (x : Rat_[p]) = 0 ↔ x = 0
  证明: by rw [← coe_zero, Subtype.coe_inj]
-/
@[simp] lemma coe_eq_zero : (x : Rat_[p]) = 0 ↔ x = 0 := by rw [← coe_zero, Subtype.coe_inj]

/--
lemma `coe_ne_zero` / 引理 `coe_ne_zero`

English:
lemma coe_ne_zero
  statement: (x : Rat_[p]) != 0 ↔ x != 0
  proof: coe_eq_zero.not

@[simp, norm_cast]

中文:
引理 coe_ne_zero
  结论: (x : Rat_[p]) != 0 ↔ x != 0
  证明: coe_eq_zero.not

@[simp, norm_cast]

Depends on / 依赖: coe_eq_zero, coe_eq_zero.not
-/
lemma coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0 := coe_eq_zero.not

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : Int_[p]) : Rat_[p]) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : 整数_[p]) : Rat_[p]) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_natCast (n : Nat) : ((n : Int_[p]) : Rat_[p]) = n := rfl

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (z : Int)
  statement: ((z : Int_[p]) : Rat_[p]) = z
  proof: rfl

中文:
定理 coe_intCast
  条件: (z : 整数)
  结论: ((z : 整数_[p]) : Rat_[p]) = z
  证明: rfl
-/
theorem coe_intCast (z : Int) : ((z : Int_[p]) : Rat_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
@[simps!]
/--
Definition of `Coe.ringHom` / `Coe.ringHom` 的定义

English:
definition Coe.ringHom
  signature: : Int_[p] ->+* Rat_[p]
  body: (subring p).subtype

@[simp, norm_cast]

中文:
定义 Coe.ringHom
  签名: : 整数_[p] ->+* Rat_[p]
  定义体: (subring p).subtype

@[simp, norm_cast]

Depends on / 依赖: subring, subtype
-/
def Coe.ringHom : Int_[p] ->+* Rat_[p] := (subring p).subtype

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : Int_[p]) (n : Nat)
  statement: (↑(x ^ n) : Rat_[p]) = (↑x : Rat_[p]) ^ n
  proof: rfl

中文:
定理 coe_pow
  条件: (x : 整数_[p]) (n : 自然数)
  结论: (↑(x ^ n) : Rat_[p]) = (↑x : Rat_[p]) ^ n
  证明: rfl
-/
theorem coe_pow (x : Int_[p]) (n : Nat) : (↑(x ^ n) : Rat_[p]) = (↑x : Rat_[p]) ^ n := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (k : Int_[p])
  statement: (⟨k, k.2⟩ : Int_[p]) = k
  proof: by simp

中文:
定理 mk_coe
  条件: (k : 整数_[p])
  结论: (⟨k, k.2⟩ : 整数_[p]) = k
  证明: by simp
-/
theorem mk_coe (k : Int_[p]) : (⟨k, k.2⟩ : Int_[p]) = k := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  given: {α : Type*} (s : Finset α) (f : α -> Int_[p])
  proof: by
  simp [← Coe.ringHom_apply, map_sum PadicInt.Coe.ringHom f s]

中文:
引理 coe_sum
  条件: {α : 类型} (s : 有限集 α) (f : α -> 整数_[p])
  证明: by
  simp [← Coe.ringHom_apply, map_sum PadicInt.Coe.ringHom f s]

Depends on / 依赖: Coe.ringHom_apply, PadicInt, PadicInt.Coe.ringHom, map_sum, ringHom, ringHom_apply
-/
lemma coe_sum {α : Type*} (s : Finset α) (f : α -> Int_[p]) :
    (((∑ z in s, f z) : Int_[p]) : Rat_[p]) = ∑ z in s, (f z : Rat_[p]) := by
  simp [← Coe.ringHom_apply, map_sum PadicInt.Coe.ringHom f s]

open Topology in
/--
lemma `isOpenEmbedding_coe` / 引理 `isOpenEmbedding_coe`

English:
lemma isOpenEmbedding_coe
  statement: IsOpenEmbedding ((↑) : Int_[p] -> Rat_[p])
  proof: by
  refine (?_ : IsOpen {y : Rat_[p] | ‖y‖ <= 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : Rat_[p]) one_ne_zero

中文:
引理 isOpenEmbedding_coe
  结论: 是开嵌入 ((↑) : 整数_[p] -> Rat_[p])
  证明: by
  refine (?_ : IsOpen {y : Rat_[p] | ‖y‖ <= 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : Rat_[p]) one_ne_zero

Depends on / 依赖: IsOpen, IsUltrametricDist, IsUltrametricDist.isOpen_closedBall, Metric, Metric.closedBall, Rat_, closedBall, dist_eq_norm_sub, isOpenEmbedding_subtypeVal, isOpen_closedBall, one_ne_zero, sub_zero
-/
lemma isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Int_[p] -> Rat_[p]) := by
  refine (?_ : IsOpen {y : Rat_[p] | ‖y‖ <= 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : Rat_[p]) one_ne_zero

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: : Int_[p] -> Int_[p]

中文:
定义 inv
  签名: : 整数_[p] -> 整数_[p]
-/
def inv : Int_[p] -> Int_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero Int_[p]
  body: Nat.cast_injective (R := Rat_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]

中文:
实例 :
  签名: 特征零 整数_[p]
  定义体: Nat.cast_injective (R := Rat_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]

Depends on / 依赖: Nat.cast_injective, Rat_, Subtype, Subtype.ext_iff, cast_injective, ext_iff
-/
instance : CharZero Int_[p] where
  cast_injective m n h :=
    Nat.cast_injective (R := Rat_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]
/--
theorem `intCast_eq` / 定理 `intCast_eq`

English:
theorem intCast_eq
  given: (z1 z2 : Int)
  statement: (z1 : Int_[p]) = z2 ↔ z1 = z2
  proof: by simp

中文:
定理 intCast_eq
  条件: (z1 z2 : 整数)
  结论: (z1 : 整数_[p]) = z2 ↔ z1 = z2
  证明: by simp
-/
theorem intCast_eq (z1 z2 : Int) : (z1 : Int_[p]) = z2 ↔ z1 = z2 := by simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofIntSeq` / `ofIntSeq` 的定义

English:
definition ofIntSeq
  signature: (seq : Nat -> Int) (h : IsCauSeq (padicNorm p) fun n => seq n)
  body: ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) <= (1 : Real) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

中文:
定义 of整数Seq
  签名: (seq : 自然数 -> 整数) (h : IsCauSeq (padicNorm p) fun n => seq n)
  定义体: ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) <= (1 : Real) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

Depends on / 依赖: PadicSeq, PadicSeq.norm, of_int, padicNorm, padicNorm.of_int, split_ifs
-/
def ofIntSeq (seq : Nat -> Int) (h : IsCauSeq (padicNorm p) fun n => seq n) : Int_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) <= (1 : Real) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variable (p)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Int_[p]
  body: inferInstanceAs MetricSpace (Subtype _)

中文:
实例 :
  签名: 度量空间 整数_[p]
  定义体: inferInstanceAs MetricSpace (Subtype _)

Depends on / 依赖: IsGaussian, IsGaussian.charFunDual_eq, MetricSpace, Subtype, charFunDual_eq, charFunDual_map_add_const, exp_add, fun_prop, hL_comp, integral, integral_add, integral_complex_ofReal, integral_map, isGaussian_of_charFunDual_eq, map_add, variance_add_const, variance_map
-/
instance : MetricSpace Int_[p] := inferInstanceAs MetricSpace (Subtype _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUltrametricDist Int_[p]
  body: IsUltrametricDist.subtype _

中文:
实例 :
  签名: 是UltrametricDist 整数_[p]
  定义体: IsUltrametricDist.subtype _

Depends on / 依赖: IsUltrametricDist, IsUltrametricDist.subtype, add_comm, infer_instance, simp_rw, subtype
-/
instance : IsUltrametricDist Int_[p] := IsUltrametricDist.subtype _

/--
Instance `completeSpace` / 实例 `completeSpace`

English:
instance completeSpace
  signature: : CompleteSpace Int_[p]
  body: have : IsClosed { x : Rat_[p] | ‖x‖ <= 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe

中文:
实例 completeSpace
  签名: : 完备空间 整数_[p]
  定义体: have : IsClosed { x : Rat_[p] | ‖x‖ <= 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe

Depends on / 依赖: IsClosed, Rat_, completeSpace_coe, continuous_const, continuous_norm, infer_instance, isClosed_le, simp_rw, sub_eq_add_neg, this.completeSpace_coe
-/
instance completeSpace : CompleteSpace Int_[p] :=
  have : IsClosed { x : Rat_[p] | ‖x‖ <= 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm Int_[p]
  body: ⟨fun z => ‖(z : Rat_[p])‖⟩

中文:
实例 :
  签名: 范数 整数_[p]
  定义体: ⟨fun z => ‖(z : Rat_[p])‖⟩

Depends on / 依赖: Rat_
-/
instance : Norm Int_[p] := ⟨fun z => ‖(z : Rat_[p])‖⟩

variable {p} in
/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: {z : Int_[p]}
  statement: ‖z‖ = ‖(z : Rat_[p])‖
  proof: rfl

中文:
定理 norm_def
  条件: {z : 整数_[p]}
  结论: ‖z‖ = ‖(z : Rat_[p])‖
  证明: rfl

Depends on / 依赖: Function, Function.comp_def, IsGaussian, Measure, Measure.map_map, comp_def, fun_prop, infer_instance, map_map, simp_rw, sub_eq_add_neg
-/
theorem norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedCommRing Int_[p]
  body: by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact dist_eq_norm_neg_add x y
  norm_mul_le := by simp [norm_def]

中文:
实例 :
  签名: NormedComm环 整数_[p]
  定义体: by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact dist_eq_norm_neg_add x y
  norm_mul_le := by simp [norm_def]

Depends on / 依赖: dist_eq_norm_neg_add, norm_def, norm_mul_le
-/
instance : NormedCommRing Int_[p] where
  dist_eq := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact dist_eq_norm_neg_add x y
  norm_mul_le := by simp [norm_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormOneClass Int_[p]
  body: ⟨norm_def.trans norm_one⟩

中文:
实例 :
  签名: NormOne类 整数_[p]
  定义体: ⟨norm_def.trans norm_one⟩

Depends on / 依赖: norm_def, norm_def.trans, norm_one
-/
instance : NormOneClass Int_[p] :=
  ⟨norm_def.trans norm_one⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormMulClass Int_[p]
  body: ⟨fun x y => by simp [norm_def]⟩

中文:
实例 :
  签名: NormMul类 整数_[p]
  定义体: ⟨fun x y => by simp [norm_def]⟩

Depends on / 依赖: norm_def
-/
instance : NormMulClass Int_[p] := ⟨fun x y => by simp [norm_def]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain Int_[p]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 :
  签名: 是整环 整数_[p]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance : IsDomain Int_[p] := NoZeroDivisors.to_isDomain _

variable {p}


/--
theorem `norm_le_one` / 定理 `norm_le_one`

English:
theorem norm_le_one
  given: (z : Int_[p])
  statement: ‖z‖ <= 1
  proof: z.2

中文:
定理 norm_le_one
  条件: (z : 整数_[p])
  结论: ‖z‖ <= 1
  证明: z.2
-/
theorem norm_le_one (z : Int_[p]) : ‖z‖ <= 1 := z.2

/--
theorem `nonarchimedean` / 定理 `nonarchimedean`

English:
theorem nonarchimedean
  given: (q r : Int_[p])
  statement: ‖q + r‖ <= max ‖q‖ ‖r‖
  proof: Padic.nonarchimedean _ _

中文:
定理 nonarchimedean
  条件: (q r : 整数_[p])
  结论: ‖q + r‖ <= 最大值 ‖q‖ ‖r‖
  证明: Padic.nonarchimedean _ _

Depends on / 依赖: Padic.nonarchimedean, nonarchimedean
-/
theorem nonarchimedean (q r : Int_[p]) : ‖q + r‖ <= max ‖q‖ ‖r‖ := Padic.nonarchimedean _ _

/--
theorem `norm_add_eq_max_of_ne` / 定理 `norm_add_eq_max_of_ne`

English:
theorem norm_add_eq_max_of_ne
  given: {q r : Int_[p]}
  statement: ‖q‖ != ‖r‖ -> ‖q + r‖ = max ‖q‖ ‖r‖
  proof: Padic.add_eq_max_of_ne

中文:
定理 norm_add_eq_max_of_ne
  条件: {q r : 整数_[p]}
  结论: ‖q‖ != ‖r‖ -> ‖q + r‖ = 最大值 ‖q‖ ‖r‖
  证明: Padic.add_eq_max_of_ne

Depends on / 依赖: Padic.add_eq_max_of_ne, add_eq_max_of_ne
-/
theorem norm_add_eq_max_of_ne {q r : Int_[p]} : ‖q‖ != ‖r‖ -> ‖q + r‖ = max ‖q‖ ‖r‖ :=
  Padic.add_eq_max_of_ne

/--
theorem `norm_eq_of_norm_add_lt_right` / 定理 `norm_eq_of_norm_add_lt_right`

English:
theorem norm_eq_of_norm_add_lt_right
  given: {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z2‖)
  statement: ‖z1‖ = ‖z2‖
  proof: by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h

中文:
定理 norm_eq_of_norm_add_lt_right
  条件: {z1 z2 : 整数_[p]} (h : ‖z1 + z2‖ < ‖z2‖)
  结论: ‖z1‖ = ‖z2‖
  证明: by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h

Depends on / 依赖: le_max_right, norm_add_eq_max_of_ne, not_lt_of_ge
-/
theorem norm_eq_of_norm_add_lt_right {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h

/--
theorem `norm_eq_of_norm_add_lt_left` / 定理 `norm_eq_of_norm_add_lt_left`

English:
theorem norm_eq_of_norm_add_lt_left
  given: {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z1‖)
  statement: ‖z1‖ = ‖z2‖
  proof: by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]

中文:
定理 norm_eq_of_norm_add_lt_left
  条件: {z1 z2 : 整数_[p]} (h : ‖z1 + z2‖ < ‖z1‖)
  结论: ‖z1‖ = ‖z2‖
  证明: by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]

Depends on / 依赖: le_max_left, norm_add_eq_max_of_ne, not_lt_of_ge
-/
theorem norm_eq_of_norm_add_lt_left {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]
/--
theorem `padic_norm_e_of_padicInt` / 定理 `padic_norm_e_of_padicInt`

English:
theorem padic_norm_e_of_padicInt
  given: (z : Int_[p])
  statement: ‖(z : Rat_[p])‖ = ‖z‖
  proof: by simp [norm_def]

中文:
定理 padic_norm_e_of_padic整数
  条件: (z : 整数_[p])
  结论: ‖(z : Rat_[p])‖ = ‖z‖
  证明: by simp [norm_def]

Depends on / 依赖: norm_def
-/
theorem padic_norm_e_of_padicInt (z : Int_[p]) : ‖(z : Rat_[p])‖ = ‖z‖ := by simp [norm_def]

/--
theorem `norm_intCast_eq_padic_norm` / 定理 `norm_intCast_eq_padic_norm`

English:
theorem norm_intCast_eq_padic_norm
  given: (z : Int)
  statement: ‖(z : Int_[p])‖ = ‖(z : Rat_[p])‖
  proof: by simp [norm_def]

@[simp]

中文:
定理 norm_intCast_eq_padic_norm
  条件: (z : 整数)
  结论: ‖(z : 整数_[p])‖ = ‖(z : Rat_[p])‖
  证明: by simp [norm_def]

@[simp]

Depends on / 依赖: norm_def
-/
theorem norm_intCast_eq_padic_norm (z : Int) : ‖(z : Int_[p])‖ = ‖(z : Rat_[p])‖ := by simp [norm_def]

@[simp]
/--
theorem `norm_eq_padic_norm` / 定理 `norm_eq_padic_norm`

English:
theorem norm_eq_padic_norm
  given: {q : Rat_[p]} (hq : ‖q‖ <= 1)
  statement: @norm Int_[p] _ ⟨q, hq⟩ = ‖q‖
  proof: rfl

@[simp]

中文:
定理 norm_eq_padic_norm
  条件: {q : Rat_[p]} (hq : ‖q‖ <= 1)
  结论: @norm 整数_[p] _ ⟨q, hq⟩ = ‖q‖
  证明: rfl

@[simp]
-/
theorem norm_eq_padic_norm {q : Rat_[p]} (hq : ‖q‖ <= 1) : @norm Int_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl

@[simp]
/--
theorem `norm_p` / 定理 `norm_p`

English:
theorem norm_p
  statement: ‖(p : Int_[p])‖ = (p : Real)⁻¹
  proof: Padic.norm_p

中文:
定理 norm_p
  结论: ‖(p : 整数_[p])‖ = (p : 实数)⁻¹
  证明: Padic.norm_p

Depends on / 依赖: Padic.norm_p, norm_p
-/
theorem norm_p : ‖(p : Int_[p])‖ = (p : Real)⁻¹ := Padic.norm_p

/--
theorem `norm_p_pow` / 定理 `norm_p_pow`

English:
theorem norm_p_pow
  given: (n : Nat)
  statement: ‖(p : Int_[p]) ^ n‖ = (p : Real) ^ (-n : Int)
  proof: by simp

@[simp]

中文:
定理 norm_p_pow
  条件: (n : 自然数)
  结论: ‖(p : 整数_[p]) ^ n‖ = (p : 实数) ^ (-n : 整数)
  证明: by simp

@[simp]
-/
theorem norm_p_pow (n : Nat) : ‖(p : Int_[p]) ^ n‖ = (p : Real) ^ (-n : Int) := by simp

@[simp]
/--
lemma `one_le_norm_iff` / 引理 `one_le_norm_iff`

English:
lemma one_le_norm_iff
  given: {x : Int_[p]}
  proof: by
  simp [le_antisymm_iff, ← padic_norm_e_of_padicInt, x.prop]

@[simp]

中文:
引理 one_le_norm_iff
  条件: {x : 整数_[p]}
  证明: by
  simp [le_antisymm_iff, ← padic_norm_e_of_padicInt, x.prop]

@[simp]

Depends on / 依赖: le_antisymm_iff, padic_norm_e_of_padicInt, x.prop
-/
lemma one_le_norm_iff {x : Int_[p]} :
    1 <= ‖x‖ ↔ ‖x‖ = 1 := by
  simp [le_antisymm_iff, ← padic_norm_e_of_padicInt, x.prop]

@[simp]
/--
lemma `norm_natCast_p_sub_one` / 引理 `norm_natCast_p_sub_one`

English:
lemma norm_natCast_p_sub_one
  proof: by
  simp [norm_def]

中文:
引理 norm_natCast_p_sub_one
  证明: by
  simp [norm_def]

Depends on / 依赖: norm_def
-/
lemma norm_natCast_p_sub_one :
    ‖((p - 1 : Nat) : Int_[p])‖ = 1 := by
  simp [norm_def]

/--
Definition of `cauSeq_to_rat_cauSeq` / `cauSeq_to_rat_cauSeq` 的定义

English:
definition cauSeq_to_rat_cauSeq
  signature: (f : CauSeq Int_[p] norm)
  body: ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

中文:
定义 cauSeq_to_rat_cauSeq
  签名: (f : CauSeq 整数_[p] norm)
  定义体: ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩
-/
private def cauSeq_to_rat_cauSeq (f : CauSeq Int_[p] norm) : CauSeq Rat_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)

/--
Instance `complete` / 实例 `complete`

English:
instance complete
  signature: : CauSeq.IsComplete Int_[p] norm
  body: ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ <= 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using! CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩

中文:
实例 complete
  签名: : CauSeq.是完备 整数_[p] norm
  定义体: ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ <= 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using! CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩

Depends on / 依赖: CauSeq, CauSeq.equiv_lim, CauSeq.lim, cauSeq_to_rat_cauSeq, equiv_lim, norm_def, norm_le_one, padicNormE_lim_le, zero_lt_one
-/
instance complete : CauSeq.IsComplete Int_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ <= 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using! CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩

/--
theorem `exists_pow_neg_lt` / 定理 `exists_pow_neg_lt`

English:
theorem exists_pow_neg_lt
  given: {ε : Real} (hε : 0 < ε)
  statement: exists k : Nat, (p : Real) ^ (-(k : Int)) < ε
  proof: by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert! Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos

中文:
定理 存在_pow_neg_lt
  条件: {ε : 实数} (hε : 0 < ε)
  结论: 存在 k : 自然数, (p : 实数) ^ (-(k : 整数)) < ε
  证明: by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert! Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos

Depends on / 依赖: Nat.lt_pow_self, convert, exists_nat_gt, inv_inv, le_of_lt, lt_of_lt_of_le, lt_pow_self, mod_cast, one_lt, zpow_natCast, zpow_neg, zpow_pos
-/
theorem exists_pow_neg_lt {ε : Real} (hε : 0 < ε) : exists k : Nat, (p : Real) ^ (-(k : Int)) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert! Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos

/--
theorem `exists_pow_neg_lt_rat` / 定理 `exists_pow_neg_lt_rat`

English:
theorem exists_pow_neg_lt_rat
  given: {ε : Rat} (hε : 0 < ε)
  statement: exists k : Nat, (p : Rat) ^ (-(k : Int)) < ε
  proof: by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : Real) = (p : Rat) by simp] at hk
  exact mod_cast hk

中文:
定理 存在_pow_neg_lt_rat
  条件: {ε : 有理数} (hε : 0 < ε)
  结论: 存在 k : 自然数, (p : 有理数) ^ (-(k : 整数)) < ε
  证明: by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : Real) = (p : Rat) by simp] at hk
  exact mod_cast hk

Depends on / 依赖: exists_pow_neg_lt, mod_cast
-/
theorem exists_pow_neg_lt_rat {ε : Rat} (hε : 0 < ε) : exists k : Nat, (p : Rat) ^ (-(k : Int)) < ε := by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : Real) = (p : Rat) by simp] at hk
  exact mod_cast hk

variable {p}

/--
theorem `norm_int_lt_one_iff_dvd` / 定理 `norm_int_lt_one_iff_dvd`

English:
theorem norm_int_lt_one_iff_dvd
  given: (k : Int)
  statement: ‖(k : Int_[p])‖ < 1 ↔ (p : Int) ∣ k
  proof: suffices ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  Padic.norm_intCast_lt_one_iff

中文:
定理 norm_int_lt_one_iff_dvd
  条件: (k : 整数)
  结论: ‖(k : 整数_[p])‖ < 1 ↔ (p : 整数) ∣ k
  证明: suffices ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  Padic.norm_intCast_lt_one_iff

Depends on / 依赖: Padic.norm_intCast_lt_one_iff, Rat_, norm_intCast_eq_padic_norm, norm_intCast_lt_one_iff
-/
theorem norm_int_lt_one_iff_dvd (k : Int) : ‖(k : Int_[p])‖ < 1 ↔ (p : Int) ∣ k :=
  suffices ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  Padic.norm_intCast_lt_one_iff

/--
theorem `norm_int_le_pow_iff_dvd` / 定理 `norm_int_le_pow_iff_dvd`

English:
theorem norm_int_le_pow_iff_dvd
  given: {k : Int} {n : Nat}
  proof: suffices ‖(k : Rat_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  Padic.norm_int_le_pow_iff_dvd _ _

@[simp]

中文:
定理 norm_int_le_pow_iff_dvd
  条件: {k : 整数} {n : 自然数}
  证明: suffices ‖(k : Rat_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  Padic.norm_int_le_pow_iff_dvd _ _

@[simp]

Depends on / 依赖: Padic.norm_int_le_pow_iff_dvd, Rat_, norm_intCast_eq_padic_norm, norm_int_le_pow_iff_dvd
-/
theorem norm_int_le_pow_iff_dvd {k : Int} {n : Nat} :
    ‖(k : Int_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k :=
  suffices ‖(k : Rat_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  Padic.norm_int_le_pow_iff_dvd _ _

@[simp]
/--
lemma `norm_natCast_eq_one_iff` / 引理 `norm_natCast_eq_one_iff`

English:
lemma norm_natCast_eq_one_iff
  given: {n : Nat}
  proof: by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_eq_one_iff]

@[simp]

中文:
引理 norm_natCast_eq_one_iff
  条件: {n : 自然数}
  证明: by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_eq_one_iff]

@[simp]

Depends on / 依赖: Padic.norm_natCast_eq_one_iff, coe_natCast, norm_def, norm_natCast_eq_one_iff
-/
lemma norm_natCast_eq_one_iff {n : Nat} :
    ‖(n : Int_[p])‖ = 1 ↔ p.Coprime n := by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_eq_one_iff]

@[simp]
/--
lemma `norm_natCast_lt_one_iff` / 引理 `norm_natCast_lt_one_iff`

English:
lemma norm_natCast_lt_one_iff
  given: {n : Nat}
  proof: by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_lt_one_iff]

@[simp]

中文:
引理 norm_natCast_lt_one_iff
  条件: {n : 自然数}
  证明: by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_lt_one_iff]

@[simp]

Depends on / 依赖: Padic.norm_natCast_lt_one_iff, coe_natCast, norm_def, norm_natCast_lt_one_iff
-/
lemma norm_natCast_lt_one_iff {n : Nat} :
    ‖(n : Int_[p])‖ < 1 ↔ p ∣ n := by
  rw [norm_def]; rw [coe_natCast]; rw [Padic.norm_natCast_lt_one_iff]

@[simp]
/--
lemma `norm_intCast_eq_one_iff` / 引理 `norm_intCast_eq_one_iff`

English:
lemma norm_intCast_eq_one_iff
  given: {z : Int}
  proof: by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_eq_one_iff]

@[simp]

中文:
引理 norm_intCast_eq_one_iff
  条件: {z : 整数}
  证明: by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_eq_one_iff]

@[simp]

Depends on / 依赖: Padic.norm_intCast_eq_one_iff, coe_intCast, norm_def, norm_intCast_eq_one_iff
-/
lemma norm_intCast_eq_one_iff {z : Int} :
    ‖(z : Int_[p])‖ = 1 ↔ IsCoprime z p := by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_eq_one_iff]

@[simp]
/--
lemma `norm_intCast_lt_one_iff` / 引理 `norm_intCast_lt_one_iff`

English:
lemma norm_intCast_lt_one_iff
  given: {z : Int}
  proof: by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_lt_one_iff]

中文:
引理 norm_intCast_lt_one_iff
  条件: {z : 整数}
  证明: by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_lt_one_iff]

Depends on / 依赖: Padic.norm_intCast_lt_one_iff, coe_intCast, norm_def, norm_intCast_lt_one_iff
-/
lemma norm_intCast_lt_one_iff {z : Int} :
    ‖(z : Int_[p])‖ < 1 ↔ (p : Int) ∣ z := by
  rw [norm_def]; rw [coe_intCast]; rw [Padic.norm_intCast_lt_one_iff]


/--
lemma `valuation_coe_nonneg` / 引理 `valuation_coe_nonneg`

English:
lemma valuation_coe_nonneg
  statement: 0 <= (x : Rat_[p]).valuation
  proof: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have := x.2
  rwa [Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx, zpow_le_one_iff_right₀, neg_nonpos]
    at this
  exact mod_cast hp.out.one_lt

中文:
引理 valuation_coe_nonneg
  结论: 0 <= (x : Rat_[p]).valuation
  证明: by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have := x.2
  rwa [Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx, zpow_le_one_iff_right₀, neg_nonpos]
    at this
  exact mod_cast hp.out.one_lt

Depends on / 依赖: Padic.norm_eq_zpow_neg_valuation, coe_ne_zero, eq_or_ne, hp.out.one_lt, mod_cast, neg_nonpos, norm_eq_zpow_neg_valuation, one_lt
-/
lemma valuation_coe_nonneg : 0 <= (x : Rat_[p]).valuation := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have := x.2
  rwa [Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx, zpow_le_one_iff_right₀, neg_nonpos]
    at this
  exact mod_cast hp.out.one_lt

/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: (x : Int_[p])
  body: (x : Rat_[p]).valuation.toNat

中文:
定义 valuation
  签名: (x : 整数_[p])
  定义体: (x : Rat_[p]).valuation.toNat

Depends on / 依赖: Rat_, valuation, valuation.toNat
-/
def valuation (x : Int_[p]) : Nat := (x : Rat_[p]).valuation.toNat

/--
lemma `valuation_coe` / 引理 `valuation_coe`

English:
lemma valuation_coe
  given: (x : Int_[p])
  statement: (x : Rat_[p]).valuation = x.valuation
  proof: by
  simp [valuation, valuation_coe_nonneg]

中文:
引理 valuation_coe
  条件: (x : 整数_[p])
  结论: (x : Rat_[p]).valuation = x.valuation
  证明: by
  simp [valuation, valuation_coe_nonneg]
-/
@[simp, norm_cast] lemma valuation_coe (x : Int_[p]) : (x : Rat_[p]).valuation = x.valuation := by
  simp [valuation, valuation_coe_nonneg]

/--
lemma `valuation_zero` / 引理 `valuation_zero`

English:
lemma valuation_zero
  statement: valuation (0 : Int_[p]) = 0
  proof: by simp [valuation]

中文:
引理 valuation_zero
  结论: valuation (0 : 整数_[p]) = 0
  证明: by simp [valuation]
-/
@[simp] lemma valuation_zero : valuation (0 : Int_[p]) = 0 := by simp [valuation]
/--
lemma `valuation_one` / 引理 `valuation_one`

English:
lemma valuation_one
  statement: valuation (1 : Int_[p]) = 0
  proof: by simp [valuation]

中文:
引理 valuation_one
  结论: valuation (1 : 整数_[p]) = 0
  证明: by simp [valuation]
-/
@[simp] lemma valuation_one : valuation (1 : Int_[p]) = 0 := by simp [valuation]
/--
lemma `valuation_p` / 引理 `valuation_p`

English:
lemma valuation_p
  statement: valuation (p : Int_[p]) = 1
  proof: by simp [valuation]

中文:
引理 valuation_p
  结论: valuation (p : 整数_[p]) = 1
  证明: by simp [valuation]
-/
@[simp] lemma valuation_p : valuation (p : Int_[p]) = 1 := by simp [valuation]

/--
lemma `le_valuation_add` / 引理 `le_valuation_add`

English:
lemma le_valuation_add
  given: (hxy : x + y != 0)
  statement: min x.valuation y.valuation <= (x + y).valuation
  proof: by
zify; simpa [← valuation_coe] using Padic.le_valuation_add coe_ne_zero.2 hxy

中文:
引理 le_valuation_add
  条件: (hxy : x + y != 0)
  结论: 最小值 x.valuation y.valuation <= (x + y).valuation
  证明: by
zify; simpa [← valuation_coe] using Padic.le_valuation_add coe_ne_zero.2 hxy

Depends on / 依赖: Padic.le_valuation_add, coe_ne_zero, le_valuation_add, valuation_coe
-/
lemma le_valuation_add (hxy : x + y != 0) : min x.valuation y.valuation <= (x + y).valuation := by
zify; simpa [← valuation_coe] using Padic.le_valuation_add coe_ne_zero.2 hxy

/--
lemma `valuation_mul` / 引理 `valuation_mul`

English:
lemma valuation_mul
  given: (hx : x != 0) (hy : y != 0)
  proof: by
  zify; simp [← valuation_coe, Padic.valuation_mul (coe_ne_zero.2 hx) (coe_ne_zero.2 hy)]

@[simp]

中文:
引理 valuation_mul
  条件: (hx : x != 0) (hy : y != 0)
  证明: by
  zify; simp [← valuation_coe, Padic.valuation_mul (coe_ne_zero.2 hx) (coe_ne_zero.2 hy)]

@[simp]
-/
@[simp] lemma valuation_mul (hx : x != 0) (hy : y != 0) :
    (x * y).valuation = x.valuation + y.valuation := by
  zify; simp [← valuation_coe, Padic.valuation_mul (coe_ne_zero.2 hx) (coe_ne_zero.2 hy)]

@[simp]
/--
lemma `valuation_pow` / 引理 `valuation_pow`

English:
lemma valuation_pow
  given: (x : Int_[p]) (n : Nat)
  statement: (x ^ n).valuation = n * x.valuation
  proof: by
  zify; simp [← valuation_coe]

中文:
引理 valuation_pow
  条件: (x : 整数_[p]) (n : 自然数)
  结论: (x ^ n).valuation = n * x.valuation
  证明: by
  zify; simp [← valuation_coe]

Depends on / 依赖: valuation_coe
-/
lemma valuation_pow (x : Int_[p]) (n : Nat) : (x ^ n).valuation = n * x.valuation := by
  zify; simp [← valuation_coe]

/--
lemma `norm_eq_zpow_neg_valuation` / 引理 `norm_eq_zpow_neg_valuation`

English:
lemma norm_eq_zpow_neg_valuation
  given: {x : Int_[p]} (hx : x != 0)
  statement: ‖x‖ = p ^ (-x.valuation : Int)
  proof: by
  simp [norm_def, Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx]

中文:
引理 norm_eq_zpow_neg_valuation
  条件: {x : 整数_[p]} (hx : x != 0)
  结论: ‖x‖ = p ^ (-x.valuation : 整数)
  证明: by
  simp [norm_def, Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx]

Depends on / 依赖: Padic.norm_eq_zpow_neg_valuation, coe_ne_zero, norm_def, norm_eq_zpow_neg_valuation
-/
lemma norm_eq_zpow_neg_valuation {x : Int_[p]} (hx : x != 0) : ‖x‖ = p ^ (-x.valuation : Int) := by
  simp [norm_def, Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx]

-- TODO: Do we really need this lemma?
@[simp]
/--
theorem `valuation_p_pow_mul` / 定理 `valuation_p_pow_mul`

English:
theorem valuation_p_pow_mul
  given: (n : Nat) (c : Int_[p]) (hc : c != 0)
  proof: by
  rw [valuation_mul (NeZero.ne _) hc]; rw [valuation_pow]; rw [valuation_p]; rw [mul_one]

中文:
定理 valuation_p_pow_mul
  条件: (n : 自然数) (c : 整数_[p]) (hc : c != 0)
  证明: by
  rw [valuation_mul (NeZero.ne _) hc]; rw [valuation_pow]; rw [valuation_p]; rw [mul_one]

Depends on / 依赖: NeZero, NeZero.ne, mul_one, valuation_mul, valuation_p, valuation_pow
-/
theorem valuation_p_pow_mul (n : Nat) (c : Int_[p]) (hc : c != 0) :
    ((p : Int_[p]) ^ n * c).valuation = n + c.valuation := by
  rw [valuation_mul (NeZero.ne _) hc]; rw [valuation_pow]; rw [valuation_p]; rw [mul_one]

section Units

/-! ### Units of `ℤ_[p]` -/

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_inv` / 定理 `mul_inv`

English:
theorem mul_inv
  statement: forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv = 1
  proof: fun h' => zero_ne_one' Rat_[p] (by simp [h'] at h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    dsimp only
    rw [dif_pos h]
    apply Subtype.ext_iff.2
    simp [mul_inv_cancel₀ hk]

中文:
定理 mul_inv
  结论: 对任意 {z : 整数_[p]}, ‖z‖ = 1 -> z * z.inv = 1
  证明: fun h' => zero_ne_one' Rat_[p] (by simp [h'] at h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    dsimp only
    rw [dif_pos h]
    apply Subtype.ext_iff.2
    simp [mul_inv_cancel₀ hk]

Depends on / 依赖: Rat_, zero_ne_one
-/
theorem mul_inv : forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv = 1
  | ⟨k, _⟩, h => by
    have hk : k != 0 := fun h' => zero_ne_one' Rat_[p] (by simp [h'] at h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    dsimp only
    rw [dif_pos h]
    apply Subtype.ext_iff.2
    simp [mul_inv_cancel₀ hk]

/--
theorem `inv_mul` / 定理 `inv_mul`

English:
theorem inv_mul
  given: {z : Int_[p]} (hz : ‖z‖ = 1)
  statement: z.inv * z = 1
  proof: by rw [mul_comm, mul_inv hz]

中文:
定理 inv_mul
  条件: {z : 整数_[p]} (hz : ‖z‖ = 1)
  结论: z.inv * z = 1
  证明: by rw [mul_comm, mul_inv hz]

Depends on / 依赖: mul_comm, mul_inv
-/
theorem inv_mul {z : Int_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  given: {z : Int_[p]}
  statement: IsUnit z ↔ ‖z‖ = 1
  proof: ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine le_antisymm (norm_le_one _) ?_
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

中文:
定理 isUnit_iff
  条件: {z : 整数_[p]}
  结论: 是单位 z ↔ ‖z‖ = 1
  证明: ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine le_antisymm (norm_le_one _) ?_
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

Depends on / 依赖: inv_mul, isUnit_iff_dvd_one, le_antisymm, mul_inv, mul_le_mul_of_nonneg_left, mul_one, norm_le_one, norm_mul, norm_nonneg, norm_one, z.inv
-/
theorem isUnit_iff {z : Int_[p]} : IsUnit z ↔ ‖z‖ = 1 :=
  ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine le_antisymm (norm_le_one _) ?_
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩

/--
theorem `norm_lt_one_add` / 定理 `norm_lt_one_add`

English:
theorem norm_lt_one_add
  given: {z1 z2 : Int_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1)
  statement: ‖z1 + z2‖ < 1
  proof: lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

中文:
定理 norm_lt_one_add
  条件: {z1 z2 : 整数_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1)
  结论: ‖z1 + z2‖ < 1
  证明: lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

Depends on / 依赖: lt_of_le_of_lt, max_lt, nonarchimedean
-/
theorem norm_lt_one_add {z1 z2 : Int_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
  lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)

/--
theorem `norm_lt_one_mul` / 定理 `norm_lt_one_mul`

English:
theorem norm_lt_one_mul
  given: {z1 z2 : Int_[p]} (hz2 : ‖z2‖ < 1)
  statement: ‖z1 * z2‖ < 1
  proof: calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

中文:
定理 norm_lt_one_mul
  条件: {z1 z2 : 整数_[p]} (hz2 : ‖z2‖ < 1)
  结论: ‖z1 * z2‖ < 1
  证明: calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

Depends on / 依赖: mul_lt_one_of_nonneg_of_lt_one_right, norm_le_one, norm_nonneg
-/
theorem norm_lt_one_mul {z1 z2 : Int_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
  calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

/--
theorem `mem_nonunits` / 定理 `mem_nonunits`

English:
theorem mem_nonunits
  given: {z : Int_[p]}
  statement: z in nonunits Int_[p] ↔ ‖z‖ < 1
  proof: by
  simp [norm_le_one z, nonunits, isUnit_iff]

中文:
定理 mem_nonunits
  条件: {z : 整数_[p]}
  结论: z in nonunits 整数_[p] ↔ ‖z‖ < 1
  证明: by
  simp [norm_le_one z, nonunits, isUnit_iff]

Depends on / 依赖: isUnit_iff, nonunits, norm_le_one
-/
theorem mem_nonunits {z : Int_[p]} : z in nonunits Int_[p] ↔ ‖z‖ < 1 := by
  simp [norm_le_one z, nonunits, isUnit_iff]

/--
theorem `not_isUnit_iff` / 定理 `not_isUnit_iff`

English:
theorem not_isUnit_iff
  given: {z : Int_[p]}
  statement: ¬IsUnit z ↔ ‖z‖ < 1
  proof: by
  simpa using mem_nonunits

中文:
定理 not_isUnit_iff
  条件: {z : 整数_[p]}
  结论: ¬是单位 z ↔ ‖z‖ < 1
  证明: by
  simpa using mem_nonunits

Depends on / 依赖: mem_nonunits
-/
theorem not_isUnit_iff {z : Int_[p]} : ¬IsUnit z ↔ ‖z‖ < 1 := by
  simpa using mem_nonunits

/--
Definition of `mkUnits` / `mkUnits` 的定义

English:
definition mkUnits
  signature: {u : Rat_[p]} (h : ‖u‖ = 1)
  body: let z : Int_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]

中文:
定义 mkUnits
  签名: {u : Rat_[p]} (h : ‖u‖ = 1)
  定义体: let z : Int_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]

Depends on / 依赖: Int_, inv_mul, le_of_eq, mul_inv, z.inv
-/
def mkUnits {u : Rat_[p]} (h : ‖u‖ = 1) : Int_[p]ˣ :=
  let z : Int_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
/--
lemma `val_mkUnits` / 引理 `val_mkUnits`

English:
lemma val_mkUnits
  given: {u : Rat_[p]} (h : ‖u‖ = 1)
  statement: (mkUnits h).val = ⟨u, h.le⟩
  proof: rfl

中文:
引理 val_mkUnits
  条件: {u : Rat_[p]} (h : ‖u‖ = 1)
  结论: (mkUnits h).val = ⟨u, h.le⟩
  证明: rfl
-/
lemma val_mkUnits {u : Rat_[p]} (h : ‖u‖ = 1) : (mkUnits h).val = ⟨u, h.le⟩ := rfl

/--
theorem `mkUnits_eq` / 定理 `mkUnits_eq`

English:
theorem mkUnits_eq
  given: {u : Rat_[p]} (h : ‖u‖ = 1)
  statement: ((mkUnits h : Int_[p]) : Rat_[p]) = u
  proof: rfl

@[simp]

中文:
定理 mkUnits_eq
  条件: {u : Rat_[p]} (h : ‖u‖ = 1)
  结论: ((mkUnits h : 整数_[p]) : Rat_[p]) = u
  证明: rfl

@[simp]
-/
theorem mkUnits_eq {u : Rat_[p]} (h : ‖u‖ = 1) : ((mkUnits h : Int_[p]) : Rat_[p]) = u := rfl

@[simp]
/--
theorem `norm_units` / 定理 `norm_units`

English:
theorem norm_units
  given: (u : Int_[p]ˣ)
  statement: ‖(u : Int_[p])‖ = 1
  proof: isUnit_iff.mp by simp

中文:
定理 norm_units
  条件: (u : 整数_[p]ˣ)
  结论: ‖(u : 整数_[p])‖ = 1
  证明: isUnit_iff.mp by simp

Depends on / 依赖: isUnit_iff, isUnit_iff.mp
-/
theorem norm_units (u : Int_[p]ˣ) : ‖(u : Int_[p])‖ = 1 := isUnit_iff.mp by simp

/--
Definition of `unitCoeff` / `unitCoeff` 的定义

English:
definition unitCoeff
  signature: {x : Int_[p]} (hx : x != 0)
  body: let u : Rat_[p] := x * (p : Rat_[p]) ^ (-x.valuation : Int)
  have hu : ‖u‖ = 1 := by
    simp [u, hx, pow_ne_zero _ (NeZero.ne _), norm_eq_zpow_neg_valuation]
  mkUnits hu

@[simp]

中文:
定义 unitCoeff
  签名: {x : 整数_[p]} (hx : x != 0)
  定义体: let u : Rat_[p] := x * (p : Rat_[p]) ^ (-x.valuation : Int)
  have hu : ‖u‖ = 1 := by
    simp [u, hx, pow_ne_zero _ (NeZero.ne _), norm_eq_zpow_neg_valuation]
  mkUnits hu

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, Rat_, mkUnits, norm_eq_zpow_neg_valuation, pow_ne_zero, valuation, x.valuation
-/
def unitCoeff {x : Int_[p]} (hx : x != 0) : Int_[p]ˣ :=
  let u : Rat_[p] := x * (p : Rat_[p]) ^ (-x.valuation : Int)
  have hu : ‖u‖ = 1 := by
    simp [u, hx, pow_ne_zero _ (NeZero.ne _), norm_eq_zpow_neg_valuation]
  mkUnits hu

@[simp]
/--
theorem `unitCoeff_coe` / 定理 `unitCoeff_coe`

English:
theorem unitCoeff_coe
  given: {x : Int_[p]} (hx : x != 0)
  proof: rfl

中文:
定理 unitCoeff_coe
  条件: {x : 整数_[p]} (hx : x != 0)
  证明: rfl
-/
theorem unitCoeff_coe {x : Int_[p]} (hx : x != 0) :
    (unitCoeff hx : Rat_[p]) = x * (p : Rat_[p]) ^ (-x.valuation : Int) := rfl

/--
theorem `unitCoeff_spec` / 定理 `unitCoeff_spec`

English:
theorem unitCoeff_spec
  given: {x : Int_[p]} (hx : x != 0)
  proof: by
  apply Subtype.coe_injective
  push_cast
  rw [unitCoeff_coe]; rw [mul_assoc]; rw [← zpow_natCast]; rw [← zpow_add₀]
  · simp
  · exact NeZero.ne _

中文:
定理 unitCoeff_spec
  条件: {x : 整数_[p]} (hx : x != 0)
  证明: by
  apply Subtype.coe_injective
  push_cast
  rw [unitCoeff_coe]; rw [mul_assoc]; rw [← zpow_natCast]; rw [← zpow_add₀]
  · simp
  · exact NeZero.ne _

Depends on / 依赖: NeZero, NeZero.ne, Subtype, Subtype.coe_injective, coe_injective, mul_assoc, unitCoeff_coe, zpow_natCast
-/
theorem unitCoeff_spec {x : Int_[p]} (hx : x != 0) :
    x = (unitCoeff hx : Int_[p]) * (p : Int_[p]) ^ x.valuation := by
  apply Subtype.coe_injective
  push_cast
  rw [unitCoeff_coe]; rw [mul_assoc]; rw [← zpow_natCast]; rw [← zpow_add₀]
  · simp
  · exact NeZero.ne _

/--
theorem `isUnit_den` / 定理 `isUnit_den`

English:
theorem isUnit_den
  given: {p : Nat} [hp_prime : Fact p.Prime] (r : Rat) (h : ‖(r : Rat_[p])‖ <= 1)
  proof: by
  rw [isUnit_iff]
  apply le_antisymm (r.den : Int_[p]).2
  rw [← not_lt]; rw [coe_natCast]
  intro norm_denom_lt
  have hr : ‖(r * r.den : Rat_[p])‖ = ‖(r.num : Rat_[p])‖ := by
    congr
    rw_mod_cast [@Rat.mul_den_eq_num r]
  rw [padicNormE.mul] at hr
  have key : ‖(r.num : Rat_[p])‖ < 1 := by
    calc
      _ = _ := hr.symm
      _ < 1 * 1 := mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one
      _ = 1 := mul_one 1
  have : ↑p ∣ r.num ∧ (p : Int) ∣ r.den := by
    simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_e_of_padicInt]
    exact ⟨key, norm_denom_lt⟩
  apply hp_prime.1.not_dvd_one
  rwa [← r.reduced.gcd_eq_one, Nat.dvd_gcd_iff, ← Int.natCast_dvd, ← Int.natCast_dvd_natCast]

中文:
定理 isUnit_den
  条件: {p : 自然数} [hp_prime : Fact p.素] (r : 有理数) (h : ‖(r : Rat_[p])‖ <= 1)
  证明: by
  rw [isUnit_iff]
  apply le_antisymm (r.den : Int_[p]).2
  rw [← not_lt]; rw [coe_natCast]
  intro norm_denom_lt
  have hr : ‖(r * r.den : Rat_[p])‖ = ‖(r.num : Rat_[p])‖ := by
    congr
    rw_mod_cast [@Rat.mul_den_eq_num r]
  rw [padicNormE.mul] at hr
  have key : ‖(r.num : Rat_[p])‖ < 1 := by
    calc
      _ = _ := hr.symm
      _ < 1 * 1 := mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one
      _ = 1 := mul_one 1
  have : ↑p ∣ r.num ∧ (p : Int) ∣ r.den := by
    simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_e_of_padicInt]
    exact ⟨key, norm_denom_lt⟩
  apply hp_prime.1.not_dvd_one
  rwa [← r.reduced.gcd_eq_one, Nat.dvd_gcd_iff, ← Int.natCast_dvd, ← Int.natCast_dvd_natCast]

Depends on / 依赖: Int_, Rat.mul_den_eq_num, Rat_, coe_natCast, hr.symm, isUnit_iff, le_antisymm, mul_den_eq_num, mul_lt_mul, mul_one, norm_denom_lt, norm_int_lt_one_iff_dvd, norm_nonneg, not_lt, padicNormE, padicNormE.mul, padic_norm_e_of_padicInt, r.den, r.num, rw_mod_cast
-/
theorem isUnit_den {p : Nat} [hp_prime : Fact p.Prime] (r : Rat) (h : ‖(r : Rat_[p])‖ <= 1) :
    IsUnit (r.den : Int_[p]) := by
  rw [isUnit_iff]
  apply le_antisymm (r.den : Int_[p]).2
  rw [← not_lt]; rw [coe_natCast]
  intro norm_denom_lt
  have hr : ‖(r * r.den : Rat_[p])‖ = ‖(r.num : Rat_[p])‖ := by
    congr
    rw_mod_cast [@Rat.mul_den_eq_num r]
  rw [padicNormE.mul] at hr
  have key : ‖(r.num : Rat_[p])‖ < 1 := by
    calc
      _ = _ := hr.symm
      _ < 1 * 1 := mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one
      _ = 1 := mul_one 1
  have : ↑p ∣ r.num ∧ (p : Int) ∣ r.den := by
    simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_e_of_padicInt]
    exact ⟨key, norm_denom_lt⟩
  apply hp_prime.1.not_dvd_one
  rwa [← r.reduced.gcd_eq_one, Nat.dvd_gcd_iff, ← Int.natCast_dvd, ← Int.natCast_dvd_natCast]

end Units

section NormLeIff


/--
theorem `norm_le_pow_iff_le_valuation` / 定理 `norm_le_pow_iff_le_valuation`

English:
theorem norm_le_pow_iff_le_valuation
  given: (x : Int_[p]) (hx : x != 0) (n : Nat)
  proof: by
  rw [norm_eq_zpow_neg_valuation hx]; rw [zpow_le_zpow_iff_right₀]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
  exact mod_cast hp.out.one_lt

中文:
定理 norm_le_pow_iff_le_valuation
  条件: (x : 整数_[p]) (hx : x != 0) (n : 自然数)
  证明: by
  rw [norm_eq_zpow_neg_valuation hx]; rw [zpow_le_zpow_iff_right₀]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
  exact mod_cast hp.out.one_lt

Depends on / 依赖: Nat.cast_le, cast_le, hp.out.one_lt, mod_cast, neg_le_neg_iff, norm_eq_zpow_neg_valuation, one_lt
-/
theorem norm_le_pow_iff_le_valuation (x : Int_[p]) (hx : x != 0) (n : Nat) :
    ‖x‖ <= (p : Real) ^ (-n : Int) ↔ n <= x.valuation := by
  rw [norm_eq_zpow_neg_valuation hx]; rw [zpow_le_zpow_iff_right₀]; rw [neg_le_neg_iff]; rw [Nat.cast_le]
  exact mod_cast hp.out.one_lt

/--
theorem `mem_span_pow_iff_le_valuation` / 定理 `mem_span_pow_iff_le_valuation`

English:
theorem mem_span_pow_iff_le_valuation
  given: (x : Int_[p]) (hx : x != 0) (n : Nat)
  proof: by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c != 0 by
      rw [valuation_p_pow_mul _ _ this]
      exact le_self_add
    contrapose hx
    rw [hx]; rw [mul_zero]
  · nth_rewrite 2 [unitCoeff_spec hx]
    simpa [Units.isUnit, IsUnit.dvd_mul_left] using pow_dvd_pow _

中文:
定理 mem_span_pow_iff_le_valuation
  条件: (x : 整数_[p]) (hx : x != 0) (n : 自然数)
  证明: by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c != 0 by
      rw [valuation_p_pow_mul _ _ this]
      exact le_self_add
    contrapose hx
    rw [hx]; rw [mul_zero]
  · nth_rewrite 2 [unitCoeff_spec hx]
    simpa [Units.isUnit, IsUnit.dvd_mul_left] using pow_dvd_pow _

Depends on / 依赖: Ideal.mem_span_singleton, IsUnit, IsUnit.dvd_mul_left, Units.isUnit, contrapose, dvd_mul_left, isUnit, le_self_add, mem_span_singleton, mul_zero, nth_rewrite, pow_dvd_pow, unitCoeff_spec, valuation_p_pow_mul
-/
theorem mem_span_pow_iff_le_valuation (x : Int_[p]) (hx : x != 0) (n : Nat) :
    x in (Ideal.span {(p : Int_[p]) ^ n} : Ideal Int_[p]) ↔ n <= x.valuation := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c != 0 by
      rw [valuation_p_pow_mul _ _ this]
      exact le_self_add
    contrapose hx
    rw [hx]; rw [mul_zero]
  · nth_rewrite 2 [unitCoeff_spec hx]
    simpa [Units.isUnit, IsUnit.dvd_mul_left] using pow_dvd_pow _

/--
theorem `norm_le_pow_iff_mem_span_pow` / 定理 `norm_le_pow_iff_mem_span_pow`

English:
theorem norm_le_pow_iff_mem_span_pow
  given: (x : Int_[p]) (n : Nat)
  proof: by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_natCast, inv_nonneg, iff_true, Submodule.zero_mem]
    exact mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx]; rw [mem_span_pow_iff_le_valuation x hx]

中文:
定理 norm_le_pow_iff_mem_span_pow
  条件: (x : 整数_[p]) (n : 自然数)
  证明: by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_natCast, inv_nonneg, iff_true, Submodule.zero_mem]
    exact mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx]; rw [mem_span_pow_iff_le_valuation x hx]

Depends on / 依赖: Nat.zero_le, Submodule, Submodule.zero_mem, iff_true, inv_nonneg, mem_span_pow_iff_le_valuation, mod_cast, norm_le_pow_iff_le_valuation, norm_zero, zero_le, zero_mem, zpow_natCast, zpow_neg
-/
theorem norm_le_pow_iff_mem_span_pow (x : Int_[p]) (n : Nat) :
    ‖x‖ <= (p : Real) ^ (-n : Int) ↔ x in (Ideal.span {(p : Int_[p]) ^ n} : Ideal Int_[p]) := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_natCast, inv_nonneg, iff_true, Submodule.zero_mem]
    exact mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx]; rw [mem_span_pow_iff_le_valuation x hx]

/--
theorem `norm_le_pow_iff_norm_lt_pow_add_one` / 定理 `norm_le_pow_iff_norm_lt_pow_add_one`

English:
theorem norm_le_pow_iff_norm_lt_pow_add_one
  given: (x : Int_[p]) (n : Int)
  proof: by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

中文:
定理 norm_le_pow_iff_norm_lt_pow_add_one
  条件: (x : 整数_[p]) (n : 整数)
  证明: by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

Depends on / 依赖: Padic.norm_le_pow_iff_norm_lt_pow_add_one, norm_def, norm_le_pow_iff_norm_lt_pow_add_one
-/
theorem norm_le_pow_iff_norm_lt_pow_add_one (x : Int_[p]) (n : Int) :
    ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n + 1) := by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _

/--
theorem `norm_lt_pow_iff_norm_le_pow_sub_one` / 定理 `norm_lt_pow_iff_norm_le_pow_sub_one`

English:
theorem norm_lt_pow_iff_norm_le_pow_sub_one
  given: (x : Int_[p]) (n : Int)
  proof: by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

中文:
定理 norm_lt_pow_iff_norm_le_pow_sub_one
  条件: (x : 整数_[p]) (n : 整数)
  证明: by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

Depends on / 依赖: norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel
-/
theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : Int_[p]) (n : Int) :
    ‖x‖ < (p : Real) ^ n ↔ ‖x‖ <= (p : Real) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one]; rw [sub_add_cancel]

/--
theorem `norm_lt_one_iff_dvd` / 定理 `norm_lt_one_iff_dvd`

English:
theorem norm_lt_one_iff_dvd
  given: (x : Int_[p])
  statement: ‖x‖ < 1 ↔ ↑p ∣ x
  proof: by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton]; rw [pow_one] at this
  rw [← this]; rw [norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.natCast_succ, neg_add_cancel, zero_add]

@[simp]

中文:
定理 norm_lt_one_iff_dvd
  条件: (x : 整数_[p])
  结论: ‖x‖ < 1 ↔ ↑p ∣ x
  证明: by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton]; rw [pow_one] at this
  rw [← this]; rw [norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.natCast_succ, neg_add_cancel, zero_add]

@[simp]

Depends on / 依赖: Ideal.mem_span_singleton, Int.natCast_succ, Int.ofNat_zero, mem_span_singleton, natCast_succ, neg_add_cancel, norm_le_pow_iff_mem_span_pow, norm_le_pow_iff_norm_lt_pow_add_one, ofNat_zero, pow_one, zero_add, zpow_zero
-/
theorem norm_lt_one_iff_dvd (x : Int_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x := by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton]; rw [pow_one] at this
  rw [← this]; rw [norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.natCast_succ, neg_add_cancel, zero_add]

@[simp]
/--
theorem `pow_p_dvd_int_iff` / 定理 `pow_p_dvd_int_iff`

English:
theorem pow_p_dvd_int_iff
  given: (n : Nat) (a : Int)
  statement: (p : Int_[p]) ^ n ∣ a ↔ (p ^ n : Int) ∣ a
  proof: by
  rw [← Nat.cast_pow]; rw [← norm_int_le_pow_iff_dvd]; rw [norm_le_pow_iff_mem_span_pow]; rw [Ideal.mem_span_singleton]; rw [Nat.cast_pow]

中文:
定理 pow_p_dvd_int_iff
  条件: (n : 自然数) (a : 整数)
  结论: (p : 整数_[p]) ^ n ∣ a ↔ (p ^ n : 整数) ∣ a
  证明: by
  rw [← Nat.cast_pow]; rw [← norm_int_le_pow_iff_dvd]; rw [norm_le_pow_iff_mem_span_pow]; rw [Ideal.mem_span_singleton]; rw [Nat.cast_pow]

Depends on / 依赖: Ideal.mem_span_singleton, Nat.cast_pow, cast_pow, mem_span_singleton, norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow
-/
theorem pow_p_dvd_int_iff (n : Nat) (a : Int) : (p : Int_[p]) ^ n ∣ a ↔ (p ^ n : Int) ∣ a := by
  rw [← Nat.cast_pow]; rw [← norm_int_le_pow_iff_dvd]; rw [norm_le_pow_iff_mem_span_pow]; rw [Ideal.mem_span_singleton]; rw [Nat.cast_pow]

end NormLeIff

section Dvr


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalRing Int_[p]
  body: IsLocalRing.of_nonunits_add by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add

中文:
实例 :
  签名: 是局部环 整数_[p]
  定义体: IsLocalRing.of_nonunits_add by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add

Depends on / 依赖: IsLocalRing, IsLocalRing.of_nonunits_add, mem_nonunits, norm_lt_one_add, of_nonunits_add
-/
instance : IsLocalRing Int_[p] :=
IsLocalRing.of_nonunits_add by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add

/--
theorem `p_nonunit` / 定理 `p_nonunit`

English:
theorem p_nonunit
  statement: (p : Int_[p]) in nonunits Int_[p]
  proof: by
have : (p : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ mod_cast hp.out.one_lt
  rwa [← norm_p, ← mem_nonunits] at this

中文:
定理 p_nonunit
  结论: (p : 整数_[p]) in nonunits 整数_[p]
  证明: by
have : (p : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ mod_cast hp.out.one_lt
  rwa [← norm_p, ← mem_nonunits] at this

Depends on / 依赖: hp.out.one_lt, mem_nonunits, mod_cast, norm_p, one_lt
-/
theorem p_nonunit : (p : Int_[p]) in nonunits Int_[p] := by
have : (p : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ mod_cast hp.out.one_lt
  rwa [← norm_p, ← mem_nonunits] at this

/--
theorem `maximalIdeal_eq_span_p` / 定理 `maximalIdeal_eq_span_p`

English:
theorem maximalIdeal_eq_span_p
  statement: maximalIdeal Int_[p] = Ideal.span {(p : Int_[p])}
  proof: by
  apply le_antisymm
  · intro x hx
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonunit

中文:
定理 maximalIdeal_eq_span_p
  结论: maximalIdeal 整数_[p] = 理想.span {(p : 整数_[p])}
  证明: by
  apply le_antisymm
  · intro x hx
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonunit

Depends on / 依赖: Ideal.mem_span_singleton, Ideal.span_le, IsLocalRing, IsLocalRing.mem_maximalIdeal, Set.singleton_subset_iff, le_antisymm, mem_maximalIdeal, mem_nonunits, mem_span_singleton, norm_lt_one_iff_dvd, p_nonunit, singleton_subset_iff, span_le
-/
theorem maximalIdeal_eq_span_p : maximalIdeal Int_[p] = Ideal.span {(p : Int_[p])} := by
  apply le_antisymm
  · intro x hx
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonunit

/--
theorem `prime_p` / 定理 `prime_p`

English:
theorem prime_p
  statement: Prime (p : Int_[p])
  proof: by
  rw [← Ideal.span_singleton_prime]; rw [← maximalIdeal_eq_span_p]
  · infer_instance
  · exact NeZero.ne _

中文:
定理 prime_p
  结论: 素 (p : 整数_[p])
  证明: by
  rw [← Ideal.span_singleton_prime]; rw [← maximalIdeal_eq_span_p]
  · infer_instance
  · exact NeZero.ne _

Depends on / 依赖: Ideal.span_singleton_prime, NeZero, NeZero.ne, infer_instance, maximalIdeal_eq_span_p, span_singleton_prime
-/
theorem prime_p : Prime (p : Int_[p]) := by
  rw [← Ideal.span_singleton_prime]; rw [← maximalIdeal_eq_span_p]
  · infer_instance
  · exact NeZero.ne _

/--
theorem `irreducible_p` / 定理 `irreducible_p`

English:
theorem irreducible_p
  statement: Irreducible (p : Int_[p])
  proof: Prime.irreducible prime_p

中文:
定理 irreducible_p
  结论: 不可约 (p : 整数_[p])
  证明: Prime.irreducible prime_p

Depends on / 依赖: Prime.irreducible, irreducible, prime_p
-/
theorem irreducible_p : Irreducible (p : Int_[p]) := Prime.irreducible prime_p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscreteValuationRing Int_[p]
  body: IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩

中文:
实例 :
  签名: 是离散赋值环 整数_[p]
  定义体: IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization, irreducible_p, mul_comm, ofHasUnitMulPowIrreducibleFactorization, unitCoeff, unitCoeff_spec, valuation, x.valuation
-/
instance : IsDiscreteValuationRing Int_[p] :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩

/--
theorem `ideal_eq_span_pow_p` / 定理 `ideal_eq_span_pow_p`

English:
theorem ideal_eq_span_pow_p
  given: {s : Ideal Int_[p]} (hs : s != ⊥)
  proof: IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

中文:
定理 ideal_eq_span_pow_p
  条件: {s : 理想 整数_[p]} (hs : s != ⊥)
  证明: IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

Depends on / 依赖: IsDiscreteValuationRing, IsDiscreteValuationRing.ideal_eq_span_pow_irreducible, ideal_eq_span_pow_irreducible, irreducible_p
-/
theorem ideal_eq_span_pow_p {s : Ideal Int_[p]} (hs : s != ⊥) :
    exists n : Nat, s = Ideal.span {(p : Int_[p]) ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

open CauSeq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAdicComplete (maximalIdeal Int_[p]) Int_[p]
  body: by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq Int_[p] norm := ⟨x, ?_⟩; swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      rw [← neg_sub]; rw [norm_neg]
      exact hx hn
    · refine ⟨x'.lim, fun n => ?_⟩
      have : (0 : Real) < (p : Real) ^ (-n : Int) := zpow_pos (mod_cast hp.out.pos) _
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases! hin : i <= n
      · exact (hi i le_rfl n hin).le
      · specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i : Int_[p]) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        exact this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

中文:
实例 :
  签名: 是AdicComplete (maximalIdeal 整数_[p]) 整数_[p]
  定义体: by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq Int_[p] norm := ⟨x, ?_⟩; swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      rw [← neg_sub]; rw [norm_neg]
      exact hx hn
    · refine ⟨x'.lim, fun n => ?_⟩
      have : (0 : Real) < (p : Real) ^ (-n : Int) := zpow_pos (mod_cast hp.out.pos) _
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases! hin : i <= n
      · exact (hi i le_rfl n hin).le
      · specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i : Int_[p]) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        exact this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

Depends on / 依赖: CauSeq, Ideal.one_eq_top, Ideal.span_singleton_pow, Int_, SModEq, SModEq.sub_mem, equiv_lim, exists_pow_neg_lt, hp.out.pos, lt_of_le_of_lt, maximalIdeal_eq_span_p, mod_cast, mul_one, neg_sub, norm_le_pow_iff_mem_span_pow, norm_neg, one_eq_top, smul_eq_mul, span_singleton_pow, sub_mem
-/
instance : IsAdicComplete (maximalIdeal Int_[p]) Int_[p] where
  prec' x hx := by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq Int_[p] norm := ⟨x, ?_⟩; swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      rw [← neg_sub]; rw [norm_neg]
      exact hx hn
    · refine ⟨x'.lim, fun n => ?_⟩
      have : (0 : Real) < (p : Real) ^ (-n : Int) := zpow_pos (mod_cast hp.out.pos) _
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases! hin : i <= n
      · exact (hi i le_rfl n hin).le
      · specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i : Int_[p]) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        exact this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

end Dvr

section FractionRing

/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra Int_[p] Rat_[p]
  body: inferInstanceAs Algebra (subring p) _

@[simp]

中文:
实例 algebra
  签名: : 代数 整数_[p] Rat_[p]
  定义体: inferInstanceAs Algebra (subring p) _

@[simp]

Depends on / 依赖: Algebra, subring
-/
instance algebra : Algebra Int_[p] Rat_[p] :=
inferInstanceAs Algebra (subring p) _

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (x : Int_[p])
  statement: algebraMap Int_[p] Rat_[p] x = x
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (x : 整数_[p])
  结论: algebraMap 整数_[p] Rat_[p] x = x
  证明: rfl
-/
theorem algebraMap_apply (x : Int_[p]) : algebraMap Int_[p] Rat_[p] x = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isFractionRing` / 实例 `isFractionRing`

English:
instance isFractionRing
  signature: : IsFractionRing Int_[p] Rat_[p] where
  body: fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ <= 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rw [PadicInt.algebraMap_apply]; rw [Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : Int) = -x.valuation := by
        rw [hn]; rw [Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg]; rw [not_le] at hx
        exact hx.le
      set a := x * (p : Rat_[p]) ^ n with ha
      have ha_norm : ‖a‖ = 1 := by
        have hx : x != 0 := by
          intro h0
          rw [h0]; rw [norm_zero] at hx
          exact hx zero_le_one
        rw [ha]; rw [padicNormE.mul]; rw [Padic.norm_p_pow]; rw [Padic.norm_eq_zpow_neg_valuation hx]; rw [← zpow_add']; rw [hn_coe]; rw [neg_neg]; rw [neg_add_cancel]; rw [zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : Int_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [a, map_pow, map_natCast, algebraMap_apply]
  exists_of_eq := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    exact fun h => ⟨1, by rw [h]⟩

中文:
实例 isFractionRing
  签名: : IsFractionRing 整数_[p] Rat_[p] where
  定义体: fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ <= 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rw [PadicInt.algebraMap_apply]; rw [Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : Int) = -x.valuation := by
        rw [hn]; rw [Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg]; rw [not_le] at hx
        exact hx.le
      set a := x * (p : Rat_[p]) ^ n with ha
      have ha_norm : ‖a‖ = 1 := by
        have hx : x != 0 := by
          intro h0
          rw [h0]; rw [norm_zero] at hx
          exact hx zero_le_one
        rw [ha]; rw [padicNormE.mul]; rw [Padic.norm_p_pow]; rw [Padic.norm_eq_zpow_neg_valuation hx]; rw [← zpow_add']; rw [hn_coe]; rw [neg_neg]; rw [neg_add_cancel]; rw [zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : Int_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [a, map_pow, map_natCast, algebraMap_apply]
  exists_of_eq := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    exact fun h => ⟨1, by rw [h]⟩

Depends on / 依赖: Int.toNat, Int.toNat_of_nonneg, Padic.norm_le_one_iff_val_nonneg, PadicInt, PadicInt.algebraMap_apply, PadicInt.coe_ne_zero, Right.nonneg_neg_iff, Submonoid, Submonoid.coe_one, Subtype, Subtype.coe_mk, algebraMap_apply, coe_mk, coe_ne_zero, coe_one, hn_coe, hx.le, isUnit_iff_ne_zero, map_one, mem_nonZeroDivisors_iff_ne_zero
-/
instance isFractionRing : IsFractionRing Int_[p] Rat_[p] where
  map_units := fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ <= 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one]; rw [map_one]; rw [mul_one]; rw [PadicInt.algebraMap_apply]; rw [Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : Int) = -x.valuation := by
        rw [hn]; rw [Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg]; rw [not_le] at hx
        exact hx.le
      set a := x * (p : Rat_[p]) ^ n with ha
      have ha_norm : ‖a‖ = 1 := by
        have hx : x != 0 := by
          intro h0
          rw [h0]; rw [norm_zero] at hx
          exact hx zero_le_one
        rw [ha]; rw [padicNormE.mul]; rw [Padic.norm_p_pow]; rw [Padic.norm_eq_zpow_neg_valuation hx]; rw [← zpow_add']; rw [hn_coe]; rw [neg_neg]; rw [neg_add_cancel]; rw [zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : Int_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [a, map_pow, map_natCast, algebraMap_apply]
  exists_of_eq := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    exact fun h => ⟨1, by rw [h]⟩

end FractionRing

end PadicInt
