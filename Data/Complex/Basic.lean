/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Torsion
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Tactic.Ring
public import Mathlib.Util.Qq

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. For the result that the complex numbers are algebraically closed, see
`Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

@[expose] public section

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
@[wikidata Q11567]
/--
Definition of `Complex` / `Complex` 的定义

English:
structure Complex
  parameters: : Type where
  axioms and operations (2):
    - re : Real
    - im : Real

中文:
结构 复形
  参数: : 类型 where
  公理与运算 (2 个):
    - re : 实数
    - im : 实数
-/
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : Real
  /-- The imaginary part of a complex number. -/
  im : Real

@[inherit_doc] notation "Complex" => Complex

namespace Complex

open ComplexConjugate

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq Complex
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq 复形
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
noncomputable instance : DecidableEq Complex :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
/--
Definition of `equivRealProd` / `equivRealProd` 的定义

English:
definition equivRealProd
  signature: : Complex ≃ Real × Real where
  body: ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]

中文:
定义 equiv实数Prod
  签名: : 复形 ≃ 实数 × 实数 where
  定义体: ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]

Depends on / 依赖: z.im, z.re
-/
def equivRealProd : Complex ≃ Real × Real where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  statement: forall z : Complex, Complex.mk z.re z.im = z

中文:
定理 eta
  结论: 对任意 z : 复形, 复形.mk z.re z.im = z
-/
theorem eta : forall z : Complex, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: forall {z w : Complex}, z.re = w.re -> z.im = w.im -> z = w

中文:
定理 ext
  结论: 对任意 {z w : 复形}, z.re = w.re -> z.im = w.im -> z = w
-/
theorem ext : forall {z w : Complex}, z.re = w.re -> z.im = w.im -> z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {p : Complex -> Prop}
  statement: (forall x, p x) ↔ forall a b, p ⟨a, b⟩
  proof: by aesop

中文:
引理 «对任意»
  条件: {p : 复形 -> 命题}
  结论: (对任意 x, p x) ↔ 对任意 a b, p ⟨a, b⟩
  证明: by aesop
-/
lemma «forall» {p : Complex -> Prop} : (forall x, p x) ↔ forall a b, p ⟨a, b⟩ := by aesop
/--
lemma `«exists»` / 引理 `«exists»`

English:
lemma «exists»
  given: {p : Complex -> Prop}
  statement: (exists x, p x) ↔ exists a b, p ⟨a, b⟩
  proof: by aesop

中文:
引理 «存在»
  条件: {p : 复形 -> 命题}
  结论: (存在 x, p x) ↔ 存在 a b, p ⟨a, b⟩
  证明: by aesop
-/
lemma «exists» {p : Complex -> Prop} : (exists x, p x) ↔ exists a b, p ⟨a, b⟩ := by aesop

/--
theorem `re_surjective` / 定理 `re_surjective`

English:
theorem re_surjective
  statement: Surjective re
  proof: fun x => ⟨⟨x, 0⟩, rfl⟩

中文:
定理 re_surjective
  结论: 满射 re
  证明: fun x => ⟨⟨x, 0⟩, rfl⟩
-/
theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

/--
theorem `im_surjective` / 定理 `im_surjective`

English:
theorem im_surjective
  statement: Surjective im
  proof: fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]

中文:
定理 im_surjective
  结论: 满射 im
  证明: fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
-/
theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
/--
theorem `range_re` / 定理 `range_re`

English:
theorem range_re
  statement: range re = univ
  proof: re_surjective.range_eq

@[simp]

中文:
定理 range_re
  结论: range re = univ
  证明: re_surjective.range_eq

@[simp]

Depends on / 依赖: range_eq, re_surjective, re_surjective.range_eq
-/
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
/--
theorem `range_im` / 定理 `range_im`

English:
theorem range_im
  statement: range im = univ
  proof: im_surjective.range_eq

中文:
定理 range_im
  结论: range im = univ
  证明: im_surjective.range_eq

Depends on / 依赖: im_surjective, im_surjective.range_eq, range_eq
-/
theorem range_im : range im = univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe, instance_reducible]
/--
Definition of `ofReal` / `ofReal` 的定义

English:
definition ofReal
  signature: (r : Real)
  body: ⟨r, 0⟩

中文:
定义 of实数
  签名: (r : 实数)
  定义体: ⟨r, 0⟩
-/
def ofReal (r : Real) : Complex :=
  ⟨r, 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Real Complex
  body: ⟨ofReal⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Coe 实数 复形
  定义体: ⟨ofReal⟩

@[simp, norm_cast]

Depends on / 依赖: ofReal
-/
instance : Coe Real Complex :=
  ⟨ofReal⟩

@[simp, norm_cast]
/--
theorem `ofReal_re` / 定理 `ofReal_re`

English:
theorem ofReal_re
  given: (r : Real)
  statement: Complex.re (r : Complex) = r
  proof: rfl

@[simp, norm_cast]

中文:
定理 of实数_re
  条件: (r : 实数)
  结论: 复形.re (r : 复形) = r
  证明: rfl

@[simp, norm_cast]
-/
theorem ofReal_re (r : Real) : Complex.re (r : Complex) = r :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_im` / 定理 `ofReal_im`

English:
theorem ofReal_im
  given: (r : Real)
  statement: (r : Complex).im = 0
  proof: rfl

中文:
定理 of实数_im
  条件: (r : 实数)
  结论: (r : 复形).im = 0
  证明: rfl
-/
theorem ofReal_im (r : Real) : (r : Complex).im = 0 :=
  rfl

/--
theorem `ofReal_def` / 定理 `ofReal_def`

English:
theorem ofReal_def
  given: (r : Real)
  statement: (r : Complex) = ⟨r, 0⟩
  proof: rfl

@[simp, norm_cast]

中文:
定理 of实数_def
  条件: (r : 实数)
  结论: (r : 复形) = ⟨r, 0⟩
  证明: rfl

@[simp, norm_cast]
-/
theorem ofReal_def (r : Real) : (r : Complex) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_inj` / 定理 `ofReal_inj`

English:
theorem ofReal_inj
  given: {z w : Real}
  statement: (z : Complex) = w ↔ z = w
  proof: ⟨congrArg re, by apply congrArg⟩

中文:
定理 of实数_inj
  条件: {z w : 实数}
  结论: (z : 复形) = w ↔ z = w
  证明: ⟨congrArg re, by apply congrArg⟩
-/
theorem ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩

/--
theorem `ofReal_injective` / 定理 `ofReal_injective`

English:
theorem ofReal_injective
  statement: Function.Injective ((↑) : Real -> Complex)
  proof: fun _ _ => congrArg re

中文:
定理 of实数_injective
  结论: 函数.单射 ((↑) : 实数 -> 复形)
  证明: fun _ _ => congrArg re
-/
theorem ofReal_injective : Function.Injective ((↑) : Real -> Complex) := fun _ _ => congrArg re

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Complex Real (↑) fun z => z.im = 0 where
  body: ⟨z.re, ext rfl hz.symm⟩

中文:
实例 canLift
  签名: : CanLift 复形 实数 (↑) fun z => z.im = 0 where
  定义体: ⟨z.re, ext rfl hz.symm⟩

Depends on / 依赖: hz.symm, z.re
-/
instance canLift : CanLift Complex Real (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/--
Definition of `reProdIm` / `reProdIm` 的定义

English:
definition reProdIm
  signature: (s t : Set Real)
  body: re ⁻¹' s inter im ⁻¹' t

@[inherit_doc]
infixl:72 " ×Complex " => reProdIm

中文:
定义 reProdIm
  签名: (s t : 集合 实数)
  定义体: re ⁻¹' s inter im ⁻¹' t

@[inherit_doc]
infixl:72 " ×Complex " => reProdIm
-/
def reProdIm (s t : Set Real) : Set Complex :=
  re ⁻¹' s inter im ⁻¹' t

@[inherit_doc]
infixl:72 " ×Complex " => reProdIm

/--
theorem `mem_reProdIm` / 定理 `mem_reProdIm`

English:
theorem mem_reProdIm
  given: {z : Complex} {s t : Set Real}
  statement: z in s ×Complex t ↔ z.re in s ∧ z.im in t
  proof: Iff.rfl

中文:
定理 mem_reProdIm
  条件: {z : 复形} {s t : 集合 实数}
  结论: z in s ×复形 t ↔ z.re in s ∧ z.im in t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_reProdIm {z : Complex} {s t : Set Real} : z in s ×Complex t ↔ z.re in s ∧ z.im in t :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Complex
  body: ⟨(0 : Real)⟩

中文:
实例 :
  签名: 零 复形
  定义体: ⟨(0 : Real)⟩
-/
instance : Zero Complex :=
  ⟨(0 : Real)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Complex
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 复形
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited Complex :=
  ⟨0⟩

@[simp]
/--
theorem `zero_re` / 定理 `zero_re`

English:
theorem zero_re
  statement: (0 : Complex).re = 0
  proof: rfl

@[simp]

中文:
定理 zero_re
  结论: (0 : 复形).re = 0
  证明: rfl

@[simp]
-/
theorem zero_re : (0 : Complex).re = 0 :=
  rfl

@[simp]
/--
theorem `zero_im` / 定理 `zero_im`

English:
theorem zero_im
  statement: (0 : Complex).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 zero_im
  结论: (0 : 复形).im = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem zero_im : (0 : Complex).im = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_zero` / 定理 `ofReal_zero`

English:
theorem ofReal_zero
  statement: ((0 : Real) : Complex) = 0
  proof: rfl

@[simp]

中文:
定理 of实数_zero
  结论: ((0 : 实数) : 复形) = 0
  证明: rfl

@[simp]
-/
theorem ofReal_zero : ((0 : Real) : Complex) = 0 :=
  rfl

@[simp]
/--
theorem `ofReal_eq_zero` / 定理 `ofReal_eq_zero`

English:
theorem ofReal_eq_zero
  given: {z : Real}
  statement: (z : Complex) = 0 ↔ z = 0
  proof: ofReal_inj

中文:
定理 of实数_eq_zero
  条件: {z : 实数}
  结论: (z : 复形) = 0 ↔ z = 0
  证明: ofReal_inj

Depends on / 依赖: ofReal_inj
-/
theorem ofReal_eq_zero {z : Real} : (z : Complex) = 0 ↔ z = 0 :=
  ofReal_inj

/--
theorem `ofReal_ne_zero` / 定理 `ofReal_ne_zero`

English:
theorem ofReal_ne_zero
  given: {z : Real}
  statement: (z : Complex) != 0 ↔ z != 0
  proof: not_congr ofReal_eq_zero

中文:
定理 of实数_ne_zero
  条件: {z : 实数}
  结论: (z : 复形) != 0 ↔ z != 0
  证明: not_congr ofReal_eq_zero

Depends on / 依赖: not_congr, ofReal_eq_zero
-/
theorem ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔ z != 0 :=
  not_congr ofReal_eq_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Complex
  body: ⟨(1 : Real)⟩

@[simp]

中文:
实例 :
  签名: 幺 复形
  定义体: ⟨(1 : Real)⟩

@[simp]
-/
instance : One Complex :=
  ⟨(1 : Real)⟩

@[simp]
/--
theorem `one_re` / 定理 `one_re`

English:
theorem one_re
  statement: (1 : Complex).re = 1
  proof: rfl

@[simp]

中文:
定理 one_re
  结论: (1 : 复形).re = 1
  证明: rfl

@[simp]
-/
theorem one_re : (1 : Complex).re = 1 :=
  rfl

@[simp]
/--
theorem `one_im` / 定理 `one_im`

English:
theorem one_im
  statement: (1 : Complex).im = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 one_im
  结论: (1 : 复形).im = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem one_im : (1 : Complex).im = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_one` / 定理 `ofReal_one`

English:
theorem ofReal_one
  statement: ((1 : Real) : Complex) = 1
  proof: rfl

@[simp]

中文:
定理 of实数_one
  结论: ((1 : 实数) : 复形) = 1
  证明: rfl

@[simp]
-/
theorem ofReal_one : ((1 : Real) : Complex) = 1 :=
  rfl

@[simp]
/--
theorem `ofReal_eq_one` / 定理 `ofReal_eq_one`

English:
theorem ofReal_eq_one
  given: {z : Real}
  statement: (z : Complex) = 1 ↔ z = 1
  proof: ofReal_inj

中文:
定理 of实数_eq_one
  条件: {z : 实数}
  结论: (z : 复形) = 1 ↔ z = 1
  证明: ofReal_inj

Depends on / 依赖: ofReal_inj
-/
theorem ofReal_eq_one {z : Real} : (z : Complex) = 1 ↔ z = 1 :=
  ofReal_inj

/--
theorem `ofReal_ne_one` / 定理 `ofReal_ne_one`

English:
theorem ofReal_ne_one
  given: {z : Real}
  statement: (z : Complex) != 1 ↔ z != 1
  proof: not_congr ofReal_eq_one

中文:
定理 of实数_ne_one
  条件: {z : 实数}
  结论: (z : 复形) != 1 ↔ z != 1
  证明: not_congr ofReal_eq_one

Depends on / 依赖: not_congr, ofReal_eq_one
-/
theorem ofReal_ne_one {z : Real} : (z : Complex) != 1 ↔ z != 1 :=
  not_congr ofReal_eq_one

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add Complex
  body: ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]

中文:
实例 :
  签名: 加法 复形
  定义体: ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
instance : Add Complex :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
/--
theorem `add_re` / 定理 `add_re`

English:
theorem add_re
  given: (z w : Complex)
  statement: (z + w).re = z.re + w.re
  proof: rfl

@[simp]

中文:
定理 add_re
  条件: (z w : 复形)
  结论: (z + w).re = z.re + w.re
  证明: rfl

@[simp]
-/
theorem add_re (z w : Complex) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
/--
theorem `add_im` / 定理 `add_im`

English:
theorem add_im
  given: (z w : Complex)
  statement: (z + w).im = z.im + w.im
  proof: rfl

@[simp, norm_cast]

中文:
定理 add_im
  条件: (z w : 复形)
  结论: (z + w).im = z.im + w.im
  证明: rfl

@[simp, norm_cast]
-/
theorem add_im (z w : Complex) : (z + w).im = z.im + w.im :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_add` / 定理 `ofReal_add`

English:
theorem ofReal_add
  given: (r s : Real)
  statement: ((r + s : Real) : Complex) = r + s
  proof: Complex.ext_iff.2 by simp [ofReal]

中文:
定理 of实数_add
  条件: (r s : 实数)
  结论: ((r + s : 实数) : 复形) = r + s
  证明: Complex.ext_iff.2 by simp [ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem ofReal_add (r s : Real) : ((r + s : Real) : Complex) = r + s :=
Complex.ext_iff.2 by simp [ofReal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg Complex
  body: ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]

中文:
实例 :
  签名: 取负 复形
  定义体: ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]

Depends on / 依赖: Nat.add_mod_right, Nat.add_sub_assoc, Nat.mod_eq_of_lt, Nat.sub_add_comm, add_mod_right, add_sub_assoc, all_goals, mod_eq_of_lt, prev_eq_getElem_idxOf_pred_of_ne_head, sub_add_comm, z.im, z.re
-/
instance : Neg Complex :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
/--
theorem `neg_re` / 定理 `neg_re`

English:
theorem neg_re
  given: (z : Complex)
  statement: (-z).re = -z.re
  proof: rfl

@[simp]

中文:
定理 neg_re
  条件: (z : 复形)
  结论: (-z).re = -z.re
  证明: rfl

@[simp]
-/
theorem neg_re (z : Complex) : (-z).re = -z.re :=
  rfl

@[simp]
/--
theorem `neg_im` / 定理 `neg_im`

English:
theorem neg_im
  given: (z : Complex)
  statement: (-z).im = -z.im
  proof: rfl

@[simp, norm_cast]

中文:
定理 neg_im
  条件: (z : 复形)
  结论: (-z).im = -z.im
  证明: rfl

@[simp, norm_cast]
-/
theorem neg_im (z : Complex) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_neg` / 定理 `ofReal_neg`

English:
theorem ofReal_neg
  given: (r : Real)
  statement: ((-r : Real) : Complex) = -r
  proof: Complex.ext_iff.2 by simp [ofReal]

中文:
定理 of实数_neg
  条件: (r : 实数)
  结论: ((-r : 实数) : 复形) = -r
  证明: Complex.ext_iff.2 by simp [ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r :=
Complex.ext_iff.2 by simp [ofReal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub Complex
  body: ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

中文:
实例 :
  签名: 减法 复形
  定义体: ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
instance : Sub Complex :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/--
`mulAux` is an auxiliary definition for defining multiplication and scalar multiplication on `ℂ`
in such a way that `real_smul {x : ℝ} {z : ℂ} : x • z = x * z` holds definitionally.
This makes sure that `Module.restrictScalars ℝ ℂ ℂ = Complex.instModule` definitionally.
-/
@[no_expose]
/--
Definition of `mulAux` / `mulAux` 的定义

English:
definition mulAux
  signature: {R : Type*} [SMul R Real] (re : R) (im : Real) (z : Complex)
  body: ⟨re • z.re - im * z.im, re • z.im + im * z.re⟩

中文:
定义 mulAux
  签名: {R : 类型} [标量乘法 R 实数] (re : R) (im : 实数) (z : 复形)
  定义体: ⟨re • z.re - im * z.im, re • z.im + im * z.re⟩

Depends on / 依赖: z.im, z.re
-/
def mulAux {R : Type*} [SMul R Real] (re : R) (im : Real) (z : Complex) : Complex :=
  ⟨re • z.re - im * z.im, re • z.im + im * z.re⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul Complex
  body: ⟨fun z w => mulAux z.re z.im w⟩

中文:
实例 :
  签名: 乘法 复形
  定义体: ⟨fun z w => mulAux z.re z.im w⟩

Depends on / 依赖: mulAux, z.im, z.re
-/
instance : Mul Complex :=
  ⟨fun z w => mulAux z.re z.im w⟩

/--
theorem `mk_mul_mk` / 定理 `mk_mul_mk`

English:
theorem mk_mul_mk
  given: (x₁ x₂ y₁ y₂ : Real)
  proof: (rfl)

@[simp]

中文:
定理 mk_mul_mk
  条件: (x₁ x₂ y₁ y₂ : 实数)
  证明: (rfl)

@[simp]
-/
theorem mk_mul_mk (x₁ x₂ y₁ y₂ : Real) :
    (⟨x₁, y₁⟩ : Complex) * ⟨x₂, y₂⟩ = ⟨x₁ * x₂ - y₁ * y₂, x₁ * y₂ + y₁ * x₂⟩ := (rfl)

@[simp]
/--
theorem `mul_re` / 定理 `mul_re`

English:
theorem mul_re
  given: (z w : Complex)
  statement: (z * w).re = z.re * w.re - z.im * w.im
  proof: (rfl)

@[simp]

中文:
定理 mul_re
  条件: (z w : 复形)
  结论: (z * w).re = z.re * w.re - z.im * w.im
  证明: (rfl)

@[simp]
-/
theorem mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im * w.im :=
  (rfl)

@[simp]
/--
theorem `mul_im` / 定理 `mul_im`

English:
theorem mul_im
  given: (z w : Complex)
  statement: (z * w).im = z.re * w.im + z.im * w.re
  proof: (rfl)

@[simp, norm_cast]

中文:
定理 mul_im
  条件: (z w : 复形)
  结论: (z * w).im = z.re * w.im + z.im * w.re
  证明: (rfl)

@[simp, norm_cast]
-/
theorem mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im * w.re :=
  (rfl)

@[simp, norm_cast]
/--
theorem `ofReal_mul` / 定理 `ofReal_mul`

English:
theorem ofReal_mul
  given: (r s : Real)
  statement: ((r * s : Real) : Complex) = r * s
  proof: Complex.ext_iff.2 by simp [ofReal]

中文:
定理 of实数_mul
  条件: (r s : 实数)
  结论: ((r * s : 实数) : 复形) = r * s
  证明: Complex.ext_iff.2 by simp [ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem ofReal_mul (r s : Real) : ((r * s : Real) : Complex) = r * s :=
Complex.ext_iff.2 by simp [ofReal]

/--
theorem `re_ofReal_mul` / 定理 `re_ofReal_mul`

English:
theorem re_ofReal_mul
  given: (r : Real) (z : Complex)
  statement: (r * z).re = r * z.re
  proof: by simp [ofReal]

中文:
定理 re_of实数_mul
  条件: (r : 实数) (z : 复形)
  结论: (r * z).re = r * z.re
  证明: by simp [ofReal]

Depends on / 依赖: ofReal
-/
theorem re_ofReal_mul (r : Real) (z : Complex) : (r * z).re = r * z.re := by simp [ofReal]

/--
theorem `im_ofReal_mul` / 定理 `im_ofReal_mul`

English:
theorem im_ofReal_mul
  given: (r : Real) (z : Complex)
  statement: (r * z).im = r * z.im
  proof: by simp [ofReal]

中文:
定理 im_of实数_mul
  条件: (r : 实数) (z : 复形)
  结论: (r * z).im = r * z.im
  证明: by simp [ofReal]

Depends on / 依赖: ofReal
-/
theorem im_ofReal_mul (r : Real) (z : Complex) : (r * z).im = r * z.im := by simp [ofReal]

/--
lemma `re_mul_ofReal` / 引理 `re_mul_ofReal`

English:
lemma re_mul_ofReal
  given: (z : Complex) (r : Real)
  statement: (z * r).re = z.re * r
  proof: by simp [ofReal]

中文:
引理 re_mul_of实数
  条件: (z : 复形) (r : 实数)
  结论: (z * r).re = z.re * r
  证明: by simp [ofReal]

Depends on / 依赖: ofReal
-/
lemma re_mul_ofReal (z : Complex) (r : Real) : (z * r).re = z.re * r := by simp [ofReal]
/--
lemma `im_mul_ofReal` / 引理 `im_mul_ofReal`

English:
lemma im_mul_ofReal
  given: (z : Complex) (r : Real)
  statement: (z * r).im = z.im * r
  proof: by simp [ofReal]

中文:
引理 im_mul_of实数
  条件: (z : 复形) (r : 实数)
  结论: (z * r).im = z.im * r
  证明: by simp [ofReal]

Depends on / 依赖: ofReal
-/
lemma im_mul_ofReal (z : Complex) (r : Real) : (z * r).im = z.im * r := by simp [ofReal]

/--
theorem `ofReal_mul'` / 定理 `ofReal_mul'`

English:
theorem ofReal_mul'
  given: (r : Real) (z : Complex)
  statement: ↑r * z = ⟨r * z.re, r * z.im⟩
  proof: ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

中文:
定理 of实数_mul'
  条件: (r : 实数) (z : 复形)
  结论: ↑r * z = ⟨r * z.re, r * z.im⟩
  证明: ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

Depends on / 依赖: im_ofReal_mul, re_ofReal_mul
-/
theorem ofReal_mul' (r : Real) (z : Complex) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

/-! ### The imaginary unit, `I` -/


/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : Complex
  body: ⟨0, 1⟩

@[simp]

中文:
定义 I
  签名: : 复形
  定义体: ⟨0, 1⟩

@[simp]
-/
def I : Complex :=
  ⟨0, 1⟩

@[simp]
/--
theorem `I_re` / 定理 `I_re`

English:
theorem I_re
  statement: I.re = 0
  proof: rfl

@[simp]

中文:
定理 I_re
  结论: I.re = 0
  证明: rfl

@[simp]
-/
theorem I_re : I.re = 0 :=
  rfl

@[simp]
/--
theorem `I_im` / 定理 `I_im`

English:
theorem I_im
  statement: I.im = 1
  proof: rfl

@[simp]

中文:
定理 I_im
  结论: I.im = 1
  证明: rfl

@[simp]
-/
theorem I_im : I.im = 1 :=
  rfl

@[simp]
/--
theorem `I_mul_I` / 定理 `I_mul_I`

English:
theorem I_mul_I
  statement: I * I = -1
  proof: Complex.ext_iff.2 by simp

中文:
定理 I_mul_I
  结论: I * I = -1
  证明: Complex.ext_iff.2 by simp

Depends on / 依赖: Complex.ext_iff, ext_iff
-/
theorem I_mul_I : I * I = -1 :=
Complex.ext_iff.2 by simp

/--
theorem `I_mul` / 定理 `I_mul`

English:
theorem I_mul
  given: (z : Complex)
  statement: I * z = ⟨-z.im, z.re⟩
  proof: Complex.ext_iff.2 by simp

中文:
定理 I_mul
  条件: (z : 复形)
  结论: I * z = ⟨-z.im, z.re⟩
  证明: Complex.ext_iff.2 by simp

Depends on / 依赖: Complex.ext_iff, ext_iff
-/
theorem I_mul (z : Complex) : I * z = ⟨-z.im, z.re⟩ :=
Complex.ext_iff.2 by simp

/--
lemma `I_ne_zero` / 引理 `I_ne_zero`

English:
lemma I_ne_zero
  statement: (I : Complex) != 0
  proof: mt (congr_arg im) zero_ne_one.symm

中文:
引理 I_ne_zero
  结论: (I : 复形) != 0
  证明: mt (congr_arg im) zero_ne_one.symm
-/
@[simp] lemma I_ne_zero : (I : Complex) != 0 := mt (congr_arg im) zero_ne_one.symm

/--
theorem `mk_eq_add_mul_I` / 定理 `mk_eq_add_mul_I`

English:
theorem mk_eq_add_mul_I
  given: (a b : Real)
  statement: Complex.mk a b = a + b * I
  proof: Complex.ext_iff.2 by simp [ofReal]

@[simp]

中文:
定理 mk_eq_add_mul_I
  条件: (a b : 实数)
  结论: 复形.mk a b = a + b * I
  证明: Complex.ext_iff.2 by simp [ofReal]

@[simp]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem mk_eq_add_mul_I (a b : Real) : Complex.mk a b = a + b * I :=
Complex.ext_iff.2 by simp [ofReal]

@[simp]
/--
theorem `re_add_im` / 定理 `re_add_im`

English:
theorem re_add_im
  given: (z : Complex)
  statement: (z.re : Complex) + z.im * I = z
  proof: Complex.ext_iff.2 by simp [ofReal]

中文:
定理 re_add_im
  条件: (z : 复形)
  结论: (z.re : 复形) + z.im * I = z
  证明: Complex.ext_iff.2 by simp [ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem re_add_im (z : Complex) : (z.re : Complex) + z.im * I = z :=
Complex.ext_iff.2 by simp [ofReal]

/--
theorem `mul_I_re` / 定理 `mul_I_re`

English:
theorem mul_I_re
  given: (z : Complex)
  statement: (z * I).re = -z.im
  proof: by simp

中文:
定理 mul_I_re
  条件: (z : 复形)
  结论: (z * I).re = -z.im
  证明: by simp
-/
theorem mul_I_re (z : Complex) : (z * I).re = -z.im := by simp

/--
theorem `mul_I_im` / 定理 `mul_I_im`

English:
theorem mul_I_im
  given: (z : Complex)
  statement: (z * I).im = z.re
  proof: by simp

中文:
定理 mul_I_im
  条件: (z : 复形)
  结论: (z * I).im = z.re
  证明: by simp
-/
theorem mul_I_im (z : Complex) : (z * I).im = z.re := by simp

/--
theorem `I_mul_re` / 定理 `I_mul_re`

English:
theorem I_mul_re
  given: (z : Complex)
  statement: (I * z).re = -z.im
  proof: by simp

中文:
定理 I_mul_re
  条件: (z : 复形)
  结论: (I * z).re = -z.im
  证明: by simp
-/
theorem I_mul_re (z : Complex) : (I * z).re = -z.im := by simp

/--
theorem `I_mul_im` / 定理 `I_mul_im`

English:
theorem I_mul_im
  given: (z : Complex)
  statement: (I * z).im = z.re
  proof: by simp

中文:
定理 I_mul_im
  条件: (z : 复形)
  结论: (I * z).im = z.re
  证明: by simp
-/
theorem I_mul_im (z : Complex) : (I * z).im = z.re := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `equivRealProd_symm_apply` / 定理 `equivRealProd_symm_apply`

English:
theorem equivRealProd_symm_apply
  given: (p : Real × Real)
  statement: equivRealProd.symm p = p.1 + p.2 * I
  proof: by
  ext <;> simp [Complex.equivRealProd, ofReal]

中文:
定理 equiv实数Prod_symm_apply
  条件: (p : 实数 × 实数)
  结论: equiv实数Prod.symm p = p.1 + p.2 * I
  证明: by
  ext <;> simp [Complex.equivRealProd, ofReal]

Depends on / 依赖: Complex.equivRealProd, equivRealProd, ofReal
-/
theorem equivRealProd_symm_apply (p : Real × Real) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal]

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
/--
Definition of `equivRealProdAddHom` / `equivRealProdAddHom` 的定义

English:
definition equivRealProdAddHom
  signature: : Complex ≃+ Real × Real
  body: { equivRealProd with map_add' := by simp }

中文:
定义 equiv实数ProdAddHom
  签名: : 复形 ≃+ 实数 × 实数
  定义体: { equivRealProd with map_add' := by simp }

Depends on / 依赖: equivRealProd, map_add
-/
def equivRealProdAddHom : Complex ≃+ Real × Real :=
  { equivRealProd with map_add' := by simp }

/--
theorem `equivRealProdAddHom_symm_apply` / 定理 `equivRealProdAddHom_symm_apply`

English:
theorem equivRealProdAddHom_symm_apply
  given: (p : Real × Real)
  proof: equivRealProd_symm_apply p

中文:
定理 equiv实数ProdAddHom_symm_apply
  条件: (p : 实数 × 实数)
  证明: equivRealProd_symm_apply p

Depends on / 依赖: equivRealProd_symm_apply
-/
theorem equivRealProdAddHom_symm_apply (p : Real × Real) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial Complex
  body: domain_nontrivial re rfl rfl

中文:
实例 :
  签名: 非平凡 复形
  定义体: domain_nontrivial re rfl rfl

Depends on / 依赖: domain_nontrivial
-/
instance : Nontrivial Complex :=
  domain_nontrivial re rfl rfl

namespace SMul

-- instance made scoped to avoid situations like instance synthesis
-- of `SMul ℂ ℂ` trying to proceed via `SMul ℂ ℝ`.
/-- Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Mathlib/LinearAlgebra/Complex/Module.lean` to transfer instances from `ℝ` to `ℂ`, but is not
needed outside, so we make it scoped. -/
scoped instance instSMulRealComplex {R : Type*} [SMul R Real] : SMul R Complex where
  smul r x := mulAux r 0 x

end SMul

open scoped Complex.SMul

section SMul

variable {R : Type*} [SMul R Real]

/--
theorem `smul_re` / 定理 `smul_re`

English:
theorem smul_re
  given: (r : R) (z : Complex)
  statement: (r • z).re = r • z.re
  proof: show r • z.re - 0 * z.im = r • z.re by simp

中文:
定理 smul_re
  条件: (r : R) (z : 复形)
  结论: (r • z).re = r • z.re
  证明: show r • z.re - 0 * z.im = r • z.re by simp

Depends on / 依赖: z.im, z.re
-/
theorem smul_re (r : R) (z : Complex) : (r • z).re = r • z.re :=
  show r • z.re - 0 * z.im = r • z.re by simp

/--
theorem `smul_im` / 定理 `smul_im`

English:
theorem smul_im
  given: (r : R) (z : Complex)
  statement: (r • z).im = r • z.im
  proof: show r • z.im + 0 * z.re = r • z.im by simp

@[simp]

中文:
定理 smul_im
  条件: (r : R) (z : 复形)
  结论: (r • z).im = r • z.im
  证明: show r • z.im + 0 * z.re = r • z.im by simp

@[simp]

Depends on / 依赖: z.im, z.re
-/
theorem smul_im (r : R) (z : Complex) : (r • z).im = r • z.im :=
  show r • z.im + 0 * z.re = r • z.im by simp

@[simp]
/--
theorem `real_smul` / 定理 `real_smul`

English:
theorem real_smul
  given: {x : Real} {z : Complex}
  statement: x • z = x * z
  proof: rfl

中文:
定理 real_smul
  条件: {x : 实数} {z : 复形}
  结论: x • z = x * z
  证明: rfl
-/
theorem real_smul {x : Real} {z : Complex} : x • z = x * z :=
  rfl

end SMul

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup Complex where
  body: by intros; ext <;> simp [smul_re, smul_im]
  nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp

中文:
实例 addCommGroup
  签名: : 加法交换群 复形 where
  定义体: by intros; ext <;> simp [smul_re, smul_im]
  nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp

Depends on / 依赖: add_assoc, add_comm, add_zero, intros, neg_add_cancel, nsmul_succ, nsmul_zero, smul_im, smul_re, zero_add, zsmul_neg, zsmul_succ
-/
instance addCommGroup : AddCommGroup Complex where
  zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp


/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast Complex where natCast n
  body: ofReal n

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 复形 where natCast n
  定义体: ofReal n

Depends on / 依赖: ofReal
-/
instance instNatCast : NatCast Complex where natCast n := ofReal n
/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast Complex where intCast n
  body: ofReal n

中文:
实例 inst整数Cast
  签名: : 整数嵌入 复形 where intCast n
  定义体: ofReal n

Depends on / 依赖: ofReal
-/
instance instIntCast : IntCast Complex where intCast n := ofReal n
/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast Complex where nnratCast q
  body: ofReal q

中文:
实例 instNNRatCast
  签名: : 非负有理数嵌入 复形 where nnratCast q
  定义体: ofReal q

Depends on / 依赖: ofReal
-/
instance instNNRatCast : NNRatCast Complex where nnratCast q := ofReal q
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: : RatCast Complex where ratCast q
  body: ofReal q

中文:
实例 instRatCast
  签名: : 有理数嵌入 复形 where ratCast q
  定义体: ofReal q

Depends on / 依赖: ofReal
-/
instance instRatCast : RatCast Complex where ratCast q := ofReal q

/--
lemma `ofReal_ofNat` / 引理 `ofReal_ofNat`

English:
lemma ofReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ofReal ofNat(n) = ofNat(n)
  proof: rfl

中文:
引理 of实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: of实数 of自然数(n) = of自然数(n)
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ofReal ofNat(n) = ofNat(n) := rfl
/--
lemma `ofReal_natCast` / 引理 `ofReal_natCast`

English:
lemma ofReal_natCast
  given: (n : Nat)
  statement: ofReal n = n
  proof: rfl

中文:
引理 of实数_natCast
  条件: (n : 自然数)
  结论: of实数 n = n
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_natCast (n : Nat) : ofReal n = n := rfl
/--
lemma `ofReal_intCast` / 引理 `ofReal_intCast`

English:
lemma ofReal_intCast
  given: (n : Int)
  statement: ofReal n = n
  proof: rfl

中文:
引理 of实数_intCast
  条件: (n : 整数)
  结论: of实数 n = n
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_intCast (n : Int) : ofReal n = n := rfl
/--
lemma `ofReal_nnratCast` / 引理 `ofReal_nnratCast`

English:
lemma ofReal_nnratCast
  given: (q : Rat>=0)
  statement: ofReal q = q
  proof: rfl

中文:
引理 of实数_nnratCast
  条件: (q : 有理数>=0)
  结论: of实数 q = q
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_nnratCast (q : Rat>=0) : ofReal q = q := rfl
/--
lemma `ofReal_ratCast` / 引理 `ofReal_ratCast`

English:
lemma ofReal_ratCast
  given: (q : Rat)
  statement: ofReal q = q
  proof: rfl

中文:
引理 of实数_ratCast
  条件: (q : 有理数)
  结论: of实数 q = q
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_ratCast (q : Rat) : ofReal q = q := rfl
/--
lemma `ofReal_ofScientific` / 引理 `ofReal_ofScientific`

English:
lemma ofReal_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

中文:
引理 of实数_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: rfl
-/
@[simp, norm_cast] lemma ofReal_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    ofReal (OfScientific.ofScientific m s e : Real) = OfScientific.ofScientific m s e := rfl

/--
lemma `re_ofNat` / 引理 `re_ofNat`

English:
lemma re_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : Complex).re = ofNat(n)
  proof: rfl

中文:
引理 re_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : 复形).re = of自然数(n)
  证明: rfl
-/
@[simp] lemma re_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Complex).re = ofNat(n) := rfl
/--
lemma `im_ofNat` / 引理 `im_ofNat`

English:
lemma im_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: (ofNat(n) : Complex).im = 0
  proof: rfl

中文:
引理 im_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (of自然数(n) : 复形).im = 0
  证明: rfl
-/
@[simp] lemma im_ofNat (n : Nat) [n.AtLeastTwo] : (ofNat(n) : Complex).im = 0 := rfl
/--
lemma `natCast_re` / 引理 `natCast_re`

English:
lemma natCast_re
  given: (n : Nat)
  statement: (n : Complex).re = n
  proof: rfl

中文:
引理 natCast_re
  条件: (n : 自然数)
  结论: (n : 复形).re = n
  证明: rfl
-/
@[simp, norm_cast] lemma natCast_re (n : Nat) : (n : Complex).re = n := rfl
/--
lemma `natCast_im` / 引理 `natCast_im`

English:
lemma natCast_im
  given: (n : Nat)
  statement: (n : Complex).im = 0
  proof: rfl

中文:
引理 natCast_im
  条件: (n : 自然数)
  结论: (n : 复形).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma natCast_im (n : Nat) : (n : Complex).im = 0 := rfl
/--
lemma `intCast_re` / 引理 `intCast_re`

English:
lemma intCast_re
  given: (n : Int)
  statement: (n : Complex).re = n
  proof: rfl

中文:
引理 intCast_re
  条件: (n : 整数)
  结论: (n : 复形).re = n
  证明: rfl
-/
@[simp, norm_cast] lemma intCast_re (n : Int) : (n : Complex).re = n := rfl
/--
lemma `intCast_im` / 引理 `intCast_im`

English:
lemma intCast_im
  given: (n : Int)
  statement: (n : Complex).im = 0
  proof: rfl

中文:
引理 intCast_im
  条件: (n : 整数)
  结论: (n : 复形).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma intCast_im (n : Int) : (n : Complex).im = 0 := rfl
/--
lemma `re_nnratCast` / 引理 `re_nnratCast`

English:
lemma re_nnratCast
  given: (q : Rat>=0)
  statement: (q : Complex).re = q
  proof: rfl

中文:
引理 re_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : 复形).re = q
  证明: rfl
-/
@[simp, norm_cast] lemma re_nnratCast (q : Rat>=0) : (q : Complex).re = q := rfl
/--
lemma `im_nnratCast` / 引理 `im_nnratCast`

English:
lemma im_nnratCast
  given: (q : Rat>=0)
  statement: (q : Complex).im = 0
  proof: rfl

中文:
引理 im_nnratCast
  条件: (q : 有理数>=0)
  结论: (q : 复形).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma im_nnratCast (q : Rat>=0) : (q : Complex).im = 0 := rfl
/--
lemma `ratCast_re` / 引理 `ratCast_re`

English:
lemma ratCast_re
  given: (q : Rat)
  statement: (q : Complex).re = q
  proof: rfl

中文:
引理 ratCast_re
  条件: (q : 有理数)
  结论: (q : 复形).re = q
  证明: rfl
-/
@[simp, norm_cast] lemma ratCast_re (q : Rat) : (q : Complex).re = q := rfl
/--
lemma `ratCast_im` / 引理 `ratCast_im`

English:
lemma ratCast_im
  given: (q : Rat)
  statement: (q : Complex).im = 0
  proof: rfl

中文:
引理 ratCast_im
  条件: (q : 有理数)
  结论: (q : 复形).im = 0
  证明: rfl
-/
@[simp, norm_cast] lemma ratCast_im (q : Rat) : (q : Complex).im = 0 := rfl
/--
lemma `re_ofScientific` / 引理 `re_ofScientific`

English:
lemma re_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

中文:
引理 re_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: rfl
-/
@[simp] lemma re_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Complex).re = OfScientific.ofScientific m s e := rfl
/--
lemma `im_ofScientific` / 引理 `im_ofScientific`

English:
lemma im_ofScientific
  given: (m : Nat) (s : Bool) (e : Nat)
  proof: rfl

中文:
引理 im_ofScientific
  条件: (m : 自然数) (s : 布尔值) (e : 自然数)
  证明: rfl
-/
@[simp] lemma im_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    (OfScientific.ofScientific m s e : Complex).im = 0 := rfl



/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: : AddGroupWithOne Complex
  body: { Complex.addCommGroup with
    natCast_zero := by ext <;> simp
    natCast_succ _ := by ext <;> simp
    intCast_ofNat _ := by ext <;> simp
    intCast_negSucc _ := by ext <;> simp }

中文:
实例 addGroupWithOne
  签名: : 加法带幺群 复形
  定义体: { Complex.addCommGroup with
    natCast_zero := by ext <;> simp
    natCast_succ _ := by ext <;> simp
    intCast_ofNat _ := by ext <;> simp
    intCast_negSucc _ := by ext <;> simp }

Depends on / 依赖: Complex.addCommGroup, addCommGroup, intCast_negSucc, intCast_ofNat, natCast_succ, natCast_zero
-/
instance addGroupWithOne : AddGroupWithOne Complex :=
  { Complex.addCommGroup with
    natCast_zero := by ext <;> simp
    natCast_succ _ := by ext <;> simp
    intCast_ofNat _ := by ext <;> simp
    intCast_negSucc _ := by ext <;> simp }

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing Complex
  body: { addGroupWithOne with
    npow := @npowRec _ ⟨(1 : Complex)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

中文:
实例 commRing
  签名: : 交换环 复形
  定义体: { addGroupWithOne with
    npow := @npowRec _ ⟨(1 : Complex)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

Depends on / 依赖: addGroupWithOne, add_comm, intros, left_distrib, mul_assoc, mul_comm, mul_im, mul_one, mul_re, mul_zero, npowRec, one_mul, right_distrib, zero_mul
-/
instance commRing : CommRing Complex :=
  { addGroupWithOne with
    npow := @npowRec _ ⟨(1 : Complex)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

section computable_shortcuts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring Complex
  body: delta% inferInstance

中文:
实例 :
  签名: 环 复形
  定义体: delta% inferInstance
-/
instance : Ring Complex :=
  delta% inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalCommRing Complex
  body: delta% inferInstance

中文:
实例 :
  签名: 非幺交换环 复形
  定义体: delta% inferInstance
-/
instance : NonUnitalCommRing Complex :=
  delta% inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring Complex
  body: delta% inferInstance

中文:
实例 :
  签名: 交换半环 复形
  定义体: delta% inferInstance
-/
instance : CommSemiring Complex :=
  delta% inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semiring Complex
  body: delta% inferInstance

中文:
实例 :
  签名: 半环 复形
  定义体: delta% inferInstance
-/
instance : Semiring Complex :=
  delta% inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid Complex
  body: delta% inferInstance

中文:
实例 :
  签名: 加法交换幺半群 复形
  定义体: delta% inferInstance
-/
instance : AddCommMonoid Complex :=
  delta% inferInstance

end computable_shortcuts

/--
Definition of `reAddGroupHom` / `reAddGroupHom` 的定义

English:
definition reAddGroupHom
  signature: : Complex ->+ Real where
  body: re
  map_zero' := zero_re
  map_add' := add_re

@[simp]

中文:
定义 reAddGroupHom
  签名: : 复形 ->+ 实数 where
  定义体: re
  map_zero' := zero_re
  map_add' := add_re

@[simp]

Depends on / 依赖: Quot.recOnSubsingleton, decidableNontrivialCoe, recOnSubsingleton
-/
def reAddGroupHom : Complex ->+ Real where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
/--
theorem `coe_reAddGroupHom` / 定理 `coe_reAddGroupHom`

English:
theorem coe_reAddGroupHom
  statement: (reAddGroupHom : Complex -> Real) = re
  proof: rfl

中文:
定理 coe_reAddGroupHom
  结论: (reAddGroupHom : 复形 -> 实数) = re
  证明: rfl

Depends on / 依赖: List.nodupDecidable, Quot.recOnSubsingleton, nodupDecidable, recOnSubsingleton
-/
theorem coe_reAddGroupHom : (reAddGroupHom : Complex -> Real) = re :=
  rfl

/--
Definition of `imAddGroupHom` / `imAddGroupHom` 的定义

English:
definition imAddGroupHom
  signature: : Complex ->+ Real where
  body: im
  map_zero' := zero_im
  map_add' := add_im

@[simp]

中文:
定义 imAddGroupHom
  签名: : 复形 ->+ 实数 where
  定义体: im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
-/
def imAddGroupHom : Complex ->+ Real where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
/--
theorem `coe_imAddGroupHom` / 定理 `coe_imAddGroupHom`

English:
theorem coe_imAddGroupHom
  statement: (imAddGroupHom : Complex -> Real) = im
  proof: rfl

中文:
定理 coe_imAddGroupHom
  结论: (imAddGroupHom : 复形 -> 实数) = im
  证明: rfl
-/
theorem coe_imAddGroupHom : (imAddGroupHom : Complex -> Real) = im :=
  rfl

/--
lemma `re_nsmul` / 引理 `re_nsmul`

English:
lemma re_nsmul
  given: (n : Nat) (z : Complex)
  statement: (n • z).re = n • z.re
  proof: smul_re ..

中文:
引理 re_nsmul
  条件: (n : 自然数) (z : 复形)
  结论: (n • z).re = n • z.re
  证明: smul_re ..

Depends on / 依赖: smul_re
-/
lemma re_nsmul (n : Nat) (z : Complex) : (n • z).re = n • z.re := smul_re ..
/--
lemma `im_nsmul` / 引理 `im_nsmul`

English:
lemma im_nsmul
  given: (n : Nat) (z : Complex)
  statement: (n • z).im = n • z.im
  proof: smul_im ..

中文:
引理 im_nsmul
  条件: (n : 自然数) (z : 复形)
  结论: (n • z).im = n • z.im
  证明: smul_im ..

Depends on / 依赖: smul_im
-/
lemma im_nsmul (n : Nat) (z : Complex) : (n • z).im = n • z.im := smul_im ..
/--
lemma `re_zsmul` / 引理 `re_zsmul`

English:
lemma re_zsmul
  given: (n : Int) (z : Complex)
  statement: (n • z).re = n • z.re
  proof: smul_re ..

中文:
引理 re_zsmul
  条件: (n : 整数) (z : 复形)
  结论: (n • z).re = n • z.re
  证明: smul_re ..

Depends on / 依赖: smul_re
-/
lemma re_zsmul (n : Int) (z : Complex) : (n • z).re = n • z.re := smul_re ..
/--
lemma `im_zsmul` / 引理 `im_zsmul`

English:
lemma im_zsmul
  given: (n : Int) (z : Complex)
  statement: (n • z).im = n • z.im
  proof: smul_im ..

中文:
引理 im_zsmul
  条件: (n : 整数) (z : 复形)
  结论: (n • z).im = n • z.im
  证明: smul_im ..

Depends on / 依赖: smul_im
-/
lemma im_zsmul (n : Int) (z : Complex) : (n • z).im = n • z.im := smul_im ..
/--
lemma `re_nnqsmul` / 引理 `re_nnqsmul`

English:
lemma re_nnqsmul
  given: (q : Rat>=0) (z : Complex)
  statement: (q • z).re = q • z.re
  proof: smul_re ..

中文:
引理 re_nnqsmul
  条件: (q : 有理数>=0) (z : 复形)
  结论: (q • z).re = q • z.re
  证明: smul_re ..
-/
@[simp] lemma re_nnqsmul (q : Rat>=0) (z : Complex) : (q • z).re = q • z.re := smul_re ..
/--
lemma `im_nnqsmul` / 引理 `im_nnqsmul`

English:
lemma im_nnqsmul
  given: (q : Rat>=0) (z : Complex)
  statement: (q • z).im = q • z.im
  proof: smul_im ..

中文:
引理 im_nnqsmul
  条件: (q : 有理数>=0) (z : 复形)
  结论: (q • z).im = q • z.im
  证明: smul_im ..
-/
@[simp] lemma im_nnqsmul (q : Rat>=0) (z : Complex) : (q • z).im = q • z.im := smul_im ..
/--
lemma `re_qsmul` / 引理 `re_qsmul`

English:
lemma re_qsmul
  given: (q : Rat) (z : Complex)
  statement: (q • z).re = q • z.re
  proof: smul_re ..

中文:
引理 re_qsmul
  条件: (q : 有理数) (z : 复形)
  结论: (q • z).re = q • z.re
  证明: smul_re ..
-/
@[simp] lemma re_qsmul (q : Rat) (z : Complex) : (q • z).re = q • z.re := smul_re ..
/--
lemma `im_qsmul` / 引理 `im_qsmul`

English:
lemma im_qsmul
  given: (q : Rat) (z : Complex)
  statement: (q • z).im = q • z.im
  proof: smul_im ..

中文:
引理 im_qsmul
  条件: (q : 有理数) (z : 复形)
  结论: (q • z).im = q • z.im
  证明: smul_im ..
-/
@[simp] lemma im_qsmul (q : Rat) (z : Complex) : (q • z).im = q • z.im := smul_im ..

/--
lemma `ofReal_nsmul` / 引理 `ofReal_nsmul`

English:
lemma ofReal_nsmul
  given: (n : Nat) (r : Real)
  statement: ↑(n • r) = n • (r : Complex)
  proof: by simp

中文:
引理 of实数_nsmul
  条件: (n : 自然数) (r : 实数)
  结论: ↑(n • r) = n • (r : 复形)
  证明: by simp
-/
@[norm_cast] lemma ofReal_nsmul (n : Nat) (r : Real) : ↑(n • r) = n • (r : Complex) := by simp

/--
lemma `ofReal_zsmul` / 引理 `ofReal_zsmul`

English:
lemma ofReal_zsmul
  given: (n : Int) (r : Real)
  statement: ↑(n • r) = n • (r : Complex)
  proof: by simp

中文:
引理 of实数_zsmul
  条件: (n : 整数) (r : 实数)
  结论: ↑(n • r) = n • (r : 复形)
  证明: by simp
-/
@[norm_cast] lemma ofReal_zsmul (n : Int) (r : Real) : ↑(n • r) = n • (r : Complex) := by simp

/-! ### Complex conjugation -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarRing Complex
  body: ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]

中文:
实例 :
  签名: 对合环 复形
  定义体: ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]

Depends on / 依赖: z.im, z.re
-/
instance : StarRing Complex where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
/--
theorem `conj_re` / 定理 `conj_re`

English:
theorem conj_re
  given: (z : Complex)
  statement: (conj z).re = z.re
  proof: rfl

@[simp]

中文:
定理 conj_re
  条件: (z : 复形)
  结论: (conj z).re = z.re
  证明: rfl

@[simp]
-/
theorem conj_re (z : Complex) : (conj z).re = z.re :=
  rfl

@[simp]
/--
theorem `conj_im` / 定理 `conj_im`

English:
theorem conj_im
  given: (z : Complex)
  statement: (conj z).im = -z.im
  proof: rfl

@[simp]

中文:
定理 conj_im
  条件: (z : 复形)
  结论: (conj z).im = -z.im
  证明: rfl

@[simp]
-/
theorem conj_im (z : Complex) : (conj z).im = -z.im :=
  rfl

@[simp]
/--
theorem `conj_ofReal` / 定理 `conj_ofReal`

English:
theorem conj_ofReal
  given: (r : Real)
  statement: conj (r : Complex) = r
  proof: Complex.ext_iff.2 by simp

@[simp]

中文:
定理 conj_of实数
  条件: (r : 实数)
  结论: conj (r : 复形) = r
  证明: Complex.ext_iff.2 by simp

@[simp]

Depends on / 依赖: Complex.ext_iff, ext_iff
-/
theorem conj_ofReal (r : Real) : conj (r : Complex) = r :=
Complex.ext_iff.2 by simp

@[simp]
/--
theorem `conj_I` / 定理 `conj_I`

English:
theorem conj_I
  statement: conj I = -I
  proof: Complex.ext_iff.2 by simp

中文:
定理 conj_I
  结论: conj I = -I
  证明: Complex.ext_iff.2 by simp

Depends on / 依赖: Complex.ext_iff, ext_iff
-/
theorem conj_I : conj I = -I :=
Complex.ext_iff.2 by simp

/--
theorem `conj_natCast` / 定理 `conj_natCast`

English:
theorem conj_natCast
  given: (n : Nat)
  statement: conj (n : Complex) = n
  proof: map_natCast _ _

中文:
定理 conj_natCast
  条件: (n : 自然数)
  结论: conj (n : 复形) = n
  证明: map_natCast _ _

Depends on / 依赖: map_natCast
-/
theorem conj_natCast (n : Nat) : conj (n : Complex) = n := map_natCast _ _

/--
theorem `conj_ofNat` / 定理 `conj_ofNat`

English:
theorem conj_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: conj (ofNat(n) : Complex) = ofNat(n)
  proof: map_ofNat _ _

中文:
定理 conj_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: conj (of自然数(n) : 复形) = of自然数(n)
  证明: map_ofNat _ _

Depends on / 依赖: map_ofNat
-/
theorem conj_ofNat (n : Nat) [n.AtLeastTwo] : conj (ofNat(n) : Complex) = ofNat(n) :=
  map_ofNat _ _

/--
theorem `conj_neg_I` / 定理 `conj_neg_I`

English:
theorem conj_neg_I
  statement: conj (-I) = I
  proof: by simp

中文:
定理 conj_neg_I
  结论: conj (-I) = I
  证明: by simp
-/
theorem conj_neg_I : conj (-I) = I := by simp

/--
theorem `conj_eq_iff_real` / 定理 `conj_eq_iff_real`

English:
theorem conj_eq_iff_real
  given: {z : Complex}
  statement: conj z = z ↔ exists r : Real, z = r
  proof: ⟨fun h => ⟨z.re, ext rfl eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e]; rw [conj_ofReal]⟩

中文:
定理 conj_eq_iff_real
  条件: {z : 复形}
  结论: conj z = z ↔ 存在 r : 实数, z = r
  证明: ⟨fun h => ⟨z.re, ext rfl eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e]; rw [conj_ofReal]⟩

Depends on / 依赖: congr_arg, conj_ofReal, eq_zero_of_neg_eq, z.re
-/
theorem conj_eq_iff_real {z : Complex} : conj z = z ↔ exists r : Real, z = r :=
⟨fun h => ⟨z.re, ext rfl eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e]; rw [conj_ofReal]⟩

/--
theorem `conj_eq_iff_re` / 定理 `conj_eq_iff_re`

English:
theorem conj_eq_iff_re
  given: {z : Complex}
  statement: conj z = z ↔ (z.re : Complex) = z
  proof: conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

中文:
定理 conj_eq_iff_re
  条件: {z : 复形}
  结论: conj z = z ↔ (z.re : 复形) = z
  证明: conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

Depends on / 依赖: conj_eq_iff_real, conj_eq_iff_real.trans, h.symm, ofReal
-/
theorem conj_eq_iff_re {z : Complex} : conj z = z ↔ (z.re : Complex) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

/--
theorem `conj_eq_iff_im` / 定理 `conj_eq_iff_im`

English:
theorem conj_eq_iff_im
  given: {z : Complex}
  statement: conj z = z ↔ z.im = 0
  proof: ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]

中文:
定理 conj_eq_iff_im
  条件: {z : 复形}
  结论: conj z = z ↔ z.im = 0
  证明: ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]

Depends on / 依赖: add_self_eq_zero, add_self_eq_zero.mp, add_self_eq_zero.mpr, congr_arg, neg_eq_iff_add_eq_zero, neg_eq_iff_add_eq_zero.mp, neg_eq_iff_add_eq_zero.mpr
-/
theorem conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]
/--
theorem `star_def` / 定理 `star_def`

English:
theorem star_def
  statement: (Star.star : Complex -> Complex) = conj
  proof: rfl

中文:
定理 star_def
  结论: (对合.star : 复形 -> 复形) = conj
  证明: rfl
-/
theorem star_def : (Star.star : Complex -> Complex) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
/--
Definition of `normSq` / `normSq` 的定义

English:
definition normSq
  signature: : Complex ->*₀ Real where
  body: z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring

中文:
定义 normSq
  签名: : 复形 ->*₀ 实数 where
  定义体: z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring

Depends on / 依赖: z.im, z.re
-/
def normSq : Complex ->*₀ Real where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring

/--
theorem `normSq_apply` / 定理 `normSq_apply`

English:
theorem normSq_apply
  given: (z : Complex)
  statement: normSq z = z.re * z.re + z.im * z.im
  proof: rfl

@[simp]

中文:
定理 normSq_apply
  条件: (z : 复形)
  结论: normSq z = z.re * z.re + z.im * z.im
  证明: rfl

@[simp]
-/
theorem normSq_apply (z : Complex) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
/--
theorem `normSq_ofReal` / 定理 `normSq_ofReal`

English:
theorem normSq_ofReal
  given: (r : Real)
  statement: normSq r = r * r
  proof: by
  simp [normSq, ofReal]

@[simp]

中文:
定理 normSq_of实数
  条件: (r : 实数)
  结论: normSq r = r * r
  证明: by
  simp [normSq, ofReal]

@[simp]

Depends on / 依赖: normSq, ofReal
-/
theorem normSq_ofReal (r : Real) : normSq r = r * r := by
  simp [normSq, ofReal]

@[simp]
/--
theorem `normSq_natCast` / 定理 `normSq_natCast`

English:
theorem normSq_natCast
  given: (n : Nat)
  statement: normSq n = n * n
  proof: normSq_ofReal _

@[simp]

中文:
定理 normSq_natCast
  条件: (n : 自然数)
  结论: normSq n = n * n
  证明: normSq_ofReal _

@[simp]

Depends on / 依赖: normSq_ofReal
-/
theorem normSq_natCast (n : Nat) : normSq n = n * n := normSq_ofReal _

@[simp]
/--
theorem `normSq_intCast` / 定理 `normSq_intCast`

English:
theorem normSq_intCast
  given: (z : Int)
  statement: normSq z = z * z
  proof: normSq_ofReal _

@[simp]

中文:
定理 normSq_intCast
  条件: (z : 整数)
  结论: normSq z = z * z
  证明: normSq_ofReal _

@[simp]

Depends on / 依赖: normSq_ofReal
-/
theorem normSq_intCast (z : Int) : normSq z = z * z := normSq_ofReal _

@[simp]
/--
theorem `normSq_ratCast` / 定理 `normSq_ratCast`

English:
theorem normSq_ratCast
  given: (q : Rat)
  statement: normSq q = q * q
  proof: normSq_ofReal _

@[simp]

中文:
定理 normSq_ratCast
  条件: (q : 有理数)
  结论: normSq q = q * q
  证明: normSq_ofReal _

@[simp]

Depends on / 依赖: normSq_ofReal
-/
theorem normSq_ratCast (q : Rat) : normSq q = q * q := normSq_ofReal _

@[simp]
/--
theorem `normSq_ofNat` / 定理 `normSq_ofNat`

English:
theorem normSq_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: normSq_natCast _

@[simp]

中文:
定理 normSq_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: normSq_natCast _

@[simp]

Depends on / 依赖: normSq_natCast
-/
theorem normSq_ofNat (n : Nat) [n.AtLeastTwo] :
    normSq (ofNat(n) : Complex) = ofNat(n) * ofNat(n) :=
  normSq_natCast _

@[simp]
/--
theorem `normSq_mk` / 定理 `normSq_mk`

English:
theorem normSq_mk
  given: (x y : Real)
  statement: normSq ⟨x, y⟩ = x * x + y * y
  proof: rfl

中文:
定理 normSq_mk
  条件: (x y : 实数)
  结论: normSq ⟨x, y⟩ = x * x + y * y
  证明: rfl
-/
theorem normSq_mk (x y : Real) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

/--
theorem `normSq_add_mul_I` / 定理 `normSq_add_mul_I`

English:
theorem normSq_add_mul_I
  given: (x y : Real)
  statement: normSq (x + y * I) = x ^ 2 + y ^ 2
  proof: by
  rw [← mk_eq_add_mul_I]; rw [normSq_mk]; rw [sq]; rw [sq]

中文:
定理 normSq_add_mul_I
  条件: (x y : 实数)
  结论: normSq (x + y * I) = x ^ 2 + y ^ 2
  证明: by
  rw [← mk_eq_add_mul_I]; rw [normSq_mk]; rw [sq]; rw [sq]

Depends on / 依赖: mk_eq_add_mul_I, normSq_mk
-/
theorem normSq_add_mul_I (x y : Real) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I]; rw [normSq_mk]; rw [sq]; rw [sq]

/--
theorem `normSq_eq_conj_mul_self` / 定理 `normSq_eq_conj_mul_self`

English:
theorem normSq_eq_conj_mul_self
  given: {z : Complex}
  statement: (normSq z : Complex) = conj z * z
  proof: by
  ext <;> simp [normSq, mul_comm, ofReal]

中文:
定理 normSq_eq_conj_mul_self
  条件: {z : 复形}
  结论: (normSq z : 复形) = conj z * z
  证明: by
  ext <;> simp [normSq, mul_comm, ofReal]

Depends on / 依赖: mul_comm, normSq, ofReal
-/
theorem normSq_eq_conj_mul_self {z : Complex} : (normSq z : Complex) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal]

/--
theorem `normSq_zero` / 定理 `normSq_zero`

English:
theorem normSq_zero
  statement: normSq 0 = 0
  proof: by simp

中文:
定理 normSq_zero
  结论: normSq 0 = 0
  证明: by simp
-/
theorem normSq_zero : normSq 0 = 0 := by simp

/--
theorem `normSq_one` / 定理 `normSq_one`

English:
theorem normSq_one
  statement: normSq 1 = 1
  proof: by simp

@[simp]

中文:
定理 normSq_one
  结论: normSq 1 = 1
  证明: by simp

@[simp]
-/
theorem normSq_one : normSq 1 = 1 := by simp

@[simp]
/--
theorem `normSq_I` / 定理 `normSq_I`

English:
theorem normSq_I
  statement: normSq I = 1
  proof: by simp [normSq]

中文:
定理 normSq_I
  结论: normSq I = 1
  证明: by simp [normSq]

Depends on / 依赖: normSq
-/
theorem normSq_I : normSq I = 1 := by simp [normSq]

/--
theorem `normSq_nonneg` / 定理 `normSq_nonneg`

English:
theorem normSq_nonneg
  given: (z : Complex)
  statement: 0 <= normSq z
  proof: add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

中文:
定理 normSq_nonneg
  条件: (z : 复形)
  结论: 0 <= normSq z
  证明: add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

Depends on / 依赖: add_nonneg, mul_self_nonneg
-/
theorem normSq_nonneg (z : Complex) : 0 <= normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/--
theorem `normSq_eq_zero` / 定理 `normSq_eq_zero`

English:
theorem normSq_eq_zero
  given: {z : Complex}
  statement: normSq z = 0 ↔ z = 0
  proof: ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]

中文:
定理 normSq_eq_zero
  条件: {z : 复形}
  结论: normSq z = 0 ↔ z = 0
  证明: ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]

Depends on / 依赖: add_comm, eq_zero_of_mul_self_add_mul_self_eq_zero, h.symm, normSq_zero
-/
theorem normSq_eq_zero {z : Complex} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
/--
theorem `normSq_pos` / 定理 `normSq_pos`

English:
theorem normSq_pos
  given: {z : Complex}
  statement: 0 < normSq z ↔ z != 0
  proof: (normSq_nonneg z).lt_iff_ne.trans not_congr (eq_comm.trans normSq_eq_zero)

@[simp]

中文:
定理 normSq_pos
  条件: {z : 复形}
  结论: 0 < normSq z ↔ z != 0
  证明: (normSq_nonneg z).lt_iff_ne.trans not_congr (eq_comm.trans normSq_eq_zero)

@[simp]

Depends on / 依赖: eq_comm, eq_comm.trans, lt_iff_ne, lt_iff_ne.trans, normSq_eq_zero, normSq_nonneg, not_congr
-/
theorem normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0 :=
(normSq_nonneg z).lt_iff_ne.trans not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
/--
theorem `normSq_neg` / 定理 `normSq_neg`

English:
theorem normSq_neg
  given: (z : Complex)
  statement: normSq (-z) = normSq z
  proof: by simp [normSq]

@[simp]

中文:
定理 normSq_neg
  条件: (z : 复形)
  结论: normSq (-z) = normSq z
  证明: by simp [normSq]

@[simp]

Depends on / 依赖: normSq
-/
theorem normSq_neg (z : Complex) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
/--
theorem `normSq_conj` / 定理 `normSq_conj`

English:
theorem normSq_conj
  given: (z : Complex)
  statement: normSq (conj z) = normSq z
  proof: by simp [normSq]

中文:
定理 normSq_conj
  条件: (z : 复形)
  结论: normSq (conj z) = normSq z
  证明: by simp [normSq]

Depends on / 依赖: normSq
-/
theorem normSq_conj (z : Complex) : normSq (conj z) = normSq z := by simp [normSq]

/--
theorem `normSq_mul` / 定理 `normSq_mul`

English:
theorem normSq_mul
  given: (z w : Complex)
  statement: normSq (z * w) = normSq z * normSq w
  proof: normSq.map_mul z w

中文:
定理 normSq_mul
  条件: (z w : 复形)
  结论: normSq (z * w) = normSq z * normSq w
  证明: normSq.map_mul z w

Depends on / 依赖: map_mul, normSq, normSq.map_mul
-/
theorem normSq_mul (z w : Complex) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

/--
theorem `normSq_add` / 定理 `normSq_add`

English:
theorem normSq_add
  given: (z w : Complex)
  statement: normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re
  proof: by
  simp [normSq]; ring

中文:
定理 normSq_add
  条件: (z w : 复形)
  结论: normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re
  证明: by
  simp [normSq]; ring

Depends on / 依赖: normSq
-/
theorem normSq_add (z w : Complex) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  simp [normSq]; ring

/--
theorem `re_sq_le_normSq` / 定理 `re_sq_le_normSq`

English:
theorem re_sq_le_normSq
  given: (z : Complex)
  statement: z.re * z.re <= normSq z
  proof: le_add_of_nonneg_right (mul_self_nonneg _)

中文:
定理 re_sq_le_normSq
  条件: (z : 复形)
  结论: z.re * z.re <= normSq z
  证明: le_add_of_nonneg_right (mul_self_nonneg _)

Depends on / 依赖: le_add_of_nonneg_right, mul_self_nonneg
-/
theorem re_sq_le_normSq (z : Complex) : z.re * z.re <= normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

/--
theorem `im_sq_le_normSq` / 定理 `im_sq_le_normSq`

English:
theorem im_sq_le_normSq
  given: (z : Complex)
  statement: z.im * z.im <= normSq z
  proof: le_add_of_nonneg_left (mul_self_nonneg _)

中文:
定理 im_sq_le_normSq
  条件: (z : 复形)
  结论: z.im * z.im <= normSq z
  证明: le_add_of_nonneg_left (mul_self_nonneg _)

Depends on / 依赖: le_add_of_nonneg_left, mul_self_nonneg
-/
theorem im_sq_le_normSq (z : Complex) : z.im * z.im <= normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

/--
theorem `mul_conj` / 定理 `mul_conj`

English:
theorem mul_conj
  given: (z : Complex)
  statement: z * conj z = normSq z
  proof: Complex.ext_iff.2 by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

中文:
定理 mul_conj
  条件: (z : 复形)
  结论: z * conj z = normSq z
  证明: Complex.ext_iff.2 by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

Depends on / 依赖: Complex.ext_iff, add_comm, ext_iff, mul_comm, normSq, ofReal, sub_eq_neg_add
-/
theorem mul_conj (z : Complex) : z * conj z = normSq z :=
Complex.ext_iff.2 by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

/--
theorem `add_conj` / 定理 `add_conj`

English:
theorem add_conj
  given: (z : Complex)
  statement: z + conj z = (2 * z.re : Real)
  proof: Complex.ext_iff.2 by simp [two_mul, ofReal]

中文:
定理 add_conj
  条件: (z : 复形)
  结论: z + conj z = (2 * z.re : 实数)
  证明: Complex.ext_iff.2 by simp [two_mul, ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal, two_mul
-/
theorem add_conj (z : Complex) : z + conj z = (2 * z.re : Real) :=
Complex.ext_iff.2 by simp [two_mul, ofReal]

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
@[instance_reducible]
/--
Definition of `ofRealHom` / `ofRealHom` 的定义

English:
definition ofRealHom
  signature: : Real ->+* Complex where
  body: (x : Complex)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

中文:
定义 of实数Hom
  签名: : 实数 ->+* 复形 where
  定义体: (x : Complex)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add
-/
def ofRealHom : Real ->+* Complex where
  toFun x := (x : Complex)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

/--
lemma `ofRealHom_eq_coe` / 引理 `ofRealHom_eq_coe`

English:
lemma ofRealHom_eq_coe
  given: (r : Real)
  statement: ofRealHom r = r
  proof: rfl

中文:
引理 of实数Hom_eq_coe
  条件: (r : 实数)
  结论: of实数Hom r = r
  证明: rfl
-/
@[simp] lemma ofRealHom_eq_coe (r : Real) : ofRealHom r = r := rfl

variable {α : Type*}

/--
lemma `ofReal_comp_add` / 引理 `ofReal_comp_add`

English:
lemma ofReal_comp_add
  given: (f g : α -> Real)
  statement: ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g
  proof: map_comp_add ofRealHom ..

中文:
引理 of实数_comp_add
  条件: (f g : α -> 实数)
  结论: of实数 ∘ (f + g) = of实数 ∘ f + of实数 ∘ g
  证明: map_comp_add ofRealHom ..
-/
@[simp] lemma ofReal_comp_add (f g : α -> Real) : ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g :=
  map_comp_add ofRealHom ..

/--
lemma `ofReal_comp_sub` / 引理 `ofReal_comp_sub`

English:
lemma ofReal_comp_sub
  given: (f g : α -> Real)
  statement: ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g
  proof: map_comp_sub ofRealHom ..

中文:
引理 of实数_comp_sub
  条件: (f g : α -> 实数)
  结论: of实数 ∘ (f - g) = of实数 ∘ f - of实数 ∘ g
  证明: map_comp_sub ofRealHom ..
-/
@[simp] lemma ofReal_comp_sub (f g : α -> Real) : ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g :=
  map_comp_sub ofRealHom ..

/--
lemma `ofReal_comp_neg` / 引理 `ofReal_comp_neg`

English:
lemma ofReal_comp_neg
  given: (f : α -> Real)
  statement: ofReal ∘ (-f) = -(ofReal ∘ f)
  proof: map_comp_neg ofRealHom _

中文:
引理 of实数_comp_neg
  条件: (f : α -> 实数)
  结论: of实数 ∘ (-f) = -(of实数 ∘ f)
  证明: map_comp_neg ofRealHom _
-/
@[simp] lemma ofReal_comp_neg (f : α -> Real) : ofReal ∘ (-f) = -(ofReal ∘ f) :=
  map_comp_neg ofRealHom _

/--
lemma `ofReal_comp_nsmul` / 引理 `ofReal_comp_nsmul`

English:
lemma ofReal_comp_nsmul
  given: (n : Nat) (f : α -> Real)
  statement: ofReal ∘ (n • f) = n • (ofReal ∘ f)
  proof: map_comp_nsmul ofRealHom ..

中文:
引理 of实数_comp_nsmul
  条件: (n : 自然数) (f : α -> 实数)
  结论: of实数 ∘ (n • f) = n • (of实数 ∘ f)
  证明: map_comp_nsmul ofRealHom ..

Depends on / 依赖: map_comp_nsmul, ofRealHom
-/
lemma ofReal_comp_nsmul (n : Nat) (f : α -> Real) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_nsmul ofRealHom ..

/--
lemma `ofReal_comp_zsmul` / 引理 `ofReal_comp_zsmul`

English:
lemma ofReal_comp_zsmul
  given: (n : Int) (f : α -> Real)
  statement: ofReal ∘ (n • f) = n • (ofReal ∘ f)
  proof: map_comp_zsmul ofRealHom ..

中文:
引理 of实数_comp_zsmul
  条件: (n : 整数) (f : α -> 实数)
  结论: of实数 ∘ (n • f) = n • (of实数 ∘ f)
  证明: map_comp_zsmul ofRealHom ..

Depends on / 依赖: map_comp_zsmul, ofRealHom
-/
lemma ofReal_comp_zsmul (n : Int) (f : α -> Real) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_zsmul ofRealHom ..

/--
lemma `ofReal_comp_mul` / 引理 `ofReal_comp_mul`

English:
lemma ofReal_comp_mul
  given: (f g : α -> Real)
  statement: ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g
  proof: map_comp_mul ofRealHom ..

中文:
引理 of实数_comp_mul
  条件: (f g : α -> 实数)
  结论: of实数 ∘ (f * g) = of实数 ∘ f * of实数 ∘ g
  证明: map_comp_mul ofRealHom ..
-/
@[simp] lemma ofReal_comp_mul (f g : α -> Real) : ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g :=
  map_comp_mul ofRealHom ..

/--
lemma `ofReal_comp_pow` / 引理 `ofReal_comp_pow`

English:
lemma ofReal_comp_pow
  given: (f : α -> Real) (n : Nat)
  statement: ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n
  proof: map_comp_pow ofRealHom ..

@[simp]

中文:
引理 of实数_comp_pow
  条件: (f : α -> 实数) (n : 自然数)
  结论: of实数 ∘ (f ^ n) = (of实数 ∘ f) ^ n
  证明: map_comp_pow ofRealHom ..

@[simp]
-/
@[simp] lemma ofReal_comp_pow (f : α -> Real) (n : Nat) : ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n :=
  map_comp_pow ofRealHom ..

@[simp]
/--
theorem `I_sq` / 定理 `I_sq`

English:
theorem I_sq
  statement: I ^ 2 = -1
  proof: by rw [sq, I_mul_I]

@[simp]

中文:
定理 I_sq
  结论: I ^ 2 = -1
  证明: by rw [sq, I_mul_I]

@[simp]

Depends on / 依赖: I_mul_I
-/
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
/--
lemma `I_pow_three` / 引理 `I_pow_three`

English:
lemma I_pow_three
  statement: I ^ 3 = -I
  proof: by rw [pow_succ, I_sq, neg_one_mul]

@[simp]

中文:
引理 I_pow_three
  结论: I ^ 3 = -I
  证明: by rw [pow_succ, I_sq, neg_one_mul]

@[simp]

Depends on / 依赖: I_sq, neg_one_mul, pow_succ
-/
lemma I_pow_three : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]

@[simp]
/--
theorem `I_pow_four` / 定理 `I_pow_four`

English:
theorem I_pow_four
  statement: I ^ 4 = 1
  proof: by rw [(by simp : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

中文:
定理 I_pow_four
  结论: I ^ 4 = 1
  证明: by rw [(by simp : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

Depends on / 依赖: I_sq, neg_one_sq, pow_mul
-/
theorem I_pow_four : I ^ 4 = 1 := by rw [(by simp : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

/--
lemma `I_pow_eq_pow_mod` / 引理 `I_pow_eq_pow_mod`

English:
lemma I_pow_eq_pow_mod
  given: (n : Nat)
  statement: I ^ n = I ^ (n % 4)
  proof: by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

中文:
引理 I_pow_eq_pow_mod
  条件: (n : 自然数)
  结论: I ^ n = I ^ (n % 4)
  证明: by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

Depends on / 依赖: I_pow_four, Nat.div_add_mod, conv_lhs, div_add_mod, pow_add, pow_mul
-/
lemma I_pow_eq_pow_mod (n : Nat) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

open Qq in
/-- Reduce `Complex.I ^ n` to `Complex.I ^ (n % 4)` when `n` is a literal natural number at
least `4`. Combined with `Nat.reduceMod` this normalises every literal power of `I` to one of
`I ^ 0`, `I ^ 1`, `I ^ 2`, `I ^ 3`, which the existing `@[simp]` lemmas dispatch. -/
simproc I_pow_eq_pow_mod' (I ^ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(Complex), ~q(I ^ ($n : Nat)) => do
    let some n' := n.nat? | return .continue
    if n' < 4 then return .continue
    -- we don't reduce `n % 4`, further, since `Nat.reduceMod` will handle that
return .visit .mk q(I ^ ($n % 4)) .some q(I_pow_eq_pow_mod $n)
  | _, _, _ => return .continue

@[simp]
/--
theorem `sub_re` / 定理 `sub_re`

English:
theorem sub_re
  given: (z w : Complex)
  statement: (z - w).re = z.re - w.re
  proof: rfl

@[simp]

中文:
定理 sub_re
  条件: (z w : 复形)
  结论: (z - w).re = z.re - w.re
  证明: rfl

@[simp]
-/
theorem sub_re (z w : Complex) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
/--
theorem `sub_im` / 定理 `sub_im`

English:
theorem sub_im
  given: (z w : Complex)
  statement: (z - w).im = z.im - w.im
  proof: rfl

@[simp, norm_cast]

中文:
定理 sub_im
  条件: (z w : 复形)
  结论: (z - w).im = z.im - w.im
  证明: rfl

@[simp, norm_cast]
-/
theorem sub_im (z w : Complex) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
/--
theorem `ofReal_sub` / 定理 `ofReal_sub`

English:
theorem ofReal_sub
  given: (r s : Real)
  statement: ((r - s : Real) : Complex) = r - s
  proof: Complex.ext_iff.2 by simp [ofReal]

@[simp, norm_cast]

中文:
定理 of实数_sub
  条件: (r s : 实数)
  结论: ((r - s : 实数) : 复形) = r - s
  证明: Complex.ext_iff.2 by simp [ofReal]

@[simp, norm_cast]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem ofReal_sub (r s : Real) : ((r - s : Real) : Complex) = r - s :=
Complex.ext_iff.2 by simp [ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_pow` / 定理 `ofReal_pow`

English:
theorem ofReal_pow
  given: (r : Real) (n : Nat)
  statement: ((r ^ n : Real) : Complex) = (r : Complex) ^ n
  proof: by
  induction n <;> simp [*, ofReal_mul, pow_succ]

中文:
定理 of实数_pow
  条件: (r : 实数) (n : 自然数)
  结论: ((r ^ n : 实数) : 复形) = (r : 复形) ^ n
  证明: by
  induction n <;> simp [*, ofReal_mul, pow_succ]

Depends on / 依赖: ofReal_mul, pow_succ
-/
theorem ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : Complex) = (r : Complex) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]

/--
theorem `sub_conj` / 定理 `sub_conj`

English:
theorem sub_conj
  given: (z : Complex)
  statement: z - conj z = (2 * z.im : Real) * I
  proof: Complex.ext_iff.2 by simp [two_mul, sub_eq_add_neg, ofReal]

中文:
定理 sub_conj
  条件: (z : 复形)
  结论: z - conj z = (2 * z.im : 实数) * I
  证明: Complex.ext_iff.2 by simp [two_mul, sub_eq_add_neg, ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal, sub_eq_add_neg, two_mul
-/
theorem sub_conj (z : Complex) : z - conj z = (2 * z.im : Real) * I :=
Complex.ext_iff.2 by simp [two_mul, sub_eq_add_neg, ofReal]

/--
theorem `normSq_sub` / 定理 `normSq_sub`

English:
theorem normSq_sub
  given: (z w : Complex)
  statement: normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re
  proof: by
  rw [sub_eq_add_neg]; rw [normSq_add]
  simp only [map_neg, mul_neg, neg_re, normSq_neg]
  ring

中文:
定理 normSq_sub
  条件: (z w : 复形)
  结论: normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re
  证明: by
  rw [sub_eq_add_neg]; rw [normSq_add]
  simp only [map_neg, mul_neg, neg_re, normSq_neg]
  ring

Depends on / 依赖: map_neg, mul_neg, neg_re, normSq_add, normSq_neg, sub_eq_add_neg
-/
theorem normSq_sub (z w : Complex) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg]; rw [normSq_add]
  simp only [map_neg, mul_neg, neg_re, normSq_neg]
  ring

/-! ### Inversion -/


@[no_expose]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv Complex
  body: ⟨fun z => conj z * ((normSq z)⁻¹ : Real)⟩

中文:
实例 :
  签名: 取逆 复形
  定义体: ⟨fun z => conj z * ((normSq z)⁻¹ : Real)⟩

Depends on / 依赖: normSq
-/
noncomputable instance : Inv Complex :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : Real)⟩

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (z : Complex)
  statement: z⁻¹ = conj z * ((normSq z)⁻¹ : Real)
  proof: (rfl)

@[simp]

中文:
定理 inv_def
  条件: (z : 复形)
  结论: z⁻¹ = conj z * ((normSq z)⁻¹ : 实数)
  证明: (rfl)

@[simp]
-/
theorem inv_def (z : Complex) : z⁻¹ = conj z * ((normSq z)⁻¹ : Real) :=
  (rfl)

@[simp]
/--
theorem `inv_re` / 定理 `inv_re`

English:
theorem inv_re
  given: (z : Complex)
  statement: z⁻¹.re = z.re / normSq z
  proof: by simp [inv_def, division_def, ofReal]

@[simp]

中文:
定理 inv_re
  条件: (z : 复形)
  结论: z⁻¹.re = z.re / normSq z
  证明: by simp [inv_def, division_def, ofReal]

@[simp]

Depends on / 依赖: division_def, inv_def, ofReal
-/
theorem inv_re (z : Complex) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal]

@[simp]
/--
theorem `inv_im` / 定理 `inv_im`

English:
theorem inv_im
  given: (z : Complex)
  statement: z⁻¹.im = -z.im / normSq z
  proof: by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]

中文:
定理 inv_im
  条件: (z : 复形)
  结论: z⁻¹.im = -z.im / normSq z
  证明: by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]

Depends on / 依赖: division_def, inv_def, ofReal
-/
theorem inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]
/--
theorem `ofReal_inv` / 定理 `ofReal_inv`

English:
theorem ofReal_inv
  given: (r : Real)
  statement: ((r⁻¹ : Real) : Complex) = (r : Complex)⁻¹
  proof: Complex.ext_iff.2 by simp [ofReal]

中文:
定理 of实数_inv
  条件: (r : 实数)
  结论: ((r⁻¹ : 实数) : 复形) = (r : 复形)⁻¹
  证明: Complex.ext_iff.2 by simp [ofReal]

Depends on / 依赖: Complex.ext_iff, ext_iff, ofReal
-/
theorem ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (r : Complex)⁻¹ :=
Complex.ext_iff.2 by simp [ofReal]

/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0⁻¹ : Complex) = 0
  proof: by
  rw [← ofReal_zero]; rw [← ofReal_inv]; rw [inv_zero]

中文:
定理 inv_zero
  结论: (0⁻¹ : 复形) = 0
  证明: by
  rw [← ofReal_zero]; rw [← ofReal_inv]; rw [inv_zero]
-/
protected theorem inv_zero : (0⁻¹ : Complex) = 0 := by
  rw [← ofReal_zero]; rw [← ofReal_inv]; rw [inv_zero]

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: {z : Complex} (h : z != 0)
  statement: z * z⁻¹ = 1
  proof: by
  rw [inv_def]; rw [← mul_assoc]; rw [mul_conj]; rw [← ofReal_mul]; rw [mul_inv_cancel₀ (mt normSq_eq_zero.1 h)]; rw [ofReal_one]

中文:
定理 mul_inv_cancel
  条件: {z : 复形} (h : z != 0)
  结论: z * z⁻¹ = 1
  证明: by
  rw [inv_def]; rw [← mul_assoc]; rw [mul_conj]; rw [← ofReal_mul]; rw [mul_inv_cancel₀ (mt normSq_eq_zero.1 h)]; rw [ofReal_one]
-/
protected theorem mul_inv_cancel {z : Complex} (h : z != 0) : z * z⁻¹ = 1 := by
  rw [inv_def]; rw [← mul_assoc]; rw [mul_conj]; rw [← ofReal_mul]; rw [mul_inv_cancel₀ (mt normSq_eq_zero.1 h)]; rw [ofReal_one]

/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: : DivInvMonoid Complex where

中文:
实例 instDivInvMonoid
  签名: : 除逆幺半群 复形 where
-/
noncomputable instance instDivInvMonoid : DivInvMonoid Complex where

/--
lemma `div_re` / 引理 `div_re`

English:
lemma div_re
  given: (z w : Complex)
  statement: (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w
  proof: by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

中文:
引理 div_re
  条件: (z w : 复形)
  结论: (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w
  证明: by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

Depends on / 依赖: div_eq_mul_inv, mul_assoc, sub_eq_add_neg
-/
lemma div_re (z w : Complex) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

/--
lemma `div_im` / 引理 `div_im`

English:
lemma div_im
  given: (z w : Complex)
  statement: (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w
  proof: by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

中文:
引理 div_im
  条件: (z w : 复形)
  结论: (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w
  证明: by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

Depends on / 依赖: add_comm, div_eq_mul_inv, mul_assoc, sub_eq_add_neg
-/
lemma div_im (z w : Complex) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]


/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field Complex where
  body: @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
nnqsmul_def n z := Complex.ext_iff.2 by simp [NNRat.smul_def, smul_re, smul_im]
qsmul_def n z := Complex.ext_iff.2 by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]

中文:
实例 instField
  签名: : 域 复形 where
  定义体: @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
nnqsmul_def n z := Complex.ext_iff.2 by simp [NNRat.smul_def, smul_re, smul_im]
qsmul_def n z := Complex.ext_iff.2 by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]

Depends on / 依赖: Complex.mul_inv_cancel, mul_inv_cancel
-/
noncomputable instance instField : Field Complex where
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
nnqsmul_def n z := Complex.ext_iff.2 by simp [NNRat.smul_def, smul_re, smul_im]
qsmul_def n z := Complex.ext_iff.2 by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]
/--
lemma `ofReal_nnqsmul` / 引理 `ofReal_nnqsmul`

English:
lemma ofReal_nnqsmul
  given: (q : Rat>=0) (r : Real)
  statement: ofReal (q • r) = q • r
  proof: by simp [NNRat.smul_def]

@[simp, norm_cast]

中文:
引理 of实数_nnqsmul
  条件: (q : 有理数>=0) (r : 实数)
  结论: of实数 (q • r) = q • r
  证明: by simp [NNRat.smul_def]

@[simp, norm_cast]

Depends on / 依赖: NNRat.smul_def, destutter, if_pos, smul_def
-/
lemma ofReal_nnqsmul (q : Rat>=0) (r : Real) : ofReal (q • r) = q • r := by simp [NNRat.smul_def]

@[simp, norm_cast]
/--
lemma `ofReal_qsmul` / 引理 `ofReal_qsmul`

English:
lemma ofReal_qsmul
  given: (q : Rat) (r : Real)
  statement: ofReal (q • r) = q • r
  proof: by simp [Rat.smul_def]

中文:
引理 of实数_qsmul
  条件: (q : 有理数) (r : 实数)
  结论: of实数 (q • r) = q • r
  证明: by simp [Rat.smul_def]

Depends on / 依赖: Rat.smul_def, destutter, if_neg, smul_def
-/
lemma ofReal_qsmul (q : Rat) (r : Real) : ofReal (q • r) = q • r := by simp [Rat.smul_def]

/--
theorem `conj_inv` / 定理 `conj_inv`

English:
theorem conj_inv
  given: (x : Complex)
  statement: conj x⁻¹ = (conj x)⁻¹
  proof: star_inv₀ _

@[simp, norm_cast]

中文:
定理 conj_inv
  条件: (x : 复形)
  结论: conj x⁻¹ = (conj x)⁻¹
  证明: star_inv₀ _

@[simp, norm_cast]

Depends on / 依赖: split_ifs
-/
theorem conj_inv (x : Complex) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

@[simp, norm_cast]
/--
theorem `ofReal_div` / 定理 `ofReal_div`

English:
theorem ofReal_div
  given: (r s : Real)
  statement: ((r / s : Real) : Complex) = r / s
  proof: map_div₀ ofRealHom r s

@[simp, norm_cast]

中文:
定理 of实数_div
  条件: (r s : 实数)
  结论: ((r / s : 实数) : 复形) = r / s
  证明: map_div₀ ofRealHom r s

@[simp, norm_cast]

Depends on / 依赖: Sublist, Sublist.cons_cons, cons_cons, destutter, generalizing, l.sublist_cons_self, ofRealHom, split_ifs, sublist_cons_self
-/
theorem ofReal_div (r s : Real) : ((r / s : Real) : Complex) = r / s := map_div₀ ofRealHom r s

@[simp, norm_cast]
/--
theorem `ofReal_zpow` / 定理 `ofReal_zpow`

English:
theorem ofReal_zpow
  given: (r : Real) (n : Int)
  statement: ((r ^ n : Real) : Complex) = (r : Complex) ^ n
  proof: map_zpow₀ ofRealHom r n

@[simp]

中文:
定理 of实数_zpow
  条件: (r : 实数) (n : 整数)
  结论: ((r ^ n : 实数) : 复形) = (r : 复形) ^ n
  证明: map_zpow₀ ofRealHom r n

@[simp]

Depends on / 依赖: ofRealHom
-/
theorem ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) : Complex) = (r : Complex) ^ n := map_zpow₀ ofRealHom r n

@[simp]
/--
theorem `div_I` / 定理 `div_I`

English:
theorem div_I
  given: (z : Complex)
  statement: z / I = -(z * I)
  proof: (div_eq_iff_mul_eq I_ne_zero).2 by simp [mul_assoc]

@[simp]

中文:
定理 div_I
  条件: (z : 复形)
  结论: z / I = -(z * I)
  证明: (div_eq_iff_mul_eq I_ne_zero).2 by simp [mul_assoc]

@[simp]

Depends on / 依赖: I_ne_zero, div_eq_iff_mul_eq, mul_assoc
-/
theorem div_I (z : Complex) : z / I = -(z * I) :=
(div_eq_iff_mul_eq I_ne_zero).2 by simp [mul_assoc]

@[simp]
/--
theorem `inv_I` / 定理 `inv_I`

English:
theorem inv_I
  statement: I⁻¹ = -I
  proof: by
  rw [inv_eq_one_div]; rw [div_I]; rw [one_mul]

中文:
定理 inv_I
  结论: I⁻¹ = -I
  证明: by
  rw [inv_eq_one_div]; rw [div_I]; rw [one_mul]

Depends on / 依赖: div_I, inv_eq_one_div, one_mul
-/
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div]; rw [div_I]; rw [one_mul]

/--
lemma `I_zpow_eq_zpow_mod` / 引理 `I_zpow_eq_zpow_mod`

English:
lemma I_zpow_eq_zpow_mod
  given: (m : Int)
  statement: I ^ m = I ^ (m % 4)
  proof: by
  conv_lhs => rw [← Int.mul_ediv_add_emod m 4]
  simp [zpow_add₀, zpow_mul, zpow_ofNat]

中文:
引理 I_zpow_eq_zpow_mod
  条件: (m : 整数)
  结论: I ^ m = I ^ (m % 4)
  证明: by
  conv_lhs => rw [← Int.mul_ediv_add_emod m 4]
  simp [zpow_add₀, zpow_mul, zpow_ofNat]

Depends on / 依赖: Int.mul_ediv_add_emod, _cons_pos, conv_lhs, destutter, generalizing, isChain_cons_cons, isChain_cons_cons.mp, l.destutter, mul_ediv_add_emod, zpow_mul, zpow_ofNat
-/
lemma I_zpow_eq_zpow_mod (m : Int) : I ^ m = I ^ (m % 4) := by
  conv_lhs => rw [← Int.mul_ediv_add_emod m 4]
  simp [zpow_add₀, zpow_mul, zpow_ofNat]

/--
theorem `normSq_inv` / 定理 `normSq_inv`

English:
theorem normSq_inv
  given: (z : Complex)
  statement: normSq z⁻¹ = (normSq z)⁻¹
  proof: by simp

中文:
定理 normSq_inv
  条件: (z : 复形)
  结论: normSq z⁻¹ = (normSq z)⁻¹
  证明: by simp

Depends on / 依赖: _of_isChain_cons, destutter, isChain_destutter, l.isChain_destutter
-/
theorem normSq_inv (z : Complex) : normSq z⁻¹ = (normSq z)⁻¹ := by simp

/--
theorem `normSq_div` / 定理 `normSq_div`

English:
theorem normSq_div
  given: (z w : Complex)
  statement: normSq (z / w) = normSq z / normSq w
  proof: by simp

中文:
定理 normSq_div
  条件: (z w : 复形)
  结论: normSq (z / w) = normSq z / normSq w
  证明: by simp

Depends on / 依赖: l.mem_destutter, mem_destutter, ne_nil_of_mem
-/
theorem normSq_div (z w : Complex) : normSq (z / w) = normSq z / normSq w := by simp

/--
lemma `div_ofReal` / 引理 `div_ofReal`

English:
lemma div_ofReal
  given: (z : Complex) (x : Real)
  statement: z / x = ⟨z.re / x, z.im / x⟩
  proof: by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

中文:
引理 div_of实数
  条件: (z : 复形) (x : 实数)
  结论: z / x = ⟨z.re / x, z.im / x⟩
  证明: by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

Depends on / 依赖: div_eq_inv_mul, ofReal_inv, ofReal_mul, simp_rw
-/
lemma div_ofReal (z : Complex) (x : Real) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

/--
lemma `div_natCast` / 引理 `div_natCast`

English:
lemma div_natCast
  given: (z : Complex) (n : Nat)
  statement: z / n = ⟨z.re / n, z.im / n⟩
  proof: mod_cast div_ofReal z n

中文:
引理 div_natCast
  条件: (z : 复形) (n : 自然数)
  结论: z / n = ⟨z.re / n, z.im / n⟩
  证明: mod_cast div_ofReal z n

Depends on / 依赖: div_ofReal, mod_cast
-/
lemma div_natCast (z : Complex) (n : Nat) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

/--
lemma `div_intCast` / 引理 `div_intCast`

English:
lemma div_intCast
  given: (z : Complex) (n : Int)
  statement: z / n = ⟨z.re / n, z.im / n⟩
  proof: mod_cast div_ofReal z n

中文:
引理 div_intCast
  条件: (z : 复形) (n : 整数)
  结论: z / n = ⟨z.re / n, z.im / n⟩
  证明: mod_cast div_ofReal z n

Depends on / 依赖: div_ofReal, mod_cast
-/
lemma div_intCast (z : Complex) (n : Int) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

/--
lemma `div_ratCast` / 引理 `div_ratCast`

English:
lemma div_ratCast
  given: (z : Complex) (x : Rat)
  statement: z / x = ⟨z.re / x, z.im / x⟩
  proof: mod_cast div_ofReal z x

中文:
引理 div_ratCast
  条件: (z : 复形) (x : 有理数)
  结论: z / x = ⟨z.re / x, z.im / x⟩
  证明: mod_cast div_ofReal z x

Depends on / 依赖: div_ofReal, mod_cast
-/
lemma div_ratCast (z : Complex) (x : Rat) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofReal z x

/--
lemma `div_ofNat` / 引理 `div_ofNat`

English:
lemma div_ofNat
  given: (z : Complex) (n : Nat) [n.AtLeastTwo]
  proof: div_natCast z n

中文:
引理 div_of自然数
  条件: (z : 复形) (n : 自然数) [n.AtLeastTwo]
  证明: div_natCast z n

Depends on / 依赖: div_natCast
-/
lemma div_ofNat (z : Complex) (n : Nat) [n.AtLeastTwo] :
    z / ofNat(n) = ⟨z.re / ofNat(n), z.im / ofNat(n)⟩ :=
  div_natCast z n

/--
lemma `div_ofReal_re` / 引理 `div_ofReal_re`

English:
lemma div_ofReal_re
  given: (z : Complex) (x : Real)
  statement: (z / x).re = z.re / x
  proof: by rw [div_ofReal]

中文:
引理 div_of实数_re
  条件: (z : 复形) (x : 实数)
  结论: (z / x).re = z.re / x
  证明: by rw [div_ofReal]
-/
@[simp] lemma div_ofReal_re (z : Complex) (x : Real) : (z / x).re = z.re / x := by rw [div_ofReal]
/--
lemma `div_ofReal_im` / 引理 `div_ofReal_im`

English:
lemma div_ofReal_im
  given: (z : Complex) (x : Real)
  statement: (z / x).im = z.im / x
  proof: by rw [div_ofReal]

中文:
引理 div_of实数_im
  条件: (z : 复形) (x : 实数)
  结论: (z / x).im = z.im / x
  证明: by rw [div_ofReal]
-/
@[simp] lemma div_ofReal_im (z : Complex) (x : Real) : (z / x).im = z.im / x := by rw [div_ofReal]
/--
lemma `div_natCast_re` / 引理 `div_natCast_re`

English:
lemma div_natCast_re
  given: (z : Complex) (n : Nat)
  statement: (z / n).re = z.re / n
  proof: by rw [div_natCast]

中文:
引理 div_natCast_re
  条件: (z : 复形) (n : 自然数)
  结论: (z / n).re = z.re / n
  证明: by rw [div_natCast]
-/
@[simp] lemma div_natCast_re (z : Complex) (n : Nat) : (z / n).re = z.re / n := by rw [div_natCast]
/--
lemma `div_natCast_im` / 引理 `div_natCast_im`

English:
lemma div_natCast_im
  given: (z : Complex) (n : Nat)
  statement: (z / n).im = z.im / n
  proof: by rw [div_natCast]

中文:
引理 div_natCast_im
  条件: (z : 复形) (n : 自然数)
  结论: (z / n).im = z.im / n
  证明: by rw [div_natCast]
-/
@[simp] lemma div_natCast_im (z : Complex) (n : Nat) : (z / n).im = z.im / n := by rw [div_natCast]
/--
lemma `div_intCast_re` / 引理 `div_intCast_re`

English:
lemma div_intCast_re
  given: (z : Complex) (n : Int)
  statement: (z / n).re = z.re / n
  proof: by rw [div_intCast]

中文:
引理 div_intCast_re
  条件: (z : 复形) (n : 整数)
  结论: (z / n).re = z.re / n
  证明: by rw [div_intCast]

Depends on / 依赖: _cotrans_ge, antisymm, length_destutter
-/
@[simp] lemma div_intCast_re (z : Complex) (n : Int) : (z / n).re = z.re / n := by rw [div_intCast]
/--
lemma `div_intCast_im` / 引理 `div_intCast_im`

English:
lemma div_intCast_im
  given: (z : Complex) (n : Int)
  statement: (z / n).im = z.im / n
  proof: by rw [div_intCast]

中文:
引理 div_intCast_im
  条件: (z : 复形) (n : 整数)
  结论: (z / n).im = z.im / n
  证明: by rw [div_intCast]
-/
@[simp] lemma div_intCast_im (z : Complex) (n : Int) : (z / n).im = z.im / n := by rw [div_intCast]
/--
lemma `div_ratCast_re` / 引理 `div_ratCast_re`

English:
lemma div_ratCast_re
  given: (z : Complex) (x : Rat)
  statement: (z / x).re = z.re / x
  proof: by rw [div_ratCast]

中文:
引理 div_ratCast_re
  条件: (z : 复形) (x : 有理数)
  结论: (z / x).re = z.re / x
  证明: by rw [div_ratCast]
-/
@[simp] lemma div_ratCast_re (z : Complex) (x : Rat) : (z / x).re = z.re / x := by rw [div_ratCast]
/--
lemma `div_ratCast_im` / 引理 `div_ratCast_im`

English:
lemma div_ratCast_im
  given: (z : Complex) (x : Rat)
  statement: (z / x).im = z.im / x
  proof: by rw [div_ratCast]

@[simp]

中文:
引理 div_ratCast_im
  条件: (z : 复形) (x : 有理数)
  结论: (z / x).im = z.im / x
  证明: by rw [div_ratCast]

@[simp]
-/
@[simp] lemma div_ratCast_im (z : Complex) (x : Rat) : (z / x).im = z.im / x := by rw [div_ratCast]

@[simp]
/--
lemma `div_ofNat_re` / 引理 `div_ofNat_re`

English:
lemma div_ofNat_re
  given: (z : Complex) (n : Nat) [n.AtLeastTwo]
  proof: div_natCast_re z n

@[simp]

中文:
引理 div_of自然数_re
  条件: (z : 复形) (n : 自然数) [n.AtLeastTwo]
  证明: div_natCast_re z n

@[simp]

Depends on / 依赖: div_natCast_re
-/
lemma div_ofNat_re (z : Complex) (n : Nat) [n.AtLeastTwo] :
    (z / ofNat(n)).re = z.re / ofNat(n) := div_natCast_re z n

@[simp]
/--
lemma `div_ofNat_im` / 引理 `div_ofNat_im`

English:
lemma div_ofNat_im
  given: (z : Complex) (n : Nat) [n.AtLeastTwo]
  proof: div_natCast_im z n

中文:
引理 div_of自然数_im
  条件: (z : 复形) (n : 自然数) [n.AtLeastTwo]
  证明: div_natCast_im z n

Depends on / 依赖: div_natCast_im
-/
lemma div_ofNat_im (z : Complex) (n : Nat) [n.AtLeastTwo] :
    (z / ofNat(n)).im = z.im / ofNat(n) := div_natCast_im z n



/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Complex
  body: charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

中文:
实例 instCharZero
  签名: : 特征零 复形
  定义体: charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

Depends on / 依赖: Nat.cast_eq_zero, cast_eq_zero, charZero_of_inj_zero, ofReal_eq_zero, ofReal_natCast
-/
instance instCharZero : CharZero Complex :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

/--
Instance `instIsAddTorsionFree` / 实例 `instIsAddTorsionFree`

English:
instance instIsAddTorsionFree
  signature: : IsAddTorsionFree Complex
  body: IsDomain.instIsAddTorsionFreeOfCharZero _

中文:
实例 instIsAddTorsionFree
  签名: : 是加法无挠 复形
  定义体: IsDomain.instIsAddTorsionFreeOfCharZero _

Depends on / 依赖: IsDomain, IsDomain.instIsAddTorsionFreeOfCharZero, instIsAddTorsionFreeOfCharZero
-/
instance instIsAddTorsionFree : IsAddTorsionFree Complex := IsDomain.instIsAddTorsionFreeOfCharZero _

/--
theorem `re_eq_add_conj` / 定理 `re_eq_add_conj`

English:
theorem re_eq_add_conj
  given: (z : Complex)
  statement: (z.re : Complex) = (z + conj z) / 2
  proof: by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : Complex) two_ne_zero]

中文:
定理 re_eq_add_conj
  条件: (z : 复形)
  结论: (z.re : 复形) = (z + conj z) / 2
  证明: by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : Complex) two_ne_zero]

Depends on / 依赖: add_conj, ofReal_mul, ofReal_ofNat, two_ne_zero, z.re
-/
theorem re_eq_add_conj (z : Complex) : (z.re : Complex) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : Complex) two_ne_zero]

/--
theorem `im_eq_sub_conj` / 定理 `im_eq_sub_conj`

English:
theorem im_eq_sub_conj
  given: (z : Complex)
  statement: (z.im : Complex) = (z - conj z) / (2 * I)
  proof: by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I != 0)]

中文:
定理 im_eq_sub_conj
  条件: (z : 复形)
  结论: (z.im : 复形) = (z - conj z) / (2 * I)
  证明: by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I != 0)]

Depends on / 依赖: I_ne_zero, mul_ne_zero, mul_right_comm, ofReal_mul, ofReal_ofNat, sub_conj, two_ne_zero
-/
theorem im_eq_sub_conj (z : Complex) : (z.im : Complex) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I != 0)]

/-- Show the imaginary number ⟨x, y⟩ as an `"x + y*I"` string

Note that the Real numbers used for x and y will show as Cauchy sequences due to the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr Complex where
  reprPrec f p :=
(if p > 65 then (Std.Format.bracket "(" · ")") else (·))
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

section reProdIm

/--
lemma `preimage_equivRealProd_prod` / 引理 `preimage_equivRealProd_prod`

English:
lemma preimage_equivRealProd_prod
  given: (s t : Set Real)
  statement: equivRealProd ⁻¹' (s ×ˢ t) = s ×Complex t
  proof: rfl

中文:
引理 preimage_equiv实数Prod_prod
  条件: (s t : 集合 实数)
  结论: equiv实数Prod ⁻¹' (s ×ˢ t) = s ×复形 t
  证明: rfl
-/
lemma preimage_equivRealProd_prod (s t : Set Real) : equivRealProd ⁻¹' (s ×ˢ t) = s ×Complex t := rfl

/--
lemma `reProdIm_subset_iff` / 引理 `reProdIm_subset_iff`

English:
lemma reProdIm_subset_iff
  given: {s s₁ t t₁ : Set Real}
  statement: s ×Complex t subseteq s₁ ×Complex t₁ ↔ s ×ˢ t subseteq s₁ ×ˢ t₁
  proof: by
  rw [← @preimage_equivRealProd_prod s t]; rw [← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

中文:
引理 reProdIm_subset_iff
  条件: {s s₁ t t₁ : 集合 实数}
  结论: s ×复形 t subseteq s₁ ×复形 t₁ ↔ s ×ˢ t subseteq s₁ ×ˢ t₁
  证明: by
  rw [← @preimage_equivRealProd_prod s t]; rw [← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

Depends on / 依赖: Equiv.preimage_subset, equivRealProd, preimage_equivRealProd_prod, preimage_subset
-/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set Real} : s ×Complex t subseteq s₁ ×Complex t₁ ↔ s ×ˢ t subseteq s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t]; rw [← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/--
lemma `reProdIm_subset_iff'` / 引理 `reProdIm_subset_iff'`

English:
lemma reProdIm_subset_iff'
  given: {s s₁ t t₁ : Set Real}
  proof: by
  convert! prod_subset_prod_iff
  exact reProdIm_subset_iff

中文:
引理 reProdIm_subset_iff'
  条件: {s s₁ t t₁ : 集合 实数}
  证明: by
  convert! prod_subset_prod_iff
  exact reProdIm_subset_iff

Depends on / 依赖: convert, prod_subset_prod_iff, reProdIm_subset_iff
-/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set Real} :
    s ×Complex t subseteq s₁ ×Complex t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert! prod_subset_prod_iff
  exact reProdIm_subset_iff

variable {s t : Set Real}

/--
lemma `reProdIm_nonempty` / 引理 `reProdIm_nonempty`

English:
lemma reProdIm_nonempty
  statement: (s ×Complex t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: by
  simp [Set.Nonempty, reProdIm, Complex.exists]

中文:
引理 reProdIm_nonempty
  结论: (s ×复形 t).非空 ↔ s.非空 ∧ t.非空
  证明: by
  simp [Set.Nonempty, reProdIm, Complex.exists]
-/
@[simp] lemma reProdIm_nonempty : (s ×Complex t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]

/--
lemma `reProdIm_eq_empty` / 引理 `reProdIm_eq_empty`

English:
lemma reProdIm_eq_empty
  statement: s ×Complex t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

中文:
引理 reProdIm_eq_empty
  结论: s ×复形 t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]
-/
@[simp] lemma reProdIm_eq_empty : s ×Complex t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end reProdIm

open scoped Interval

section Rectangle

/--
Definition of `Rectangle` / `Rectangle` 的定义

English:
definition Rectangle
  signature: (z w : Complex)
  body: [[z.re, w.re]] ×Complex [[z.im, w.im]]

中文:
定义 Rectangle
  签名: (z w : 复形)
  定义体: [[z.re, w.re]] ×Complex [[z.im, w.im]]

Depends on / 依赖: w.im, w.re, z.im, z.re
-/
def Rectangle (z w : Complex) : Set Complex := [[z.re, w.re]] ×Complex [[z.im, w.im]]

end Rectangle

section Segments

/--
lemma `horizontalSegment_eq` / 引理 `horizontalSegment_eq`

English:
lemma horizontalSegment_eq
  given: (a₁ a₂ b : Real)
  proof: by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

中文:
引理 horizontalSegment_eq
  条件: (a₁ a₂ b : 实数)
  证明: by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

Depends on / 依赖: mem_preimage, mem_prod, preimage_equivRealProd_prod, x.re
-/
lemma horizontalSegment_eq (a₁ a₂ b : Real) :
    (fun (x : Real) => x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×Complex {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/--
lemma `verticalSegment_eq` / 引理 `verticalSegment_eq`

English:
lemma verticalSegment_eq
  given: (a b₁ b₂ : Real)
  proof: by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

中文:
引理 verticalSegment_eq
  条件: (a b₁ b₂ : 实数)
  证明: by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

Depends on / 依赖: Prod.mk.injEq, equivRealProd_apply, exists_eq_right_right, mem_image, mem_preimage, mem_prod, preimage_equivRealProd_prod, singleton_prod, x.im
-/
lemma verticalSegment_eq (a b₁ b₂ : Real) :
    (fun (y : Real) => a + y * I) '' [[b₁, b₂]] = {a} ×Complex [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

end Complex
