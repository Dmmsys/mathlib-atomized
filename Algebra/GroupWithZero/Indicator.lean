/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Indicator functions and support of a function in groups with zero
-/

public section

assert_not_exists Ring

open Set

variable {ι κ G₀ M₀ R : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

/--
lemma `indicator_mul` / 引理 `indicator_mul`

English:
lemma indicator_mul
  given: (s : Set ι) (f g : ι -> M₀)
  proof: by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]

中文:
引理 indicator_mul
  条件: (s : 集合 ι) (f g : ι -> M₀)
  证明: by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]

Depends on / 依赖: indicator, mul_zero, split_ifs
-/
lemma indicator_mul (s : Set ι) (f g : ι -> M₀) :
    indicator s (fun i => f i * g i) = fun i => indicator s f i * indicator s g i := by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]

/--
lemma `indicator_mul_left` / 引理 `indicator_mul_left`

English:
lemma indicator_mul_left
  given: (s : Set ι) (f g : ι -> M₀)
  proof: by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [zero_mul]

中文:
引理 indicator_mul_left
  条件: (s : 集合 ι) (f g : ι -> M₀)
  证明: by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [zero_mul]

Depends on / 依赖: indicator, split_ifs, zero_mul
-/
lemma indicator_mul_left (s : Set ι) (f g : ι -> M₀) :
    indicator s (fun j => f j * g j) i = indicator s f i * g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [zero_mul]

/--
lemma `indicator_mul_right` / 引理 `indicator_mul_right`

English:
lemma indicator_mul_right
  given: (s : Set ι) (f g : ι -> M₀)
  proof: by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]

中文:
引理 indicator_mul_right
  条件: (s : 集合 ι) (f g : ι -> M₀)
  证明: by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]

Depends on / 依赖: indicator, mul_zero, split_ifs
-/
lemma indicator_mul_right (s : Set ι) (f g : ι -> M₀) :
    indicator s (fun j => f j * g j) i = f i * indicator s g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]

/--
lemma `indicator_mul_const` / 引理 `indicator_mul_const`

English:
lemma indicator_mul_const
  given: (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι)
  proof: by rw [indicator_mul_left]

中文:
引理 indicator_mul_const
  条件: (s : 集合 ι) (f : ι -> M₀) (a : M₀) (i : ι)
  证明: by rw [indicator_mul_left]

Depends on / 依赖: indicator_mul_left
-/
lemma indicator_mul_const (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι) :
    s.indicator (f · * a) i = s.indicator f i * a := by rw [indicator_mul_left]

/--
lemma `indicator_const_mul` / 引理 `indicator_const_mul`

English:
lemma indicator_const_mul
  given: (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι)
  proof: by rw [indicator_mul_right]

中文:
引理 indicator_const_mul
  条件: (s : 集合 ι) (f : ι -> M₀) (a : M₀) (i : ι)
  证明: by rw [indicator_mul_right]

Depends on / 依赖: indicator_mul_right
-/
lemma indicator_const_mul (s : Set ι) (f : ι -> M₀) (a : M₀) (i : ι) :
    s.indicator (a * f ·) i = a * s.indicator f i := by rw [indicator_mul_right]

/--
lemma `inter_indicator_mul` / 引理 `inter_indicator_mul`

English:
lemma inter_indicator_mul
  given: (f g : ι -> M₀) (i : ι)
  proof: by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp

中文:
引理 inter_indicator_mul
  条件: (f g : ι -> M₀) (i : ι)
  证明: by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp

Depends on / 依赖: Set.indicator_indicator, indicator, indicator_indicator, simp_rw, split_ifs
-/
lemma inter_indicator_mul (f g : ι -> M₀) (i : ι) :
    (s inter t).indicator (fun j => f j * g j) i = s.indicator f i * t.indicator g i := by
  rw [← Set.indicator_indicator]
  simp_rw [indicator]
  split_ifs <;> simp

end MulZeroClass

section MulZeroOneClass
variable [MulZeroOneClass M₀] {s t : Set ι} {i : ι}

/--
lemma `inter_indicator_one` / 引理 `inter_indicator_one`

English:
lemma inter_indicator_one
  statement: (s inter t).indicator (1 : ι -> M₀) = s.indicator 1 * t.indicator 1
  proof: funext fun _ => by simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr

中文:
引理 inter_indicator_one
  结论: (s inter t).indicator (1 : ι -> M₀) = s.indicator 1 * t.indicator 1
  证明: funext fun _ => by simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr

Depends on / 依赖: Pi.mul_apply, Pi.one_apply, inter_indicator_mul, mul_apply, one_apply, one_mul
-/
lemma inter_indicator_one : (s inter t).indicator (1 : ι -> M₀) = s.indicator 1 * t.indicator 1 :=
  funext fun _ => by simp only [← inter_indicator_mul, Pi.mul_apply, Pi.one_apply, one_mul]; congr

set_option backward.isDefEq.respectTransparency false in
/--
lemma `indicator_prod_one` / 引理 `indicator_prod_one`

English:
lemma indicator_prod_one
  given: {t : Set κ} {j : κ}
  proof: by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto

中文:
引理 indicator_prod_one
  条件: {t : 集合 κ} {j : κ}
  证明: by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto

Depends on / 依赖: Pi.one_apply, indicator, mem_prod_eq, mul_one, mul_zero, one_apply, simp_rw, split_ifs
-/
lemma indicator_prod_one {t : Set κ} {j : κ} :
    (s ×ˢ t).indicator (1 : ι × κ -> M₀) (i, j) = s.indicator 1 i * t.indicator 1 j := by
  simp_rw [indicator, mem_prod_eq]
  split_ifs with h₀ <;> simp only [Pi.one_apply, mul_one, mul_zero] <;> tauto

variable (M₀) [Nontrivial M₀]

/--
lemma `indicator_eq_zero_iff_notMem` / 引理 `indicator_eq_zero_iff_notMem`

English:
lemma indicator_eq_zero_iff_notMem
  statement: indicator s 1 i = (0 : M₀) ↔ i ∉ s
  proof: by
  simp

中文:
引理 indicator_eq_zero_iff_notMem
  结论: indicator s 1 i = (0 : M₀) ↔ i ∉ s
  证明: by
  simp

Depends on / 依赖: Category, Category.comp_id, comp_id, if_pos
-/
lemma indicator_eq_zero_iff_notMem : indicator s 1 i = (0 : M₀) ↔ i ∉ s := by
  simp

/--
lemma `indicator_eq_one_iff_mem` / 引理 `indicator_eq_one_iff_mem`

English:
lemma indicator_eq_one_iff_mem
  statement: indicator s 1 i = (1 : M₀) ↔ i in s
  proof: by
  classical simp [indicator_apply, imp_false]

中文:
引理 indicator_eq_one_iff_mem
  结论: indicator s 1 i = (1 : M₀) ↔ i in s
  证明: by
  classical simp [indicator_apply, imp_false]

Depends on / 依赖: classical, imp_false, indicator_apply
-/
lemma indicator_eq_one_iff_mem : indicator s 1 i = (1 : M₀) ↔ i in s := by
  classical simp [indicator_apply, imp_false]

/--
lemma `indicator_one_inj` / 引理 `indicator_one_inj`

English:
lemma indicator_one_inj
  given: (h : indicator s (1 : ι -> M₀) = indicator t 1)
  statement: s = t
  proof: by
  ext; simp_rw [← indicator_eq_one_iff_mem M₀, h]

中文:
引理 indicator_one_inj
  条件: (h : indicator s (1 : ι -> M₀) = indicator t 1)
  结论: s = t
  证明: by
  ext; simp_rw [← indicator_eq_one_iff_mem M₀, h]

Depends on / 依赖: indicator_eq_one_iff_mem, simp_rw
-/
lemma indicator_one_inj (h : indicator s (1 : ι -> M₀) = indicator t 1) : s = t := by
  ext; simp_rw [← indicator_eq_one_iff_mem M₀, h]

end MulZeroOneClass
end Set

namespace Function
section ZeroOne
variable (R) [Zero R] [One R] [NeZero (1 : R)]

/--
lemma `support_one` / 引理 `support_one`

English:
lemma support_one
  statement: support (1 : ι -> R) = univ
  proof: support_const one_ne_zero

中文:
引理 support_one
  结论: support (1 : ι -> R) = univ
  证明: support_const one_ne_zero
-/
@[simp] lemma support_one : support (1 : ι -> R) = univ := support_const one_ne_zero

/--
lemma `mulSupport_zero` / 引理 `mulSupport_zero`

English:
lemma mulSupport_zero
  statement: mulSupport (0 : ι -> R) = univ
  proof: mulSupport_const zero_ne_one

中文:
引理 mulSupport_zero
  结论: mulSupport (0 : ι -> R) = univ
  证明: mulSupport_const zero_ne_one
-/
@[simp] lemma mulSupport_zero : mulSupport (0 : ι -> R) = univ := mulSupport_const zero_ne_one

end ZeroOne

section MulZeroClass
variable [MulZeroClass M₀]

/--
lemma `support_mul_subset_left` / 引理 `support_mul_subset_left`

English:
lemma support_mul_subset_left
  given: (f g : ι -> M₀)
  statement: support (fun x => f x * g x) subseteq support f
  proof: fun x hfg hf => hfg by simp only [hf, zero_mul]

中文:
引理 support_mul_subset_left
  条件: (f g : ι -> M₀)
  结论: support (fun x => f x * g x) subseteq support f
  证明: fun x hfg hf => hfg by simp only [hf, zero_mul]

Depends on / 依赖: zero_mul
-/
lemma support_mul_subset_left (f g : ι -> M₀) : support (fun x => f x * g x) subseteq support f :=
fun x hfg hf => hfg by simp only [hf, zero_mul]

/--
lemma `support_mul_subset_right` / 引理 `support_mul_subset_right`

English:
lemma support_mul_subset_right
  given: (f g : ι -> M₀)
  statement: support (fun x => f x * g x) subseteq support g
  proof: fun x hfg hg => hfg by simp only [hg, mul_zero]

中文:
引理 support_mul_subset_right
  条件: (f g : ι -> M₀)
  结论: support (fun x => f x * g x) subseteq support g
  证明: fun x hfg hg => hfg by simp only [hg, mul_zero]

Depends on / 依赖: mul_zero
-/
lemma support_mul_subset_right (f g : ι -> M₀) : support (fun x => f x * g x) subseteq support g :=
fun x hfg hg => hfg by simp only [hg, mul_zero]

variable [NoZeroDivisors M₀]

/--
lemma `support_mul` / 引理 `support_mul`

English:
lemma support_mul
  given: (f g : ι -> M₀)
  statement: support (fun x => f x * g x) = support f inter support g
  proof: ext fun x => by simp [not_or]

中文:
引理 support_mul
  条件: (f g : ι -> M₀)
  结论: support (fun x => f x * g x) = support f inter support g
  证明: ext fun x => by simp [not_or]
-/
@[simp] lemma support_mul (f g : ι -> M₀) : support (fun x => f x * g x) = support f inter support g :=
  ext fun x => by simp [not_or]

/--
lemma `support_mul'` / 引理 `support_mul'`

English:
lemma support_mul'
  given: (f g : ι -> M₀)
  statement: support (f * g) = support f inter support g
  proof: support_mul _ _

中文:
引理 support_mul'
  条件: (f g : ι -> M₀)
  结论: support (f * g) = support f inter support g
  证明: support_mul _ _
-/
@[simp] lemma support_mul' (f g : ι -> M₀) : support (f * g) = support f inter support g :=
  support_mul _ _

/--
lemma `support_mul_of_ne_zero_left` / 引理 `support_mul_of_ne_zero_left`

English:
lemma support_mul_of_ne_zero_left
  given: {f : ι -> M₀} (hf : forall x, f x != 0) (g : ι -> M₀)
  proof: by simp [support_eq_univ hf]

中文:
引理 support_mul_of_ne_zero_left
  条件: {f : ι -> M₀} (hf : 对任意 x, f x != 0) (g : ι -> M₀)
  证明: by simp [support_eq_univ hf]

Depends on / 依赖: support_eq_univ
-/
lemma support_mul_of_ne_zero_left {f : ι -> M₀} (hf : forall x, f x != 0) (g : ι -> M₀) :
    support (fun x => f x * g x) = support g := by simp [support_eq_univ hf]

/--
lemma `support_mul_of_ne_zero_right` / 引理 `support_mul_of_ne_zero_right`

English:
lemma support_mul_of_ne_zero_right
  given: (f : ι -> M₀) {g : ι -> M₀} (hg : forall x, g x != 0)
  proof: by simp [support_eq_univ hg]

中文:
引理 support_mul_of_ne_zero_right
  条件: (f : ι -> M₀) {g : ι -> M₀} (hg : 对任意 x, g x != 0)
  证明: by simp [support_eq_univ hg]

Depends on / 依赖: support_eq_univ
-/
lemma support_mul_of_ne_zero_right (f : ι -> M₀) {g : ι -> M₀} (hg : forall x, g x != 0) :
    support (fun x => f x * g x) = support f := by simp [support_eq_univ hg]

end MulZeroClass

section MonoidWithZero
variable [MonoidWithZero M₀] [IsReduced M₀] {n : Nat}

/--
lemma `support_pow` / 引理 `support_pow`

English:
lemma support_pow
  given: (f : ι -> M₀) (hn : n != 0)
  statement: support (fun a => f a ^ n) = support f
  proof: by
  ext; exact (pow_eq_zero_iff hn).not

中文:
引理 support_pow
  条件: (f : ι -> M₀) (hn : n != 0)
  结论: support (fun a => f a ^ n) = support f
  证明: by
  ext; exact (pow_eq_zero_iff hn).not

Depends on / 依赖: infer_instance, injective, isZero_single_obj_X, single_obj_X_self
-/
@[simp] lemma support_pow (f : ι -> M₀) (hn : n != 0) : support (fun a => f a ^ n) = support f := by
  ext; exact (pow_eq_zero_iff hn).not

/--
lemma `support_pow'` / 引理 `support_pow'`

English:
lemma support_pow'
  given: (f : ι -> M₀) (hn : n != 0)
  statement: support (f ^ n) = support f
  proof: support_pow _ hn

中文:
引理 support_pow'
  条件: (f : ι -> M₀) (hn : n != 0)
  结论: support (f ^ n) = support f
  证明: support_pow _ hn

Depends on / 依赖: infer_instance, isZero_single_obj_X, projective, single_obj_X_self
-/
@[simp] lemma support_pow' (f : ι -> M₀) (hn : n != 0) : support (f ^ n) = support f :=
  support_pow _ hn

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

/--
lemma `support_inv` / 引理 `support_inv`

English:
lemma support_inv
  given: (f : ι -> G₀)
  statement: support (fun a => (f a)⁻¹) = support f
  proof: Set.ext fun _ => not_congr inv_eq_zero

中文:
引理 support_inv
  条件: (f : ι -> G₀)
  结论: support (fun a => (f a)⁻¹) = support f
  证明: Set.ext fun _ => not_congr inv_eq_zero
-/
@[simp] lemma support_inv (f : ι -> G₀) : support (fun a => (f a)⁻¹) = support f :=
  Set.ext fun _ => not_congr inv_eq_zero

/--
lemma `support_inv'` / 引理 `support_inv'`

English:
lemma support_inv'
  given: (f : ι -> G₀)
  statement: support f⁻¹ = support f
  proof: support_inv _

中文:
引理 support_inv'
  条件: (f : ι -> G₀)
  结论: support f⁻¹ = support f
  证明: support_inv _
-/
@[simp] lemma support_inv' (f : ι -> G₀) : support f⁻¹ = support f := support_inv _

/--
lemma `support_div` / 引理 `support_div`

English:
lemma support_div
  given: (f g : ι -> G₀)
  statement: support (fun a => f a / g a) = support f inter support g
  proof: by
  simp [div_eq_mul_inv]

中文:
引理 support_div
  条件: (f g : ι -> G₀)
  结论: support (fun a => f a / g a) = support f inter support g
  证明: by
  simp [div_eq_mul_inv]
-/
@[simp] lemma support_div (f g : ι -> G₀) : support (fun a => f a / g a) = support f inter support g := by
  simp [div_eq_mul_inv]

/--
lemma `support_div'` / 引理 `support_div'`

English:
lemma support_div'
  given: (f g : ι -> G₀)
  statement: support (f / g) = support f inter support g
  proof: support_div _ _

中文:
引理 support_div'
  条件: (f g : ι -> G₀)
  结论: support (f / g) = support f inter support g
  证明: support_div _ _
-/
@[simp] lemma support_div' (f g : ι -> G₀) : support (f / g) = support f inter support g :=
  support_div _ _

end GroupWithZero

variable [One R]

/--
lemma `mulSupport_one_add` / 引理 `mulSupport_one_add`

English:
lemma mulSupport_one_add
  given: [AddLeftCancelMonoid R] (f : ι -> R)
  proof: Set.ext fun _ => not_congr add_eq_left

中文:
引理 mulSupport_one_add
  条件: [加法左消去幺半群 R] (f : ι -> R)
  证明: Set.ext fun _ => not_congr add_eq_left

Depends on / 依赖: Set.ext, add_eq_left, infer_instance, not_congr
-/
lemma mulSupport_one_add [AddLeftCancelMonoid R] (f : ι -> R) :
    mulSupport (fun x => 1 + f x) = support f :=
  Set.ext fun _ => not_congr add_eq_left

/--
lemma `mulSupport_one_add'` / 引理 `mulSupport_one_add'`

English:
lemma mulSupport_one_add'
  given: [AddLeftCancelMonoid R] (f : ι -> R)
  statement: mulSupport (1 + f) = support f
  proof: mulSupport_one_add f

中文:
引理 mulSupport_one_add'
  条件: [加法左消去幺半群 R] (f : ι -> R)
  结论: mulSupport (1 + f) = support f
  证明: mulSupport_one_add f

Depends on / 依赖: diagramIsoPair, e.symm, hasLimit_of_iso, mulSupport_one_add
-/
lemma mulSupport_one_add' [AddLeftCancelMonoid R] (f : ι -> R) : mulSupport (1 + f) = support f :=
  mulSupport_one_add f

/--
lemma `mulSupport_add_one` / 引理 `mulSupport_add_one`

English:
lemma mulSupport_add_one
  given: [AddRightCancelMonoid R] (f : ι -> R)
  proof: Set.ext fun _ => not_congr add_eq_right

中文:
引理 mulSupport_add_one
  条件: [加法右消去幺半群 R] (f : ι -> R)
  证明: Set.ext fun _ => not_congr add_eq_right

Depends on / 依赖: Set.ext, add_eq_right, diagramIsoPair, hasColimit_of_iso, not_congr
-/
lemma mulSupport_add_one [AddRightCancelMonoid R] (f : ι -> R) :
    mulSupport (fun x => f x + 1) = support f := Set.ext fun _ => not_congr add_eq_right

/--
lemma `mulSupport_add_one'` / 引理 `mulSupport_add_one'`

English:
lemma mulSupport_add_one'
  given: [AddRightCancelMonoid R] (f : ι -> R)
  statement: mulSupport (f + 1) = support f
  proof: mulSupport_add_one f

中文:
引理 mulSupport_add_one'
  条件: [加法右消去幺半群 R] (f : ι -> R)
  结论: mulSupport (f + 1) = support f
  证明: mulSupport_add_one f

Depends on / 依赖: mulSupport_add_one
-/
lemma mulSupport_add_one' [AddRightCancelMonoid R] (f : ι -> R) : mulSupport (f + 1) = support f :=
  mulSupport_add_one f

/--
lemma `mulSupport_one_sub'` / 引理 `mulSupport_one_sub'`

English:
lemma mulSupport_one_sub'
  given: [AddGroup R] (f : ι -> R)
  statement: mulSupport (1 - f) = support f
  proof: by
  rw [sub_eq_add_neg]; rw [mulSupport_one_add']; rw [support_neg]

中文:
引理 mulSupport_one_sub'
  条件: [加法群 R] (f : ι -> R)
  结论: mulSupport (1 - f) = support f
  证明: by
  rw [sub_eq_add_neg]; rw [mulSupport_one_add']; rw [support_neg]

Depends on / 依赖: mulSupport_one_add, preservesBinaryBiproduct_of_preservesBinaryProduct, sub_eq_add_neg, support_neg
-/
lemma mulSupport_one_sub' [AddGroup R] (f : ι -> R) : mulSupport (1 - f) = support f := by
  rw [sub_eq_add_neg]; rw [mulSupport_one_add']; rw [support_neg]

/--
lemma `mulSupport_one_sub` / 引理 `mulSupport_one_sub`

English:
lemma mulSupport_one_sub
  given: [AddGroup R] (f : ι -> R)
  proof: mulSupport_one_sub' f

中文:
引理 mulSupport_one_sub
  条件: [加法群 R] (f : ι -> R)
  证明: mulSupport_one_sub' f

Depends on / 依赖: mulSupport_one_sub
-/
lemma mulSupport_one_sub [AddGroup R] (f : ι -> R) :
    mulSupport (fun x => 1 - f x) = support f := mulSupport_one_sub' f

end Function
