/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `Circle.exp` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `Circle` and `ℝ`, see
`Circle.argPartialEquiv` and `Circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/

@[expose] public section


open Complex Function Set

open Real

namespace Circle

/--
theorem `injective_arg` / 定理 `injective_arg`

English:
theorem injective_arg
  statement: Injective fun z : Circle => arg z
  proof: fun z w h =>
Subtype.ext ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h

@[simp]

中文:
定理 injective_arg
  结论: 单射 fun z : Circle => arg z
  证明: fun z w h =>
Subtype.ext ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h

@[simp]
-/
theorem injective_arg : Injective fun z : Circle => arg z := fun z w h =>
Subtype.ext ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h

@[simp]
/--
theorem `arg_eq_arg` / 定理 `arg_eq_arg`

English:
theorem arg_eq_arg
  given: {z w : Circle}
  statement: arg z = arg w ↔ z = w
  proof: injective_arg.eq_iff

@[simp]

中文:
定理 arg_eq_arg
  条件: {z w : Circle}
  结论: arg z = arg w ↔ z = w
  证明: injective_arg.eq_iff

@[simp]

Depends on / 依赖: eq_iff, injective_arg, injective_arg.eq_iff
-/
theorem arg_eq_arg {z w : Circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff

@[simp]
/--
theorem `arg_eq_zero` / 定理 `arg_eq_zero`

English:
theorem arg_eq_zero
  given: {z : Circle}
  statement: arg z = 0 ↔ z = 1
  proof: by
  simpa using arg_eq_arg (w := 1)

中文:
定理 arg_eq_zero
  条件: {z : Circle}
  结论: arg z = 0 ↔ z = 1
  证明: by
  simpa using arg_eq_arg (w := 1)

Depends on / 依赖: arg_eq_arg
-/
theorem arg_eq_zero {z : Circle} : arg z = 0 ↔ z = 1 := by
  simpa using arg_eq_arg (w := 1)

/--
theorem `arg_exp` / 定理 `arg_exp`

English:
theorem arg_exp
  given: {x : Real} (h₁ : -π < x) (h₂ : x <= π)
  statement: arg (exp x) = x
  proof: by
  rw [coe_exp]; rw [exp_mul_I]; rw [arg_cos_add_sin_mul_I ⟨h₁]; rw [h₂⟩]

@[simp]

中文:
定理 arg_exp
  条件: {x : 实数} (h₁ : -π < x) (h₂ : x <= π)
  结论: arg (exp x) = x
  证明: by
  rw [coe_exp]; rw [exp_mul_I]; rw [arg_cos_add_sin_mul_I ⟨h₁]; rw [h₂⟩]

@[simp]

Depends on / 依赖: arg_cos_add_sin_mul_I, coe_exp, exp_mul_I
-/
theorem arg_exp {x : Real} (h₁ : -π < x) (h₂ : x <= π) : arg (exp x) = x := by
  rw [coe_exp]; rw [exp_mul_I]; rw [arg_cos_add_sin_mul_I ⟨h₁]; rw [h₂⟩]

@[simp]
/--
theorem `exp_arg` / 定理 `exp_arg`

English:
theorem exp_arg
  given: (z : Circle)
  statement: exp (arg z) = z
  proof: injective_arg arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

中文:
定理 exp_arg
  条件: (z : Circle)
  结论: exp (arg z) = z
  证明: injective_arg arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

Depends on / 依赖: arg_exp, arg_le_pi, injective_arg, neg_pi_lt_arg
-/
theorem exp_arg (z : Circle) : exp (arg z) = z :=
injective_arg arg_exp (neg_pi_lt_arg _) (arg_le_pi _)

/-- `Complex.arg ∘ (↑)` and `Circle.exp` define a partial equivalence between `Circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps -fullyApplied]
/--
Definition of `argPartialEquiv` / `argPartialEquiv` 的定义

English:
definition argPartialEquiv
  signature: : PartialEquiv Circle Real where
  body: arg ∘ (↑)
  invFun := exp
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := exp_arg z
  right_inv' _ hx := arg_exp hx.1 hx.2

中文:
定义 argPartialEquiv
  签名: : 部分等价 Circle 实数 where
  定义体: arg ∘ (↑)
  invFun := exp
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := exp_arg z
  right_inv' _ hx := arg_exp hx.1 hx.2
-/
noncomputable def argPartialEquiv : PartialEquiv Circle Real where
  toFun := arg ∘ (↑)
  invFun := exp
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := exp_arg z
  right_inv' _ hx := arg_exp hx.1 hx.2

/-- `Complex.arg` and `Circle.exp ∘ (↑)` define an equivalence between `Circle` and `(-π, π]`. -/
@[simps -fullyApplied]
/--
Definition of `argEquiv` / `argEquiv` 的定义

English:
definition argEquiv
  signature: : Circle ≃ Ioc (-π) π where
  body: ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := exp ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
right_inv x := Subtype.ext argPartialEquiv.right_inv x.2

中文:
定义 argEquiv
  签名: : Circle ≃ 左开右闭区间 (-π) π where
  定义体: ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := exp ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
right_inv x := Subtype.ext argPartialEquiv.right_inv x.2

Depends on / 依赖: arg_le_pi, neg_pi_lt_arg
-/
noncomputable def argEquiv : Circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := exp ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
right_inv x := Subtype.ext argPartialEquiv.right_inv x.2

/--
lemma `leftInverse_exp_arg` / 引理 `leftInverse_exp_arg`

English:
lemma leftInverse_exp_arg
  statement: LeftInverse exp (arg ∘ (↑))
  proof: exp_arg

中文:
引理 leftInverse_exp_arg
  结论: 左逆 exp (arg ∘ (↑))
  证明: exp_arg

Depends on / 依赖: exp_arg
-/
lemma leftInverse_exp_arg : LeftInverse exp (arg ∘ (↑)) := exp_arg
/--
lemma `invOn_arg_exp` / 引理 `invOn_arg_exp`

English:
lemma invOn_arg_exp
  statement: InvOn (arg ∘ (↑)) exp (Ioc (-π) π) univ
  proof: argPartialEquiv.symm.invOn

中文:
引理 invOn_arg_exp
  结论: InvOn (arg ∘ (↑)) exp (左开右闭区间 (-π) π) univ
  证明: argPartialEquiv.symm.invOn

Depends on / 依赖: argPartialEquiv, argPartialEquiv.symm.invOn
-/
lemma invOn_arg_exp : InvOn (arg ∘ (↑)) exp (Ioc (-π) π) univ := argPartialEquiv.symm.invOn
/--
lemma `surjOn_exp_neg_pi_pi` / 引理 `surjOn_exp_neg_pi_pi`

English:
lemma surjOn_exp_neg_pi_pi
  statement: SurjOn exp (Ioc (-π) π) univ
  proof: argPartialEquiv.symm.surjOn

中文:
引理 surjOn_exp_neg_pi_pi
  结论: 满射限制 exp (左开右闭区间 (-π) π) univ
  证明: argPartialEquiv.symm.surjOn

Depends on / 依赖: argPartialEquiv, argPartialEquiv.symm.surjOn, surjOn
-/
lemma surjOn_exp_neg_pi_pi : SurjOn exp (Ioc (-π) π) univ := argPartialEquiv.symm.surjOn

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exp_eq_exp` / 引理 `exp_eq_exp`

English:
lemma exp_eq_exp
  given: {x y : Real}
  statement: exp x = exp y ↔ exists m : Int, x = y + m * (2 * π)
  proof: by
  rw [Subtype.ext_iff]; rw [coe_exp]; rw [coe_exp]; rw [exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc]; rw [← add_mul]; rw [mul_left_inj' I_ne_zero]
  norm_cast

中文:
引理 exp_eq_exp
  条件: {x y : 实数}
  结论: exp x = exp y ↔ 存在 m : 整数, x = y + m * (2 * π)
  证明: by
  rw [Subtype.ext_iff]; rw [coe_exp]; rw [coe_exp]; rw [exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc]; rw [← add_mul]; rw [mul_left_inj' I_ne_zero]
  norm_cast

Depends on / 依赖: I_ne_zero, Subtype, Subtype.ext_iff, add_mul, coe_exp, exists_congr, exp_eq_exp_iff_exists_int, ext_iff, mul_assoc, mul_left_inj
-/
lemma exp_eq_exp {x y : Real} : exp x = exp y ↔ exists m : Int, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff]; rw [coe_exp]; rw [coe_exp]; rw [exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  rw [← mul_assoc]; rw [← add_mul]; rw [mul_left_inj' I_ne_zero]
  norm_cast

/--
lemma `periodic_exp` / 引理 `periodic_exp`

English:
lemma periodic_exp
  statement: Periodic exp (2 * π)
  proof: fun z => exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

中文:
引理 periodic_exp
  结论: 周期 exp (2 * π)
  证明: fun z => exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

Depends on / 依赖: Int.cast_one, cast_one, exp_eq_exp, one_mul
-/
lemma periodic_exp : Periodic exp (2 * π) := fun z => exp_eq_exp.2 ⟨1, by rw [Int.cast_one, one_mul]⟩

/--
lemma `exp_two_pi` / 引理 `exp_two_pi`

English:
lemma exp_two_pi
  statement: exp (2 * π) = 1
  proof: periodic_exp.eq.trans exp_zero

中文:
引理 exp_two_pi
  结论: exp (2 * π) = 1
  证明: periodic_exp.eq.trans exp_zero
-/
@[simp] lemma exp_two_pi : exp (2 * π) = 1 := periodic_exp.eq.trans exp_zero

/--
lemma `exp_int_mul_two_pi` / 引理 `exp_int_mul_two_pi`

English:
lemma exp_int_mul_two_pi
  given: (n : Int)
  statement: exp (n * (2 * π)) = 1
  proof: ext by simp

中文:
引理 exp_int_mul_two_pi
  条件: (n : 整数)
  结论: exp (n * (2 * π)) = 1
  证明: ext by simp
-/
lemma exp_int_mul_two_pi (n : Int) : exp (n * (2 * π)) = 1 :=
ext by simp

/--
lemma `exp_two_pi_mul_int` / 引理 `exp_two_pi_mul_int`

English:
lemma exp_two_pi_mul_int
  given: (n : Int)
  statement: exp (2 * π * n) = 1
  proof: by
  simpa only [mul_comm] using exp_int_mul_two_pi n

中文:
引理 exp_two_pi_mul_int
  条件: (n : 整数)
  结论: exp (2 * π * n) = 1
  证明: by
  simpa only [mul_comm] using exp_int_mul_two_pi n

Depends on / 依赖: exp_int_mul_two_pi, mul_comm
-/
lemma exp_two_pi_mul_int (n : Int) : exp (2 * π * n) = 1 := by
  simpa only [mul_comm] using exp_int_mul_two_pi n

/--
lemma `exp_eq_one` / 引理 `exp_eq_one`

English:
lemma exp_eq_one
  given: {r : Real}
  statement: exp r = 1 ↔ exists n : Int, r = n * (2 * π)
  proof: by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

中文:
引理 exp_eq_one
  条件: {r : 实数}
  结论: exp r = 1 ↔ 存在 n : 整数, r = n * (2 * π)
  证明: by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

Depends on / 依赖: Circle, Circle.ext_iff, Complex.I_ne_zero, Complex.exp_eq_one_iff, Complex.ofReal_inj, I_ne_zero, exp_eq_one_iff, ext_iff, mul_assoc, ofReal_inj
-/
lemma exp_eq_one {r : Real} : exp r = 1 ↔ exists n : Int, r = n * (2 * π) := by
  simp [Circle.ext_iff, Complex.exp_eq_one_iff, ← mul_assoc, Complex.I_ne_zero,
    ← Complex.ofReal_inj]

/--
lemma `exp_inj` / 引理 `exp_inj`

English:
lemma exp_inj
  given: {r s : Real}
  statement: exp r = exp s ↔ r ≡ s [PMOD (2 * π)]
  proof: by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]

中文:
引理 exp_inj
  条件: {r s : 实数}
  结论: exp r = exp s ↔ r ≡ s [PMOD (2 * π)]
  证明: by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]

Depends on / 依赖: AddCommGroup, AddCommGroup.modEq_iff_zsmul, div_eq_one, eq_comm, exp_eq_one, modEq_iff_zsmul
-/
lemma exp_inj {r s : Real} : exp r = exp s ↔ r ≡ s [PMOD (2 * π)] := by
  simp [AddCommGroup.modEq_iff_zsmul', ← exp_eq_one, div_eq_one, eq_comm (a := exp r)]

/--
lemma `exp_sub_two_pi` / 引理 `exp_sub_two_pi`

English:
lemma exp_sub_two_pi
  given: (x : Real)
  statement: exp (x - 2 * π) = exp x
  proof: periodic_exp.sub_eq x

中文:
引理 exp_sub_two_pi
  条件: (x : 实数)
  结论: exp (x - 2 * π) = exp x
  证明: periodic_exp.sub_eq x

Depends on / 依赖: periodic_exp, periodic_exp.sub_eq, sub_eq
-/
lemma exp_sub_two_pi (x : Real) : exp (x - 2 * π) = exp x := periodic_exp.sub_eq x
/--
lemma `exp_add_two_pi` / 引理 `exp_add_two_pi`

English:
lemma exp_add_two_pi
  given: (x : Real)
  statement: exp (x + 2 * π) = exp x
  proof: periodic_exp x

中文:
引理 exp_add_two_pi
  条件: (x : 实数)
  结论: exp (x + 2 * π) = exp x
  证明: periodic_exp x

Depends on / 依赖: periodic_exp
-/
lemma exp_add_two_pi (x : Real) : exp (x + 2 * π) = exp x := periodic_exp x

/--
lemma `exp_injOn_of_forall_sub_mem_Ioo` / 引理 `exp_injOn_of_forall_sub_mem_Ioo`

English:
lemma exp_injOn_of_forall_sub_mem_Ioo
  statement: {s : Set Real}
  proof: by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero]; rw [← cos_eq_one_iff_of_lt_of_lt h1 h2]; rw [← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one]; rw [← sub_mul]; rw [← ofReal_sub]; rw [Complex.ext_iff] at heq
  exact heq.1

中文:
引理 exp_injOn_of_对任意_sub_mem_Ioo
  结论: {s : 集合 实数}
  证明: by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero]; rw [← cos_eq_one_iff_of_lt_of_lt h1 h2]; rw [← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one]; rw [← sub_mul]; rw [← ofReal_sub]; rw [Complex.ext_iff] at heq
  exact heq.1

Depends on / 依赖: Complex.ext_iff, Subtype, Subtype.val, cos_eq_one_iff_of_lt_of_lt, exp_eq_exp_iff_exp_sub_eq_one, exp_ofReal_mul_I_re, ext_iff, neg_mul, ofReal_sub, replace, sub_eq_zero, sub_mul
-/
lemma exp_injOn_of_forall_sub_mem_Ioo {s : Set Real}
    (hs : forall x in s, forall y in s, x - y in Ioo (-2 * π) (2 * π)) : InjOn exp s := by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero]; rw [← cos_eq_one_iff_of_lt_of_lt h1 h2]; rw [← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one]; rw [← sub_mul]; rw [← ofReal_sub]; rw [Complex.ext_iff] at heq
  exact heq.1

/--
lemma `exp_injOn_Icc` / 引理 `exp_injOn_Icc`

English:
lemma exp_injOn_Icc
  given: {a b : Real} (h : b - a < 2 * π)
  statement: InjOn exp (Icc a b)
  proof: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

中文:
引理 exp_injOn_Icc
  条件: {a b : 实数} (h : b - a < 2 * π)
  结论: 单射限制 exp (闭区间 a b)
  证明: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

Depends on / 依赖: exp_injOn_of_forall_sub_mem_Ioo
-/
lemma exp_injOn_Icc {a b : Real} (h : b - a < 2 * π) : InjOn exp (Icc a b) :=
exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

/--
lemma `exp_injOn_Ico` / 引理 `exp_injOn_Ico`

English:
lemma exp_injOn_Ico
  given: {a b : Real} (h : b - a <= 2 * π)
  statement: InjOn exp (Ico a b)
  proof: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

中文:
引理 exp_injOn_Ico
  条件: {a b : 实数} (h : b - a <= 2 * π)
  结论: 单射限制 exp (左闭右开区间 a b)
  证明: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

Depends on / 依赖: exp_injOn_of_forall_sub_mem_Ioo
-/
lemma exp_injOn_Ico {a b : Real} (h : b - a <= 2 * π) : InjOn exp (Ico a b) :=
exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

/--
lemma `exp_injOn_Ioc` / 引理 `exp_injOn_Ioc`

English:
lemma exp_injOn_Ioc
  given: {a b : Real} (h : b - a <= 2 * π)
  statement: InjOn exp (Ioc a b)
  proof: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

中文:
引理 exp_injOn_Ioc
  条件: {a b : 实数} (h : b - a <= 2 * π)
  结论: 单射限制 exp (左开右闭区间 a b)
  证明: exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

Depends on / 依赖: exp_injOn_of_forall_sub_mem_Ioo
-/
lemma exp_injOn_Ioc {a b : Real} (h : b - a <= 2 * π) : InjOn exp (Ioc a b) :=
exp_injOn_of_forall_sub_mem_Ioo fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ => by constructor <;> linarith

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `centeredArc` / `centeredArc` 的定义

English:
definition centeredArc
  signature: (r : Real)
  body: exp '' {x | |x| < r}

中文:
定义 centeredArc
  签名: (r : 实数)
  定义体: exp '' {x | |x| < r}
-/
noncomputable def centeredArc (r : Real) : Set Circle :=
  exp '' {x | |x| < r}

/--
theorem `bijOn_exp_Ioo_centeredArc` / 定理 `bijOn_exp_Ioo_centeredArc`

English:
theorem bijOn_exp_Ioo_centeredArc
  given: {r : Real} (hr : r <= π)
  proof: by
  simp_rw [centeredArc, abs_lt, Set.Ioo_def]
.bijOn_image .mono Ioo_subset_Ico_self refine exp_injOn_Ico ?_
  grind

中文:
定理 bijOn_exp_Ioo_centeredArc
  条件: {r : 实数} (hr : r <= π)
  证明: by
  simp_rw [centeredArc, abs_lt, Set.Ioo_def]
.bijOn_image .mono Ioo_subset_Ico_self refine exp_injOn_Ico ?_
  grind

Depends on / 依赖: Ioo_def, Ioo_subset_Ico_self, Set.Ioo_def, abs_lt, bijOn_image, centeredArc, exp_injOn_Ico, simp_rw
-/
theorem bijOn_exp_Ioo_centeredArc {r : Real} (hr : r <= π) :
    BijOn Circle.exp (Ioo (-r) r) (centeredArc r) := by
  simp_rw [centeredArc, abs_lt, Set.Ioo_def]
.bijOn_image .mono Ioo_subset_Ico_self refine exp_injOn_Ico ?_
  grind

/--
theorem `centeredArc_mono` / 定理 `centeredArc_mono`

English:
theorem centeredArc_mono
  given: {r s : Real} (h : r <= s)
  statement: centeredArc r subseteq centeredArc s
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans_le h, rfl⟩

中文:
定理 centeredArc_mono
  条件: {r s : 实数} (h : r <= s)
  结论: centeredArc r subseteq centeredArc s
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans_le h, rfl⟩

Depends on / 依赖: hx.trans_le, trans_le
-/
theorem centeredArc_mono {r s : Real} (h : r <= s) : centeredArc r subseteq centeredArc s := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.trans_le h, rfl⟩

/--
theorem `mem_centeredArc` / 定理 `mem_centeredArc`

English:
theorem mem_centeredArc
  given: {r : Real} (hr : r <= π) {z : Circle}
  proof: by
  refine ⟨?_, fun hz => ⟨arg z, hz, exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  have htπ : |t| < π := ht.trans_le hr
  rwa [arg_exp (neg_lt_of_abs_lt htπ) (lt_of_abs_lt htπ).le]

中文:
定理 mem_centeredArc
  条件: {r : 实数} (hr : r <= π) {z : Circle}
  证明: by
  refine ⟨?_, fun hz => ⟨arg z, hz, exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  have htπ : |t| < π := ht.trans_le hr
  rwa [arg_exp (neg_lt_of_abs_lt htπ) (lt_of_abs_lt htπ).le]

Depends on / 依赖: arg_exp, exp_arg, ht.trans_le, lt_of_abs_lt, neg_lt_of_abs_lt, trans_le
-/
theorem mem_centeredArc {r : Real} (hr : r <= π) {z : Circle} :
    z in centeredArc r ↔ |arg z| < r := by
  refine ⟨?_, fun hz => ⟨arg z, hz, exp_arg z⟩⟩
  rintro ⟨t, ht, rfl⟩
  have htπ : |t| < π := ht.trans_le hr
  rwa [arg_exp (neg_lt_of_abs_lt htπ) (lt_of_abs_lt htπ).le]

/--
theorem `centeredArc_eq_empty` / 定理 `centeredArc_eq_empty`

English:
theorem centeredArc_eq_empty
  given: {r : Real} (hr : r <= 0)
  statement: centeredArc r = ∅
  proof: by
  contrapose! hr
  obtain ⟨-, x, hx, rfl⟩ := hr
  exact (abs_nonneg x).trans_lt hx

@[simp]

中文:
定理 centeredArc_eq_empty
  条件: {r : 实数} (hr : r <= 0)
  结论: centeredArc r = ∅
  证明: by
  contrapose! hr
  obtain ⟨-, x, hx, rfl⟩ := hr
  exact (abs_nonneg x).trans_lt hx

@[simp]

Depends on / 依赖: abs_nonneg, contrapose, trans_lt
-/
theorem centeredArc_eq_empty {r : Real} (hr : r <= 0) : centeredArc r = ∅ := by
  contrapose! hr
  obtain ⟨-, x, hx, rfl⟩ := hr
  exact (abs_nonneg x).trans_lt hx

@[simp]
/--
theorem `centeredArc_zero` / 定理 `centeredArc_zero`

English:
theorem centeredArc_zero
  statement: centeredArc 0 = ∅
  proof: centeredArc_eq_empty le_rfl

中文:
定理 centeredArc_zero
  结论: centeredArc 0 = ∅
  证明: centeredArc_eq_empty le_rfl

Depends on / 依赖: centeredArc_eq_empty, le_rfl
-/
theorem centeredArc_zero : centeredArc 0 = ∅ :=
  centeredArc_eq_empty le_rfl

/--
theorem `mem_centeredArc_div` / 定理 `mem_centeredArc_div`

English:
theorem mem_centeredArc_div
  statement: {z : Circle} {s : Real} {n : Nat} (hs : s <= π)
  proof: by
  have hs0 : 0 < s := by
    contrapose! h2
    simp [centeredArc_eq_empty h2]
  have hn0 : n != 0 := by
    contrapose! h1
    simp [h1]
  have hn : 1 <= (n : Real) := by simpa [Nat.one_le_iff_ne_zero]
  rw [mem_centeredArc ((div_le_self hs0.le hn).trans hs)]; rw [lt_div_iff₀' (one_pos.trans_le hn)]
  rw [mem_centeredArc (div_le_self pi_nonneg hn)] at h1
  rwa [mem_centeredArc hs, coe_pow, ← arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle,
    (Angle.nsmul_toReal_eq_mul hn0).mpr (mem_Ioc_of_Ioo ?_), abs_mul, Nat.abs_cast,
    arg_coe_angle_toReal_eq_arg] at h2
  rwa [neg_div, mem_Ioo, ← abs_lt, arg_coe_angle_toReal_eq_arg]

中文:
定理 mem_centeredArc_div
  结论: {z : Circle} {s : 实数} {n : 自然数} (hs : s <= π)
  证明: by
  have hs0 : 0 < s := by
    contrapose! h2
    simp [centeredArc_eq_empty h2]
  have hn0 : n != 0 := by
    contrapose! h1
    simp [h1]
  have hn : 1 <= (n : Real) := by simpa [Nat.one_le_iff_ne_zero]
  rw [mem_centeredArc ((div_le_self hs0.le hn).trans hs)]; rw [lt_div_iff₀' (one_pos.trans_le hn)]
  rw [mem_centeredArc (div_le_self pi_nonneg hn)] at h1
  rwa [mem_centeredArc hs, coe_pow, ← arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle,
    (Angle.nsmul_toReal_eq_mul hn0).mpr (mem_Ioc_of_Ioo ?_), abs_mul, Nat.abs_cast,
    arg_coe_angle_toReal_eq_arg] at h2
  rwa [neg_div, mem_Ioo, ← abs_lt, arg_coe_angle_toReal_eq_arg]

Depends on / 依赖: Angle.nsmul_toReal_eq_mul, Nat.abs_cast, Nat.one_le_iff_ne_zero, abs_cast, abs_mul, arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle, centeredArc_eq_empty, coe_pow, contrapose, div_le_self, hs0.le, mem_Ioc_of_Ioo, mem_centeredArc, nsmul_toReal_eq_mul, one_le_iff_ne_zero, one_pos, one_pos.trans_le, pi_nonneg, trans_le
-/
theorem mem_centeredArc_div {z : Circle} {s : Real} {n : Nat} (hs : s <= π)
    (h1 : z in centeredArc (π / n)) (h2 : z ^ n in centeredArc s) :
    z in centeredArc (s / n) := by
  have hs0 : 0 < s := by
    contrapose! h2
    simp [centeredArc_eq_empty h2]
  have hn0 : n != 0 := by
    contrapose! h1
    simp [h1]
  have hn : 1 <= (n : Real) := by simpa [Nat.one_le_iff_ne_zero]
  rw [mem_centeredArc ((div_le_self hs0.le hn).trans hs)]; rw [lt_div_iff₀' (one_pos.trans_le hn)]
  rw [mem_centeredArc (div_le_self pi_nonneg hn)] at h1
  rwa [mem_centeredArc hs, coe_pow, ← arg_coe_angle_toReal_eq_arg, arg_pow_coe_angle,
    (Angle.nsmul_toReal_eq_mul hn0).mpr (mem_Ioc_of_Ioo ?_), abs_mul, Nat.abs_cast,
    arg_coe_angle_toReal_eq_arg] at h2
  rwa [neg_div, mem_Ioo, ← abs_lt, arg_coe_angle_toReal_eq_arg]

/--
lemma `exp_surjective` / 引理 `exp_surjective`

English:
lemma exp_surjective
  statement: Surjective exp
  proof: fun z => ⟨z.val.arg, exp_arg z⟩

中文:
引理 exp_surjective
  结论: 满射 exp
  证明: fun z => ⟨z.val.arg, exp_arg z⟩

Depends on / 依赖: exp_arg, z.val.arg
-/
lemma exp_surjective : Surjective exp := fun z => ⟨z.val.arg, exp_arg z⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PathConnectedSpace Circle
  body: exp_surjective.pathConnectedSpace exp.continuous

中文:
实例 :
  签名: 道路连通空间 Circle
  定义体: exp_surjective.pathConnectedSpace exp.continuous

Depends on / 依赖: continuous, exp.continuous, exp_surjective, exp_surjective.pathConnectedSpace, pathConnectedSpace
-/
instance : PathConnectedSpace Circle := exp_surjective.pathConnectedSpace exp.continuous

variable {x y : Circle}

/-- Length of the anti-clockwise arc from `x` to `y`. -/
@[grind]
/--
Definition of `angleDiff` / `angleDiff` 的定义

English:
definition angleDiff
  signature: (x y : Circle)
  body: if x.val.arg <= y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]

中文:
定义 angleDiff
  签名: (x y : Circle)
  定义体: if x.val.arg <= y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]

Depends on / 依赖: x.val.arg, y.val.arg
-/
noncomputable def angleDiff (x y : Circle) : Real :=
  if x.val.arg <= y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]
/--
lemma `angleDiff_nonneg` / 引理 `angleDiff_nonneg`

English:
lemma angleDiff_nonneg
  given: (x y : Circle)
  statement: 0 <= angleDiff x y
  proof: by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]

中文:
引理 angleDiff_nonneg
  条件: (x y : Circle)
  结论: 0 <= angleDiff x y
  证明: by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]

Depends on / 依赖: arg_le_pi, neg_pi_lt_arg, x.val, y.val
-/
lemma angleDiff_nonneg (x y : Circle) : 0 <= angleDiff x y := by
  grind [neg_pi_lt_arg y.val, arg_le_pi x.val]

/--
lemma `angleDiff_pos` / 引理 `angleDiff_pos`

English:
lemma angleDiff_pos
  given: (h : x != y)
  statement: 0 < angleDiff x y
  proof: by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]

中文:
引理 angleDiff_pos
  条件: (h : x != y)
  结论: 0 < angleDiff x y
  证明: by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]

Depends on / 依赖: arg_eq_arg, arg_le_pi, neg_pi_lt_arg, x.val, y.val
-/
lemma angleDiff_pos (h : x != y) : 0 < angleDiff x y := by
  grind [arg_eq_arg, neg_pi_lt_arg y.val, arg_le_pi x.val]

/--
lemma `angleDiff_lt_two_pi` / 引理 `angleDiff_lt_two_pi`

English:
lemma angleDiff_lt_two_pi
  given: (x y : Circle)
  statement: angleDiff x y < 2 * π
  proof: by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]

中文:
引理 angleDiff_lt_two_pi
  条件: (x y : Circle)
  结论: angleDiff x y < 2 * π
  证明: by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]

Depends on / 依赖: arg_le_pi, neg_pi_lt_arg, x.val, y.val
-/
lemma angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * π := by
  grind [neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
/--
lemma `angleDiff_add_angleDiff` / 引理 `angleDiff_add_angleDiff`

English:
lemma angleDiff_add_angleDiff
  given: (h : x != y)
  statement: angleDiff x y + angleDiff y x = 2 * π
  proof: by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]

中文:
引理 angleDiff_add_angleDiff
  条件: (h : x != y)
  结论: angleDiff x y + angleDiff y x = 2 * π
  证明: by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]

Depends on / 依赖: arg_eq_arg, arg_le_pi, neg_pi_lt_arg, x.val, y.val
-/
lemma angleDiff_add_angleDiff (h : x != y) : angleDiff x y + angleDiff y x = 2 * π := by
  grind [arg_eq_arg, neg_pi_lt_arg x.val, arg_le_pi y.val]

@[simp]
/--
lemma `exp_angleDiff_mul` / 引理 `exp_angleDiff_mul`

English:
lemma exp_angleDiff_mul
  statement: exp (angleDiff x y) * x = y
  proof: by
  rw [← exp_arg x]; rw [← exp_add]; rw [angleDiff]
  split_ifs with hxy <;> simp

中文:
引理 exp_angleDiff_mul
  结论: exp (angleDiff x y) * x = y
  证明: by
  rw [← exp_arg x]; rw [← exp_add]; rw [angleDiff]
  split_ifs with hxy <;> simp

Depends on / 依赖: angleDiff, exp_add, exp_arg, split_ifs
-/
lemma exp_angleDiff_mul : exp (angleDiff x y) * x = y := by
  rw [← exp_arg x]; rw [← exp_add]; rw [angleDiff]
  split_ifs with hxy <;> simp

/--
lemma `Icc_union_Icc_angleDiff_add_arg` / 引理 `Icc_union_Icc_angleDiff_add_arg`

English:
lemma Icc_union_Icc_angleDiff_add_arg
  given: (h : x != y)
  proof: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

中文:
引理 Icc_union_Icc_angleDiff_add_arg
  条件: (h : x != y)
  证明: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

Depends on / 依赖: arg_eq_arg, arg_lt_arg_add_two_pi
-/
lemma Icc_union_Icc_angleDiff_add_arg (h : x != y) :
    Icc x.val.arg (angleDiff x y + x.val.arg) union Icc y.val.arg (angleDiff y x + y.val.arg) =
    Icc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

/--
lemma `Ico_union_Ico_angleDiff_add_arg` / 引理 `Ico_union_Ico_angleDiff_add_arg`

English:
lemma Ico_union_Ico_angleDiff_add_arg
  given: (h : x != y)
  proof: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

中文:
引理 Ico_union_Ico_angleDiff_add_arg
  条件: (h : x != y)
  证明: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

Depends on / 依赖: arg_eq_arg, arg_lt_arg_add_two_pi
-/
lemma Ico_union_Ico_angleDiff_add_arg (h : x != y) :
    Ico x.val.arg (angleDiff x y + x.val.arg) union Ico y.val.arg (angleDiff y x + y.val.arg) =
    Ico (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

/--
lemma `Ioc_union_Ioc_angleDiff_add_arg` / 引理 `Ioc_union_Ioc_angleDiff_add_arg`

English:
lemma Ioc_union_Ioc_angleDiff_add_arg
  given: (h : x != y)
  proof: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

中文:
引理 Ioc_union_Ioc_angleDiff_add_arg
  条件: (h : x != y)
  证明: by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

Depends on / 依赖: arg_eq_arg, arg_lt_arg_add_two_pi
-/
lemma Ioc_union_Ioc_angleDiff_add_arg (h : x != y) :
    Ioc x.val.arg (angleDiff x y + x.val.arg) union Ioc y.val.arg (angleDiff y x + y.val.arg) =
    Ioc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  grind [arg_eq_arg, arg_lt_arg_add_two_pi y x, arg_lt_arg_add_two_pi x y]

/--
Definition of `path` / `path` 的定义

English:
definition path
  signature: (x y : Circle)
  body: (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
.cast (by simp) (by simp)

@[simp]

中文:
定义 path
  签名: (x y : Circle)
  定义体: (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
.cast (by simp) (by simp)

@[simp]

Depends on / 依赖: Path.segment, angleDiff, continuous, exp.continuous, segment, x.val.arg
-/
noncomputable def path (x y : Circle) : Path x y :=
  (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
.cast (by simp) (by simp)

@[simp]
/--
lemma `path_apply` / 引理 `path_apply`

English:
lemma path_apply
  given: (x y : Circle) (a : unitInterval)
  proof: by
  simp [path]

@[simp]

中文:
引理 path_apply
  条件: (x y : Circle) (a : unit整数erval)
  证明: by
  simp [path]

@[simp]
-/
lemma path_apply (x y : Circle) (a : unitInterval) :
    path x y a = exp (Path.segment x.val.arg (x.angleDiff y + x.val.arg) a) := by
  simp [path]

@[simp]
/--
lemma `coe_path` / 引理 `coe_path`

English:
lemma coe_path
  given: (x y : Circle)
  statement: (path x y : _ -> _) =
  proof: by
  ext t
  rw [path_apply]; rw [comp_apply]

中文:
引理 coe_path
  条件: (x y : Circle)
  结论: (path x y : _ -> _) =
  证明: by
  ext t
  rw [path_apply]; rw [comp_apply]

Depends on / 依赖: comp_apply, path_apply
-/
lemma coe_path (x y : Circle) : (path x y : _ -> _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.angleDiff y + x.val.arg)) := by
  ext t
  rw [path_apply]; rw [comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `path_self` / 引理 `path_self`

English:
lemma path_self
  given: (x : Circle)
  statement: path x x = Path.refl x
  proof: by
  ext a
  simp [path, angleDiff]

中文:
引理 path_self
  条件: (x : Circle)
  结论: path x x = 道路.refl x
  证明: by
  ext a
  simp [path, angleDiff]

Depends on / 依赖: angleDiff
-/
lemma path_self (x : Circle) : path x x = Path.refl x := by
  ext a
  simp [path, angleDiff]

/--
lemma `path_injective_of_ne` / 引理 `path_injective_of_ne`

English:
lemma path_injective_of_ne
  given: (hne : x != y)
  statement: Injective (path x y)
  proof: by
  rw [coe_path]
  refine (exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
 by simp [angleDiff_lt_two_pi]).injective_iff _ ?_ |>.mpr
 Path.segment_injective_of_ne by simp [angleDiff_pos hne |>.ne']
  rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

中文:
引理 path_injective_of_ne
  条件: (hne : x != y)
  结论: 单射 (path x y)
  证明: by
  rw [coe_path]
  refine (exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
 by simp [angleDiff_lt_two_pi]).injective_iff _ ?_ |>.mpr
 Path.segment_injective_of_ne by simp [angleDiff_pos hne |>.ne']
  rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

Depends on / 依赖: Path.range_segment, Path.segment_injective_of_ne, angleDiff, angleDiff_lt_two_pi, angleDiff_pos, coe_path, exp_injOn_Icc, injective_iff, range_segment, segment_eq_Icc, segment_injective_of_ne, x.val.arg
-/
lemma path_injective_of_ne (hne : x != y) : Injective (path x y) := by
  rw [coe_path]
  refine (exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
 by simp [angleDiff_lt_two_pi]).injective_iff _ ?_ |>.mpr
 Path.segment_injective_of_ne by simp [angleDiff_pos hne |>.ne']
  rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

/--
lemma `range_path` / 引理 `range_path`

English:
lemma range_path
  given: (x y : Circle)
  proof: by
  rw [coe_path]; rw [range_comp]; rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

中文:
引理 range_path
  条件: (x y : Circle)
  证明: by
  rw [coe_path]; rw [range_comp]; rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

Depends on / 依赖: Path.range_segment, coe_path, range_comp, range_segment, segment_eq_Icc
-/
lemma range_path (x y : Circle) :
    range (path x y) = exp '' Icc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path]; rw [range_comp]; rw [Path.range_segment]; rw [segment_eq_Icc (by simp)]

/--
lemma `path_image_Ico_of_ne` / 引理 `path_image_Ico_of_ne`

English:
lemma path_image_Ico_of_ne
  given: (h : x != y)
  proof: by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ico (by simp [angleDiff_pos h])]

中文:
引理 path_image_Ico_of_ne
  条件: (h : x != y)
  证明: by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ico (by simp [angleDiff_pos h])]

Depends on / 依赖: angleDiff_pos, coe_path, image_comp, segment_image_Ico
-/
lemma path_image_Ico_of_ne (h : x != y) :
    path x y '' Ico 0 1 = exp '' Ico x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ico (by simp [angleDiff_pos h])]

/--
lemma `path_image_Ioc_of_ne` / 引理 `path_image_Ioc_of_ne`

English:
lemma path_image_Ioc_of_ne
  given: (h : x != y)
  proof: by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ioc (by simp [angleDiff_pos h])]

中文:
引理 path_image_Ioc_of_ne
  条件: (h : x != y)
  证明: by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ioc (by simp [angleDiff_pos h])]

Depends on / 依赖: angleDiff_pos, coe_path, image_comp, segment_image_Ioc
-/
lemma path_image_Ioc_of_ne (h : x != y) :
    path x y '' Ioc 0 1 = exp '' Ioc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path]; rw [image_comp]; rw [segment_image_Ioc (by simp [angleDiff_pos h])]

/--
lemma `range_path_union_range_path` / 引理 `range_path_union_range_path`

English:
lemma range_path_union_range_path
  given: (h : x != y)
  statement: range (path x y) union range (path y x) = univ
  proof: by
  rw [range_path]; rw [range_path]; rw [← image_union]; rw [Icc_union_Icc_angleDiff_add_arg h]; rw [periodic_exp.image_Icc two_pi_pos]
  exact exp_surjective.range_eq

中文:
引理 range_path_union_range_path
  条件: (h : x != y)
  结论: range (path x y) union range (path y x) = univ
  证明: by
  rw [range_path]; rw [range_path]; rw [← image_union]; rw [Icc_union_Icc_angleDiff_add_arg h]; rw [periodic_exp.image_Icc two_pi_pos]
  exact exp_surjective.range_eq

Depends on / 依赖: Icc_union_Icc_angleDiff_add_arg, exp_surjective, exp_surjective.range_eq, image_Icc, image_union, periodic_exp, periodic_exp.image_Icc, range_eq, range_path, two_pi_pos
-/
lemma range_path_union_range_path (h : x != y) : range (path x y) union range (path y x) = univ := by
  rw [range_path]; rw [range_path]; rw [← image_union]; rw [Icc_union_Icc_angleDiff_add_arg h]; rw [periodic_exp.image_Icc two_pi_pos]
  exact exp_surjective.range_eq

/--
lemma `path_image_Ioc_union` / 引理 `path_image_Ioc_union`

English:
lemma path_image_Ioc_union
  given: (h : x != y)
  statement: path x y '' Ioc 0 1 union path y x '' Ioc 0 1 = univ
  proof: by
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]; rw [← image_union]; rw [Ioc_union_Ioc_angleDiff_add_arg h]; rw [periodic_exp.image_Ioc two_pi_pos]
  exact exp_surjective.range_eq

中文:
引理 path_image_Ioc_union
  条件: (h : x != y)
  结论: path x y '' 左开右闭区间 0 1 union path y x '' 左开右闭区间 0 1 = univ
  证明: by
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]; rw [← image_union]; rw [Ioc_union_Ioc_angleDiff_add_arg h]; rw [periodic_exp.image_Ioc two_pi_pos]
  exact exp_surjective.range_eq

Depends on / 依赖: Ioc_union_Ioc_angleDiff_add_arg, exp_surjective, exp_surjective.range_eq, h.symm, image_Ioc, image_union, path_image_Ioc_of_ne, periodic_exp, periodic_exp.image_Ioc, range_eq, two_pi_pos
-/
lemma path_image_Ioc_union (h : x != y) : path x y '' Ioc 0 1 union path y x '' Ioc 0 1 = univ := by
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]; rw [← image_union]; rw [Ioc_union_Ioc_angleDiff_add_arg h]; rw [periodic_exp.image_Ioc two_pi_pos]
  exact exp_surjective.range_eq

/--
lemma `disjoint_path_image_Ioc` / 引理 `disjoint_path_image_Ioc`

English:
lemma disjoint_path_image_Ioc
  given: (h : x != y)
  proof: by
  have hdisj : Disjoint (Ioc x.val.arg (angleDiff x y + x.val.arg))
      (Ioc y.val.arg (angleDiff y x + y.val.arg)) := by grind [angleDiff]
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]
  refine Set.disjoint_image_image fun a ha b hb => ?_
  refine exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * π)
.ne ?_ ?_ hdisj.ne_of_mem ha hb (by simp)
  all_goals
    rw [← Ioc_union_Ioc_angleDiff_add_arg h]
    tauto

中文:
引理 disjoint_path_image_Ioc
  条件: (h : x != y)
  证明: by
  have hdisj : Disjoint (Ioc x.val.arg (angleDiff x y + x.val.arg))
      (Ioc y.val.arg (angleDiff y x + y.val.arg)) := by grind [angleDiff]
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]
  refine Set.disjoint_image_image fun a ha b hb => ?_
  refine exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * π)
.ne ?_ ?_ hdisj.ne_of_mem ha hb (by simp)
  all_goals
    rw [← Ioc_union_Ioc_angleDiff_add_arg h]
    tauto

Depends on / 依赖: Disjoint, Ioc_union_Ioc_angleDiff_add_arg, Set.disjoint_image_image, all_goals, angleDiff, disjoint_image_image, exp_injOn_Ioc, h.symm, hdisj.ne_of_mem, ne_of_mem, path_image_Ioc_of_ne, x.val.arg, y.val.arg
-/
lemma disjoint_path_image_Ioc (h : x != y) :
    Disjoint (path x y '' Ioc 0 1) (path y x '' Ioc 0 1) := by
  have hdisj : Disjoint (Ioc x.val.arg (angleDiff x y + x.val.arg))
      (Ioc y.val.arg (angleDiff y x + y.val.arg)) := by grind [angleDiff]
  rw [path_image_Ioc_of_ne h]; rw [path_image_Ioc_of_ne h.symm]
  refine Set.disjoint_image_image fun a ha b hb => ?_
  refine exp_injOn_Ioc (a := min x.val.arg y.val.arg) (b := min x.val.arg y.val.arg + 2 * π)
.ne ?_ ?_ hdisj.ne_of_mem ha hb (by simp)
  all_goals
    rw [← Ioc_union_Ioc_angleDiff_add_arg h]
    tauto

/--
lemma `compl_path_image_Ioc` / 引理 `compl_path_image_Ioc`

English:
lemma compl_path_image_Ioc
  given: (h : x != y)
  statement: (path x y '' Ioc 0 1)ᶜ = path y x '' Ioc 0 1
  proof: (compl_subset_iff_union.mpr <| path_image_Ioc_union h).antisymm
 (disjoint_path_image_Ioc h.symm).subset_compl_right

中文:
引理 compl_path_image_Ioc
  条件: (h : x != y)
  结论: (path x y '' 左开右闭区间 0 1)ᶜ = path y x '' 左开右闭区间 0 1
  证明: (compl_subset_iff_union.mpr <| path_image_Ioc_union h).antisymm
 (disjoint_path_image_Ioc h.symm).subset_compl_right

Depends on / 依赖: antisymm, compl_subset_iff_union, compl_subset_iff_union.mpr, disjoint_path_image_Ioc, h.symm, path_image_Ioc_union, subset_compl_right
-/
lemma compl_path_image_Ioc (h : x != y) : (path x y '' Ioc 0 1)ᶜ = path y x '' Ioc 0 1 :=
  (compl_subset_iff_union.mpr <| path_image_Ioc_union h).antisymm
 (disjoint_path_image_Ioc h.symm).subset_compl_right

/--
lemma `compl_range_path` / 引理 `compl_range_path`

English:
lemma compl_range_path
  given: (h : x != y)
  statement: (range (path x y))ᶜ = path y x '' Ioo 0 1
  proof: by
  rw [range_path]; rw [← Ioc_insert_left (by simp)]; rw [image_insert_eq]; rw [← path_image_Ioc_of_ne h]; rw [← union_singleton]; rw [compl_union]; rw [compl_path_image_Ioc h]; rw [← Ioo_insert_right (by simp)]; rw [image_insert_eq]; rw [(y.path x).target]; rw [exp_arg]; rw [insert_inter_of_notMem (by simp)]; rw [inter_eq_left]
  rintro z ⟨t, ht, rfl⟩
.trans_eq (y.path x).target exact (path_injective_of_ne h.symm).ne ht.2.ne

中文:
引理 compl_range_path
  条件: (h : x != y)
  结论: (range (path x y))ᶜ = path y x '' 开区间 0 1
  证明: by
  rw [range_path]; rw [← Ioc_insert_left (by simp)]; rw [image_insert_eq]; rw [← path_image_Ioc_of_ne h]; rw [← union_singleton]; rw [compl_union]; rw [compl_path_image_Ioc h]; rw [← Ioo_insert_right (by simp)]; rw [image_insert_eq]; rw [(y.path x).target]; rw [exp_arg]; rw [insert_inter_of_notMem (by simp)]; rw [inter_eq_left]
  rintro z ⟨t, ht, rfl⟩
.trans_eq (y.path x).target exact (path_injective_of_ne h.symm).ne ht.2.ne

Depends on / 依赖: Ioc_insert_left, Ioo_insert_right, compl_path_image_Ioc, compl_union, exp_arg, h.symm, image_insert_eq, insert_inter_of_notMem, inter_eq_left, path_image_Ioc_of_ne, path_injective_of_ne, range_path, target, trans_eq, union_singleton, y.path
-/
lemma compl_range_path (h : x != y) : (range (path x y))ᶜ = path y x '' Ioo 0 1 := by
  rw [range_path]; rw [← Ioc_insert_left (by simp)]; rw [image_insert_eq]; rw [← path_image_Ioc_of_ne h]; rw [← union_singleton]; rw [compl_union]; rw [compl_path_image_Ioc h]; rw [← Ioo_insert_right (by simp)]; rw [image_insert_eq]; rw [(y.path x).target]; rw [exp_arg]; rw [insert_inter_of_notMem (by simp)]; rw [inter_eq_left]
  rintro z ⟨t, ht, rfl⟩
.trans_eq (y.path x).target exact (path_injective_of_ne h.symm).ne ht.2.ne

/--
lemma `range_path_ssubset_univ` / 引理 `range_path_ssubset_univ`

English:
lemma range_path_ssubset_univ
  given: (x y : Circle)
  statement: range (path x y) ⊂ univ
  proof: by
  rw [ssubset_univ_iff_nonempty_compl]
  obtain rfl | hne := eq_or_ne x y
  · use -x, by simp [neg_ne_self]
  rw [compl_range_path hne]
  use y.path x ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
  refine mem_image_of_mem _ ⟨by simp [← unitInterval.coe_pos], unitInterval.coe_lt_one.mp ?_⟩
  linarith

中文:
引理 range_path_ssubset_univ
  条件: (x y : Circle)
  结论: range (path x y) ⊂ univ
  证明: by
  rw [ssubset_univ_iff_nonempty_compl]
  obtain rfl | hne := eq_or_ne x y
  · use -x, by simp [neg_ne_self]
  rw [compl_range_path hne]
  use y.path x ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
  refine mem_image_of_mem _ ⟨by simp [← unitInterval.coe_pos], unitInterval.coe_lt_one.mp ?_⟩
  linarith

Depends on / 依赖: Nat.ofNat_nonneg, coe_lt_one, coe_pos, compl_range_path, eq_or_ne, inv_nonneg, mem_Icc, mem_image_of_mem, neg_ne_self, ofNat_nonneg, ssubset_univ_iff_nonempty_compl, true_and, unitInterval, unitInterval.coe_lt_one.mp, unitInterval.coe_pos, y.path
-/
lemma range_path_ssubset_univ (x y : Circle) : range (path x y) ⊂ univ := by
  rw [ssubset_univ_iff_nonempty_compl]
  obtain rfl | hne := eq_or_ne x y
  · use -x, by simp [neg_ne_self]
  rw [compl_range_path hne]
  use y.path x ⟨2⁻¹, by simp only [mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]; linarith⟩
  refine mem_image_of_mem _ ⟨by simp [← unitInterval.coe_pos], unitInterval.coe_lt_one.mp ?_⟩
  linarith

/--
lemma `range_path_inter_range_path` / 引理 `range_path_inter_range_path`

English:
lemma range_path_inter_range_path
  given: (h : x != y)
  statement: range (path x y) inter range (path y x) = {x, y}
  proof: by
  rw [← image_univ]; rw [← image_univ]; rw [unitInterval.univ_eq_Icc]; rw [← Ioc_insert_left (by simp)]; rw [← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (disjoint_path_image_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind

中文:
引理 range_path_inter_range_path
  条件: (h : x != y)
  结论: range (path x y) inter range (path y x) = {x, y}
  证明: by
  rw [← image_univ]; rw [← image_univ]; rw [unitInterval.univ_eq_Icc]; rw [← Ioc_insert_left (by simp)]; rw [← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (disjoint_path_image_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind

Depends on / 依赖: Disjoint, Ioc_insert_left, Ioo_insert_right, Ioo_subset_Ioc_self, disjoint_path_image_Ioc, image_insert_eq, image_mono, image_univ, simp_rw, unitInterval, unitInterval.univ_eq_Icc, univ_eq_Icc, x.path, y.path
-/
lemma range_path_inter_range_path (h : x != y) : range (path x y) inter range (path y x) = {x, y} := by
  rw [← image_univ]; rw [← image_univ]; rw [unitInterval.univ_eq_Icc]; rw [← Ioc_insert_left (by simp)]; rw [← Ioo_insert_right (by simp)]
  simp_rw [image_insert_eq]
  have h : Disjoint ((x.path y) '' Ioo 0 1) ((y.path x) '' Ioo 0 1) := by
    refine (disjoint_path_image_Ioc h).mono ?_ ?_ <;> exact image_mono Ioo_subset_Ioc_self
  grind

/--
lemma `isPathConnected_compl_singleton` / 引理 `isPathConnected_compl_singleton`

English:
lemma isPathConnected_compl_singleton
  given: (x : Circle)
  statement: IsPathConnected {x}ᶜ
  proof: by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y != x) => ?_⟩
  obtain hxP | hxP := (em (x in range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t => by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x != y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x in range _ inter _ := ⟨hxP, hP₂⟩
    rw [range_path_inter_range_path hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind

中文:
引理 isPathConnected_compl_singleton
  条件: (x : Circle)
  结论: 是道路连通 {x}ᶜ
  证明: by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y != x) => ?_⟩
  obtain hxP | hxP := (em (x in range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t => by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x != y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x in range _ inter _ := ⟨hxP, hP₂⟩
    rw [range_path_inter_range_path hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind

Depends on / 依赖: hyx.symm, neg_ne_self, range_path_inter_range_path
-/
lemma isPathConnected_compl_singleton (x : Circle) : IsPathConnected {x}ᶜ := by
  refine ⟨-x, neg_ne_self x, fun y (hyx : y != x) => ?_⟩
  obtain hxP | hxP := (em (x in range (path (-x) y))).symm
  · exact ⟨(path (-x) y), fun t => by grind⟩
  refine ⟨(path y (-x)).symm, ?_⟩
  have hne : -x != y := by
    rintro rfl
    simp [(neg_ne_self x).symm] at hxP
  have hP₂ : x ∉ range (path y (-x)) := by
    rintro hP₂
    have h : x in range _ inter _ := ⟨hxP, hP₂⟩
    rw [range_path_inter_range_path hne] at h
    simp [(neg_ne_self x).symm, hyx.symm] at h
  grind

/--
lemma `not_isPreconnected_compl_pair` / 引理 `not_isPreconnected_compl_pair`

English:
lemma not_isPreconnected_compl_pair
  given: (hxy : x != y)
  statement: ¬ IsPreconnected {x, y}ᶜ
  proof: by
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, exists_and_left]
  refine ⟨range (path x y), ?_, range (path y x), (isCompact_range (path x y).continuous).isClosed,
    (isCompact_range (path y x).continuous).isClosed, ?_, ?_, ?_⟩
  · rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path x y).source_mem_range, (path x y).target_mem_range, and_self])]
    exact (range_path_ssubset_univ x y).ne
  · rw [range_path_union_range_path hxy]
    exact subset_univ _
  · rw [range_path_inter_range_path hxy]
    exact compl_inter_self {x, y}
  rw [compl_subset_iff_union]; rw [union_eq_right.mpr (by simp only [pair_subset_iff]; rw [(path y x).source_mem_range]; rw [(path y x).target_mem_range]; rw [and_self])]
  exact (range_path_ssubset_univ y x).ne

中文:
引理 not_isPreconnected_compl_pair
  条件: (hxy : x != y)
  结论: ¬ 是预连通 {x, y}ᶜ
  证明: by
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, exists_and_left]
  refine ⟨range (path x y), ?_, range (path y x), (isCompact_range (path x y).continuous).isClosed,
    (isCompact_range (path y x).continuous).isClosed, ?_, ?_, ?_⟩
  · rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path x y).source_mem_range, (path x y).target_mem_range, and_self])]
    exact (range_path_ssubset_univ x y).ne
  · rw [range_path_union_range_path hxy]
    exact subset_univ _
  · rw [range_path_inter_range_path hxy]
    exact compl_inter_self {x, y}
  rw [compl_subset_iff_union]; rw [union_eq_right.mpr (by simp only [pair_subset_iff]; rw [(path y x).source_mem_range]; rw [(path y x).target_mem_range]; rw [and_self])]
  exact (range_path_ssubset_univ y x).ne

Depends on / 依赖: and_self, compl_subset_iff_union, continuous, exists_and_left, isClosed, isCompact_range, isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, pair_subset_iff, range_path_ssubset_univ, range_path_union_range_path, source_mem_range, subset_u, target_mem_range, union_eq_right, union_eq_right.mpr
-/
lemma not_isPreconnected_compl_pair (hxy : x != y) : ¬ IsPreconnected {x, y}ᶜ := by
  simp only [isPreconnected_iff_subset_of_disjoint_closed, not_forall, not_or, exists_and_left]
  refine ⟨range (path x y), ?_, range (path y x), (isCompact_range (path x y).continuous).isClosed,
    (isCompact_range (path y x).continuous).isClosed, ?_, ?_, ?_⟩
  · rw [compl_subset_iff_union, union_eq_right.mpr (by simp only [pair_subset_iff,
      (path x y).source_mem_range, (path x y).target_mem_range, and_self])]
    exact (range_path_ssubset_univ x y).ne
  · rw [range_path_union_range_path hxy]
    exact subset_univ _
  · rw [range_path_inter_range_path hxy]
    exact compl_inter_self {x, y}
  rw [compl_subset_iff_union]; rw [union_eq_right.mpr (by simp only [pair_subset_iff]; rw [(path y x).source_mem_range]; rw [(path y x).target_mem_range]; rw [and_self])]
  exact (range_path_ssubset_univ y x).ne

end Circle

namespace Real.Angle

/--
Definition of `toCircle` / `toCircle` 的定义

English:
definition toCircle
  signature: (θ : Angle)
  body: Circle.periodic_exp.lift θ

中文:
定义 toCircle
  签名: (θ : Angle)
  定义体: Circle.periodic_exp.lift θ

Depends on / 依赖: Circle, Circle.periodic_exp.lift, periodic_exp
-/
noncomputable def toCircle (θ : Angle) : Circle := Circle.periodic_exp.lift θ

/--
lemma `toCircle_coe` / 引理 `toCircle_coe`

English:
lemma toCircle_coe
  given: (x : Real)
  statement: toCircle x = .exp x
  proof: rfl

中文:
引理 toCircle_coe
  条件: (x : 实数)
  结论: toCircle x = .exp x
  证明: rfl
-/
@[simp] lemma toCircle_coe (x : Real) : toCircle x = .exp x := rfl

/--
lemma `coe_toCircle` / 引理 `coe_toCircle`

English:
lemma coe_toCircle
  given: (θ : Angle)
  statement: (θ.toCircle : Complex) = θ.cos + θ.sin * I
  proof: by
  induction θ using Angle.induction_on
  simp [exp_mul_I]

中文:
引理 coe_toCircle
  条件: (θ : Angle)
  结论: (θ.toCircle : 复形) = θ.cos + θ.sin * I
  证明: by
  induction θ using Angle.induction_on
  simp [exp_mul_I]

Depends on / 依赖: Angle.induction_on, exp_mul_I, induction_on
-/
lemma coe_toCircle (θ : Angle) : (θ.toCircle : Complex) = θ.cos + θ.sin * I := by
  induction θ using Angle.induction_on
  simp [exp_mul_I]

/--
lemma `toCircle_zero` / 引理 `toCircle_zero`

English:
lemma toCircle_zero
  statement: toCircle 0 = 1
  proof: by rw [← coe_zero, toCircle_coe, Circle.exp_zero]

中文:
引理 toCircle_zero
  结论: toCircle 0 = 1
  证明: by rw [← coe_zero, toCircle_coe, Circle.exp_zero]
-/
@[simp] lemma toCircle_zero : toCircle 0 = 1 := by rw [← coe_zero, toCircle_coe, Circle.exp_zero]

/--
lemma `toCircle_neg` / 引理 `toCircle_neg`

English:
lemma toCircle_neg
  given: (θ : Angle)
  statement: toCircle (-θ) = (toCircle θ)⁻¹
  proof: by
  induction θ using Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]

中文:
引理 toCircle_neg
  条件: (θ : Angle)
  结论: toCircle (-θ) = (toCircle θ)⁻¹
  证明: by
  induction θ using Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]
-/
@[simp] lemma toCircle_neg (θ : Angle) : toCircle (-θ) = (toCircle θ)⁻¹ := by
  induction θ using Angle.induction_on
  simp_rw [← coe_neg, toCircle_coe, Circle.exp_neg]

/--
lemma `toCircle_add` / 引理 `toCircle_add`

English:
lemma toCircle_add
  given: (θ₁ θ₂ : Angle)
  statement: toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂
  proof: by
  induction θ₁ using Angle.induction_on
  induction θ₂ using Angle.induction_on
  exact Circle.exp_add _ _

中文:
引理 toCircle_add
  条件: (θ₁ θ₂ : Angle)
  结论: toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂
  证明: by
  induction θ₁ using Angle.induction_on
  induction θ₂ using Angle.induction_on
  exact Circle.exp_add _ _
-/
@[simp] lemma toCircle_add (θ₁ θ₂ : Angle) : toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂ := by
  induction θ₁ using Angle.induction_on
  induction θ₂ using Angle.induction_on
  exact Circle.exp_add _ _

/--
lemma `arg_toCircle` / 引理 `arg_toCircle`

English:
lemma arg_toCircle
  given: (θ : Angle)
  statement: (arg θ.toCircle : Angle) = θ
  proof: by
  induction θ using Angle.induction_on
  rw [toCircle_coe]; rw [Circle.coe_exp]; rw [exp_mul_I]; rw [← ofReal_cos]; rw [← ofReal_sin]; rw [←
    Angle.cos_coe]; rw [← Angle.sin_coe]; rw [arg_cos_add_sin_mul_I_coe_angle]

中文:
引理 arg_toCircle
  条件: (θ : Angle)
  结论: (arg θ.toCircle : Angle) = θ
  证明: by
  induction θ using Angle.induction_on
  rw [toCircle_coe]; rw [Circle.coe_exp]; rw [exp_mul_I]; rw [← ofReal_cos]; rw [← ofReal_sin]; rw [←
    Angle.cos_coe]; rw [← Angle.sin_coe]; rw [arg_cos_add_sin_mul_I_coe_angle]
-/
@[simp] lemma arg_toCircle (θ : Angle) : (arg θ.toCircle : Angle) = θ := by
  induction θ using Angle.induction_on
  rw [toCircle_coe]; rw [Circle.coe_exp]; rw [exp_mul_I]; rw [← ofReal_cos]; rw [← ofReal_sin]; rw [←
    Angle.cos_coe]; rw [← Angle.sin_coe]; rw [arg_cos_add_sin_mul_I_coe_angle]

end Real.Angle

namespace AddCircle

variable {T : Real}


/--
theorem `scaled_exp_map_periodic` / 定理 `scaled_exp_map_periodic`

English:
theorem scaled_exp_map_periodic
  statement: Function.Periodic (fun x => Circle.exp (2 * π / T * x)) T
  proof: by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]

中文:
定理 scaled_exp_map_periodic
  结论: 函数.周期 (fun x => Circle.exp (2 * π / T * x)) T
  证明: by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]
-/
theorem scaled_exp_map_periodic : Function.Periodic (fun x => Circle.exp (2 * π / T * x)) T := by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · simp
  · intro x; simp_rw [mul_add]; rw [div_mul_cancel₀ _ hT, Circle.periodic_exp]

/--
Definition of `toCircle` / `toCircle` 的定义

English:
definition toCircle
  signature: : AddCircle T -> Circle
  body: (@scaled_exp_map_periodic T).lift

中文:
定义 toCircle
  签名: : AddCircle T -> Circle
  定义体: (@scaled_exp_map_periodic T).lift

Depends on / 依赖: scaled_exp_map_periodic
-/
noncomputable def toCircle : AddCircle T -> Circle :=
  (@scaled_exp_map_periodic T).lift

/--
theorem `toCircle_apply_mk` / 定理 `toCircle_apply_mk`

English:
theorem toCircle_apply_mk
  given: (x : Real)
  statement: @toCircle T x = Circle.exp (2 * π / T * x)
  proof: rfl

中文:
定理 toCircle_apply_mk
  条件: (x : 实数)
  结论: @toCircle T x = Circle.exp (2 * π / T * x)
  证明: rfl
-/
theorem toCircle_apply_mk (x : Real) : @toCircle T x = Circle.exp (2 * π / T * x) :=
  rfl

/--
theorem `toCircle_add` / 定理 `toCircle_add`

English:
theorem toCircle_add
  given: (x y : AddCircle T)
  statement: toCircle (x + y) = toCircle x * toCircle y
  proof: by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, Circle.exp_add]

中文:
定理 toCircle_add
  条件: (x y : AddCircle T)
  结论: toCircle (x + y) = toCircle x * toCircle y
  证明: by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, Circle.exp_add]

Depends on / 依赖: Circle, Circle.exp_add, QuotientAddGroup, QuotientAddGroup.induction_on, coe_add, exp_add, induction_on, mul_add, simp_rw, toCircle_apply_mk
-/
theorem toCircle_add (x y : AddCircle T) : toCircle (x + y) = toCircle x * toCircle y := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  simp_rw [← coe_add, toCircle_apply_mk, mul_add, Circle.exp_add]

/--
lemma `toCircle_zero` / 引理 `toCircle_zero`

English:
lemma toCircle_zero
  statement: toCircle (0 : AddCircle T) = 1
  proof: by
  rw [← QuotientAddGroup.mk_zero]; rw [toCircle_apply_mk]; rw [mul_zero]; rw [Circle.exp_zero]

中文:
引理 toCircle_zero
  结论: toCircle (0 : AddCircle T) = 1
  证明: by
  rw [← QuotientAddGroup.mk_zero]; rw [toCircle_apply_mk]; rw [mul_zero]; rw [Circle.exp_zero]
-/
@[simp] lemma toCircle_zero : toCircle (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero]; rw [toCircle_apply_mk]; rw [mul_zero]; rw [Circle.exp_zero]

/--
theorem `toCircle_neg` / 定理 `toCircle_neg`

English:
theorem toCircle_neg
  given: (x : AddCircle T)
  statement: toCircle (-x) = (toCircle x)⁻¹
  proof: (mul_left_inj (toCircle x)).mp by simp [← toCircle_add]

中文:
定理 toCircle_neg
  条件: (x : AddCircle T)
  结论: toCircle (-x) = (toCircle x)⁻¹
  证明: (mul_left_inj (toCircle x)).mp by simp [← toCircle_add]

Depends on / 依赖: mul_left_inj, toCircle, toCircle_add
-/
theorem toCircle_neg (x : AddCircle T) : toCircle (-x) = (toCircle x)⁻¹ :=
(mul_left_inj (toCircle x)).mp by simp [← toCircle_add]

/--
theorem `toCircle_nsmul` / 定理 `toCircle_nsmul`

English:
theorem toCircle_nsmul
  given: (x : AddCircle T) (n : Nat)
  statement: toCircle (n • x) = toCircle x ^ n
  proof: by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, toCircle_add, ih, pow_succ]

中文:
定理 toCircle_nsmul
  条件: (x : AddCircle T) (n : 自然数)
  结论: toCircle (n • x) = toCircle x ^ n
  证明: by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, toCircle_add, ih, pow_succ]

Depends on / 依赖: pow_succ, succ_nsmul, toCircle_add
-/
theorem toCircle_nsmul (x : AddCircle T) (n : Nat) : toCircle (n • x) = toCircle x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, toCircle_add, ih, pow_succ]

/--
theorem `toCircle_zsmul` / 定理 `toCircle_zsmul`

English:
theorem toCircle_zsmul
  given: (x : AddCircle T) (n : Int)
  statement: toCircle (n • x) = toCircle x ^ n
  proof: by
  cases n <;> simp [toCircle_nsmul, toCircle_neg]

@[fun_prop, continuity]

中文:
定理 toCircle_zsmul
  条件: (x : AddCircle T) (n : 整数)
  结论: toCircle (n • x) = toCircle x ^ n
  证明: by
  cases n <;> simp [toCircle_nsmul, toCircle_neg]

@[fun_prop, continuity]

Depends on / 依赖: toCircle_neg, toCircle_nsmul
-/
theorem toCircle_zsmul (x : AddCircle T) (n : Int) : toCircle (n • x) = toCircle x ^ n := by
  cases n <;> simp [toCircle_nsmul, toCircle_neg]

@[fun_prop, continuity]
/--
theorem `continuous_toCircle` / 定理 `continuous_toCircle`

English:
theorem continuous_toCircle
  statement: Continuous (@toCircle T)
  proof: continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)

中文:
定理 continuous_toCircle
  结论: 连续 (@toCircle T)
  证明: continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)

Depends on / 依赖: Circle, Circle.exp.continuous.comp, continuous, continuous_coinduced_dom, continuous_coinduced_dom.mpr, fun_prop
-/
theorem continuous_toCircle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (Circle.exp.continuous.comp <| by fun_prop)

/--
theorem `injective_toCircle` / 定理 `injective_toCircle`

English:
theorem injective_toCircle
  given: (hT : T != 0)
  statement: Function.Injective (@toCircle T)
  proof: by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith

中文:
定理 injective_toCircle
  条件: (hT : T != 0)
  结论: 函数.单射 (@toCircle T)
  证明: by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, Circle, Circle.exp_eq_exp.mp, QuotientAddGroup, QuotientAddGroup.eq, QuotientAddGroup.induction_on, exp_eq_exp, h.symm, induction_on, mem_zmultiples_iff, simp_rw, toCircle_apply_mk, zsmul_eq_mul
-/
theorem injective_toCircle (hT : T != 0) : Function.Injective (@toCircle T) := by
  intro a b h
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  simp_rw [toCircle_apply_mk] at h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h.symm
  rw [QuotientAddGroup.eq]; simp_rw [AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp at hm
  linarith

/--
Definition of `homeomorphCircle'` / `homeomorphCircle'` 的定义

English:
definition homeomorphCircle'
  signature: : AddCircle (2 * π) ≃ₜ Circle where
  body: Angle.toCircle
  invFun := fun x => arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val

中文:
定义 homeomorphCircle'
  签名: : AddCircle (2 * π) ≃ₜ Circle where
  定义体: Angle.toCircle
  invFun := fun x => arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val
-/
@[simps] noncomputable def homeomorphCircle' : AddCircle (2 * π) ≃ₜ Circle where
  toFun := Angle.toCircle
  invFun := fun x => arg x
  left_inv := Angle.arg_toCircle
  right_inv := Circle.exp_arg
  continuous_toFun := continuous_coinduced_dom.mpr Circle.exp.continuous
  continuous_invFun := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (continuousAt_arg_coe_angle x.coe_ne_zero).comp continuousAt_subtype_val

/--
theorem `homeomorphCircle'_apply_mk` / 定理 `homeomorphCircle'_apply_mk`

English:
theorem homeomorphCircle'_apply_mk
  given: (x : Real)
  statement: homeomorphCircle' x = Circle.exp x
  proof: rfl

中文:
定理 homeomorphCircle'_apply_mk
  条件: (x : 实数)
  结论: homeomorphCircle' x = Circle.exp x
  证明: rfl
-/
theorem homeomorphCircle'_apply_mk (x : Real) : homeomorphCircle' x = Circle.exp x := rfl

/--
Definition of `homeomorphCircle` / `homeomorphCircle` 的定义

English:
definition homeomorphCircle
  signature: (hT : T != 0)
  body: (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'

中文:
定义 homeomorphCircle
  签名: (hT : T != 0)
  定义体: (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'

Depends on / 依赖: homeomorphAddCircle, homeomorphCircle
-/
noncomputable def homeomorphCircle (hT : T != 0) : AddCircle T ≃ₜ Circle :=
  (homeomorphAddCircle T (2 * π) hT (by positivity)).trans homeomorphCircle'

/--
theorem `homeomorphCircle_apply` / 定理 `homeomorphCircle_apply`

English:
theorem homeomorphCircle_apply
  given: (hT : T != 0) (x : AddCircle T)
  proof: by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle]; rw [Homeomorph.trans_apply]; rw [homeomorphAddCircle_apply_mk]; rw [homeomorphCircle'_apply_mk]; rw [toCircle_apply_mk]
  ring_nf

中文:
定理 homeomorphCircle_apply
  条件: (hT : T != 0) (x : AddCircle T)
  证明: by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle]; rw [Homeomorph.trans_apply]; rw [homeomorphAddCircle_apply_mk]; rw [homeomorphCircle'_apply_mk]; rw [toCircle_apply_mk]
  ring_nf

Depends on / 依赖: Homeomorph, Homeomorph.trans_apply, QuotientAddGroup, QuotientAddGroup.induction_on, _apply_mk, homeomorphAddCircle_apply_mk, homeomorphCircle, induction_on, ring_nf, toCircle_apply_mk, trans_apply
-/
theorem homeomorphCircle_apply (hT : T != 0) (x : AddCircle T) :
    homeomorphCircle hT x = toCircle x := by
  cases x using QuotientAddGroup.induction_on
  rw [homeomorphCircle]; rw [Homeomorph.trans_apply]; rw [homeomorphAddCircle_apply_mk]; rw [homeomorphCircle'_apply_mk]; rw [toCircle_apply_mk]
  ring_nf

end AddCircle

open AddCircle

/--
theorem `Circle.isAddQuotientCoveringMap_exp` / 定理 `Circle.isAddQuotientCoveringMap_exp`

English:
theorem Circle.isAddQuotientCoveringMap_exp
  proof: by
  convert! (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]

中文:
定理 Circle.isAddQuotientCoveringMap_exp
  证明: by
  convert! (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]

Depends on / 依赖: convert, homeomorphCircle, homeomorphCircle_apply, homeomorph_comp, isAddQuotientCoveringMap_coe, on_goal, toCircle
-/
theorem Circle.isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap exp (AddSubgroup.zmultiples (2 * π)) := by
  convert! (isAddQuotientCoveringMap_coe _).homeomorph_comp (homeomorphCircle _)
  on_goal 2 => simp
  ext; simp [homeomorphCircle_apply, toCircle]

/--
theorem `Circle.isCoveringMap_exp` / 定理 `Circle.isCoveringMap_exp`

English:
theorem Circle.isCoveringMap_exp
  statement: IsCoveringMap exp
  proof: isAddQuotientCoveringMap_exp.isCoveringMap

中文:
定理 Circle.isCoveringMap_exp
  结论: IsCoveringMap exp
  证明: isAddQuotientCoveringMap_exp.isCoveringMap

Depends on / 依赖: isAddQuotientCoveringMap_exp, isAddQuotientCoveringMap_exp.isCoveringMap, isCoveringMap
-/
theorem Circle.isCoveringMap_exp : IsCoveringMap exp := isAddQuotientCoveringMap_exp.isCoveringMap

/--
lemma `isLocalHomeomorph_circleExp` / 引理 `isLocalHomeomorph_circleExp`

English:
lemma isLocalHomeomorph_circleExp
  statement: IsLocalHomeomorph Circle.exp
  proof: Circle.isCoveringMap_exp.isLocalHomeomorph

中文:
引理 isLocalHomeomorph_circleExp
  结论: IsLocalHomeomorph Circle.exp
  证明: Circle.isCoveringMap_exp.isLocalHomeomorph

Depends on / 依赖: Circle, Circle.isCoveringMap_exp.isLocalHomeomorph, isCoveringMap_exp, isLocalHomeomorph
-/
lemma isLocalHomeomorph_circleExp : IsLocalHomeomorph Circle.exp :=
  Circle.isCoveringMap_exp.isLocalHomeomorph

/--
theorem `Circle.hasBasis_centeredArc_div_two_pow` / 定理 `Circle.hasBasis_centeredArc_div_two_pow`

English:
theorem Circle.hasBasis_centeredArc_div_two_pow
  proof: by
  rw [← Circle.exp_zero]; rw [← isLocalHomeomorph_circleExp.map_nhds_eq 0]
  simp_rw [centeredArc, abs_lt, Set.Ioo_def, ← Real.ball_zero_eq_Ioo]
  apply Filter.HasBasis.map
refine nhds_basis_uniformity Metric.mk_uniformity_basis_of_tendsto (l := Filter.atTop)
    (fun _ _ => by positivity) (by simp) ?_
  simp_rw [div_eq_mul_inv, pow_succ, mul_inv_rev, ← mul_assoc]
  rw [← mul_zero (π * 2⁻¹)]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
.const_mul _

中文:
定理 Circle.hasBasis_centeredArc_div_two_pow
  证明: by
  rw [← Circle.exp_zero]; rw [← isLocalHomeomorph_circleExp.map_nhds_eq 0]
  simp_rw [centeredArc, abs_lt, Set.Ioo_def, ← Real.ball_zero_eq_Ioo]
  apply Filter.HasBasis.map
refine nhds_basis_uniformity Metric.mk_uniformity_basis_of_tendsto (l := Filter.atTop)
    (fun _ _ => by positivity) (by simp) ?_
  simp_rw [div_eq_mul_inv, pow_succ, mul_inv_rev, ← mul_assoc]
  rw [← mul_zero (π * 2⁻¹)]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
.const_mul _

Depends on / 依赖: Circle, Circle.exp_zero, Filter, Filter.HasBasis.map, Filter.atTop, HasBasis, Ioo_def, Metric, Metric.mk_uniformity_basis_of_tendsto, Real.ball_zero_eq_Ioo, Set.Ioo_def, abs_lt, ball_zero_eq_Ioo, centeredArc, const_mul, div_eq_mul_inv, exp_zero, isLocalHomeomorph_circleExp, isLocalHomeomorph_circleExp.map_nhds_eq, map_nhds_eq
-/
theorem Circle.hasBasis_centeredArc_div_two_pow :
    (nhds (1 : Circle)).HasBasis (fun _ => True) (fun n => centeredArc (π / 2 ^ (n + 1))) := by
  rw [← Circle.exp_zero]; rw [← isLocalHomeomorph_circleExp.map_nhds_eq 0]
  simp_rw [centeredArc, abs_lt, Set.Ioo_def, ← Real.ball_zero_eq_Ioo]
  apply Filter.HasBasis.map
refine nhds_basis_uniformity Metric.mk_uniformity_basis_of_tendsto (l := Filter.atTop)
    (fun _ _ => by positivity) (by simp) ?_
  simp_rw [div_eq_mul_inv, pow_succ, mul_inv_rev, ← mul_assoc]
  rw [← mul_zero (π * 2⁻¹)]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
.const_mul _

/--
theorem `Circle.isOpen_centeredArc` / 定理 `Circle.isOpen_centeredArc`

English:
theorem Circle.isOpen_centeredArc
  given: (r : Real)
  statement: IsOpen (centeredArc r)
  proof: by
  have hset : {x : Real | |x| < r} = Ioo (-r) r := by
    ext x
    simp [abs_lt]
  simpa [centeredArc, hset] using
    isLocalHomeomorph_circleExp.isOpenMap (Ioo (-r) r) isOpen_Ioo

中文:
定理 Circle.isOpen_centeredArc
  条件: (r : 实数)
  结论: 是开集 (centeredArc r)
  证明: by
  have hset : {x : Real | |x| < r} = Ioo (-r) r := by
    ext x
    simp [abs_lt]
  simpa [centeredArc, hset] using
    isLocalHomeomorph_circleExp.isOpenMap (Ioo (-r) r) isOpen_Ioo

Depends on / 依赖: abs_lt, centeredArc, isLocalHomeomorph_circleExp, isLocalHomeomorph_circleExp.isOpenMap, isOpenMap, isOpen_Ioo
-/
theorem Circle.isOpen_centeredArc (r : Real) : IsOpen (centeredArc r) := by
  have hset : {x : Real | |x| < r} = Ioo (-r) r := by
    ext x
    simp [abs_lt]
  simpa [centeredArc, hset] using
    isLocalHomeomorph_circleExp.isOpenMap (Ioo (-r) r) isOpen_Ioo

/--
theorem `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` / 定理 `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two`

English:
theorem Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  statement: {z : Circle}
  proof: by
  have hz1 : z in centeredArc (π / 2) := by simpa using hz 1
  have h (n : Nat) : z in centeredArc (π / 2 ^ (n + 1)) := by
    induction n with
    | zero => simpa using hz1
    | succ n ih =>
        simpa [div_div, ← pow_succ'] using mem_centeredArc_div
          (div_le_self pi_nonneg one_le_two) (by simpa) (hz (2 ^ (n + 1)) (by positivity))
  simpa [h] using Set.ext_iff.mp hasBasis_centeredArc_div_two_pow.ker z

中文:
定理 Circle.eq_one_of_对任意_pow_mem_centeredArc_pi_div_two
  结论: {z : Circle}
  证明: by
  have hz1 : z in centeredArc (π / 2) := by simpa using hz 1
  have h (n : Nat) : z in centeredArc (π / 2 ^ (n + 1)) := by
    induction n with
    | zero => simpa using hz1
    | succ n ih =>
        simpa [div_div, ← pow_succ'] using mem_centeredArc_div
          (div_le_self pi_nonneg one_le_two) (by simpa) (hz (2 ^ (n + 1)) (by positivity))
  simpa [h] using Set.ext_iff.mp hasBasis_centeredArc_div_two_pow.ker z

Depends on / 依赖: Set.ext_iff.mp, centeredArc, div_div, div_le_self, ext_iff, hasBasis_centeredArc_div_two_pow, hasBasis_centeredArc_div_two_pow.ker, mem_centeredArc_div, one_le_two, pi_nonneg, pow_succ
-/
theorem Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two {z : Circle}
    (hz : forall n > 0, z ^ n in centeredArc (π / 2)) : z = 1 := by
  have hz1 : z in centeredArc (π / 2) := by simpa using hz 1
  have h (n : Nat) : z in centeredArc (π / 2 ^ (n + 1)) := by
    induction n with
    | zero => simpa using hz1
    | succ n ih =>
        simpa [div_div, ← pow_succ'] using mem_centeredArc_div
          (div_le_self pi_nonneg one_le_two) (by simpa) (hz (2 ^ (n + 1)) (by positivity))
  simpa [h] using Set.ext_iff.mp hasBasis_centeredArc_div_two_pow.ker z

/--
theorem `Circle.isQuotientCoveringMap_zpow` / 定理 `Circle.isQuotientCoveringMap_zpow`

English:
theorem Circle.isQuotientCoveringMap_zpow
  given: (n : Int) [NeZero n]
  proof: by
  have hn : IsUnit (n : Real) := by simpa using NeZero.ne n
  let e := AddCircle.homeomorphCircle one_ne_zero
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := zpowGroupHom (α := Circle) n) ?_ (Set.Finite.isDiscrete <| .of_preimage ?_ e.surjective)
  · refine .of_comp e.continuous (continuous_zpow n) ?_
    convert!
e.isQuotientMap.comp
        IsUnit.isQuotientMap_zsmul (M := Real) (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : Real)))
          isQuotientMap_quotient_mk' n hn
    ext; simp [zpowGroupHom, e, homeomorphCircle_apply, toCircle_zsmul]
  · convert! finite_torsion_of_isSMulRegular_int (1 : Real) n fun _ => by simp [NeZero.ne]
    ext
    simp [e, homeomorphCircle_apply, ← toCircle_zsmul, ← (injective_toCircle one_ne_zero).eq_iff]

中文:
定理 Circle.isQuotientCoveringMap_zpow
  条件: (n : 整数) [NeZero n]
  证明: by
  have hn : IsUnit (n : Real) := by simpa using NeZero.ne n
  let e := AddCircle.homeomorphCircle one_ne_zero
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := zpowGroupHom (α := Circle) n) ?_ (Set.Finite.isDiscrete <| .of_preimage ?_ e.surjective)
  · refine .of_comp e.continuous (continuous_zpow n) ?_
    convert!
e.isQuotientMap.comp
        IsUnit.isQuotientMap_zsmul (M := Real) (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : Real)))
          isQuotientMap_quotient_mk' n hn
    ext; simp [zpowGroupHom, e, homeomorphCircle_apply, toCircle_zsmul]
  · convert! finite_torsion_of_isSMulRegular_int (1 : Real) n fun _ => by simp [NeZero.ne]
    ext
    simp [e, homeomorphCircle_apply, ← toCircle_zsmul, ← (injective_toCircle one_ne_zero).eq_iff]

Depends on / 依赖: AddCircle, AddCircle.homeomorphCircle, AddSubgroup, AddSubgroup.zmultiples, Circle, Finite, IsQuotientMap, IsUnit, IsUnit.isQuotientMap_zsmul, NeZero, NeZero.ne, QuotientAddGroup, QuotientAddGroup.mk, Set.Finite.isDiscrete, Topology, Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom, continuous, continuous_zpow, convert, e.continuous
-/
theorem Circle.isQuotientCoveringMap_zpow (n : Int) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle -> _) (zpowGroupHom (α := Circle) n).ker := by
  have hn : IsUnit (n : Real) := by simpa using NeZero.ne n
  let e := AddCircle.homeomorphCircle one_ne_zero
  refine Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f := zpowGroupHom (α := Circle) n) ?_ (Set.Finite.isDiscrete <| .of_preimage ?_ e.surjective)
  · refine .of_comp e.continuous (continuous_zpow n) ?_
    convert!
e.isQuotientMap.comp
        IsUnit.isQuotientMap_zsmul (M := Real) (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : Real)))
          isQuotientMap_quotient_mk' n hn
    ext; simp [zpowGroupHom, e, homeomorphCircle_apply, toCircle_zsmul]
  · convert! finite_torsion_of_isSMulRegular_int (1 : Real) n fun _ => by simp [NeZero.ne]
    ext
    simp [e, homeomorphCircle_apply, ← toCircle_zsmul, ← (injective_toCircle one_ne_zero).eq_iff]

/--
theorem `Circle.isQuotientCoveringMap_npow` / 定理 `Circle.isQuotientCoveringMap_npow`

English:
theorem Circle.isQuotientCoveringMap_npow
  given: (n : Nat) [NeZero n]
  proof: isQuotientCoveringMap_zpow n

中文:
定理 Circle.isQuotientCoveringMap_npow
  条件: (n : 自然数) [NeZero n]
  证明: isQuotientCoveringMap_zpow n

Depends on / 依赖: Circle, CochainComplex, CochainComplex.single, F.map_comp, Functor, Functor.mapHomologicalComplex_map_f, HomologicalComplex, HomologicalComplex.cyclesMap_i, HomologicalComplex.iCycles, _comp_iCycles, _comp_iCycles_assoc, cancel_mono, cyclesMap_i, iCycles, mapHomologicalComplex_map_f, map_comp, toRightDerivedZero
-/
theorem Circle.isQuotientCoveringMap_npow (n : Nat) [NeZero n] :
    IsQuotientCoveringMap (· ^ n : Circle -> _) (powMonoidHom (α := Circle) n).ker :=
  isQuotientCoveringMap_zpow n
