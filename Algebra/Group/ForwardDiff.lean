/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler, Yu Shao, Weijie Jiang, BeiBei Xiong
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Forward difference operators and Newton series

We define the forward difference operator, sending `f` to the function `x ↦ f (x + h) - f x` for
a given `h` (for any additive semigroup, taking values in an abelian group). The notation `Δ_[h]` is
defined for this operator, scoped in namespace `fwdDiff`.

We prove two key formulae about this operator:

* `shift_eq_sum_fwdDiff_iter`: the **Gregory-Newton formula**, expressing `f (y + n • h)` as a
  linear combination of forward differences of `f` at `y`, for `n ∈ ℕ`;
* `fwdDiff_iter_eq_sum_shift`: formula expressing the `n`-th forward difference of `f` at `y` as
  a linear combination of `f (y + k • h)` for `0 ≤ k ≤ n`.

We also prove some auxiliary results about iterated forward differences of the function
`n ↦ n.choose k`.
-/

@[expose] public section

open Finset Nat Function Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

/--
Definition of `fwdDiff` / `fwdDiff` 的定义

English:
definition fwdDiff
  signature: (h : M) (f : M -> G)
  body: fun n => f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h

中文:
定义 fwdDiff
  签名: (h : M) (f : M -> G)
  定义体: fun n => f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h
-/
def fwdDiff (h : M) (f : M -> G) : M -> G := fun n => f (n + h) - f n

@[inherit_doc] scoped[fwdDiff] notation "Δ_[" h "]" => fwdDiff h

open fwdDiff

/--
lemma `fwdDiff_add` / 引理 `fwdDiff_add`

English:
lemma fwdDiff_add
  given: (h : M) (f g : M -> G)
  proof: add_sub_add_comm ..

中文:
引理 fwdDiff_add
  条件: (h : M) (f g : M -> G)
  证明: add_sub_add_comm ..
-/
@[simp] lemma fwdDiff_add (h : M) (f g : M -> G) :
    Δ_[h] (f + g) = Δ_[h] f + Δ_[h] g :=
  add_sub_add_comm ..

/--
lemma `fwdDiff_const` / 引理 `fwdDiff_const`

English:
lemma fwdDiff_const
  given: (g : G)
  statement: Δ_[h] (fun _ => g : M -> G) = fun _ => 0
  proof: funext fun _ => sub_self g

中文:
引理 fwdDiff_const
  条件: (g : G)
  结论: Δ_[h] (fun _ => g : M -> G) = fun _ => 0
  证明: funext fun _ => sub_self g
-/
@[simp] lemma fwdDiff_const (g : G) : Δ_[h] (fun _ => g : M -> G) = fun _ => 0 :=
  funext fun _ => sub_self g

section smul

/--
lemma `fwdDiff_smul` / 引理 `fwdDiff_smul`

English:
lemma fwdDiff_smul
  given: {R : Type*} [Ring R] [Module R G] (f : M -> R) (g : M -> G)
  proof: by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

中文:
引理 fwdDiff_smul
  条件: {R : 类型} [环 R] [模 R G] (f : M -> R) (g : M -> G)
  证明: by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

Depends on / 依赖: Pi.add_apply, Pi.smul_apply, add_apply, fwdDiff, smul_apply, smul_sub, sub_smul
-/
lemma fwdDiff_smul {R : Type*} [Ring R] [Module R G] (f : M -> R) (g : M -> G) :
    Δ_[h] (f • g) = Δ_[h] f • g + f • Δ_[h] g + Δ_[h] f • Δ_[h] g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', Pi.add_apply, smul_sub, sub_smul]
  abel

-- Note `fwdDiff_const_smul` is more general than `fwdDiff_smul` since it allows `R` to be a
-- semiring, rather than a ring; in particular `R = ℕ` is allowed.
/--
lemma `fwdDiff_const_smul` / 引理 `fwdDiff_const_smul`

English:
lemma fwdDiff_const_smul
  given: {R : Type*} [Monoid R] [DistribMulAction R G] (r : R) (f : M -> G)
  proof: funext fun _ => (smul_sub ..).symm

中文:
引理 fwdDiff_const_smul
  条件: {R : 类型} [幺半群 R] [分配乘法作用 R G] (r : R) (f : M -> G)
  证明: funext fun _ => (smul_sub ..).symm
-/
@[simp] lemma fwdDiff_const_smul {R : Type*} [Monoid R] [DistribMulAction R G] (r : R) (f : M -> G) :
    Δ_[h] (r • f) = r • Δ_[h] f :=
  funext fun _ => (smul_sub ..).symm

/--
lemma `fwdDiff_smul_const` / 引理 `fwdDiff_smul_const`

English:
lemma fwdDiff_smul_const
  given: {R : Type*} [Ring R] [Module R G] (f : M -> R) (g : G)
  proof: by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

中文:
引理 fwdDiff_smul_const
  条件: {R : 类型} [环 R] [模 R G] (f : M -> R) (g : G)
  证明: by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

Depends on / 依赖: MulHom, MulHom.map_mul, map_mul
-/
@[simp] lemma fwdDiff_smul_const {R : Type*} [Ring R] [Module R G] (f : M -> R) (g : G) :
    Δ_[h] (fun y => f y • g) = Δ_[h] f • fun _ => g := by
  ext y
  simp only [fwdDiff, Pi.smul_apply', sub_smul]

end smul

namespace fwdDiff_aux
/-!
## Forward-difference and shift operators as linear endomorphisms

This section contains versions of the forward-difference operator and the shift operator bundled as
`ℤ`-linear endomorphisms. These are useful for certain proofs; but they are slightly annoying to
use, as the source and target types of the maps have to be specified each time, and various
coercions need to be un-wound when the operators are applied, so we also provide the un-bundled
version.
-/

variable (M G) in
/-- Linear-endomorphism version of the forward difference operator. -/
@[simps]
/--
Definition of `fwdDiffₗ` / `fwdDiffₗ` 的定义

English:
definition fwdDiffₗ
  signature: : Module.End Int (M -> G) where
  body: fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h

中文:
定义 fwdDiffₗ
  签名: : 模.End 整数 (M -> G) where
  定义体: fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h

Depends on / 依赖: MulHom, MulHom.map_mul, fwdDiff, map_mul
-/
def fwdDiffₗ : Module.End Int (M -> G) where
  toFun := fwdDiff h
  map_add' := fwdDiff_add h
  map_smul' := fwdDiff_const_smul h

/--
lemma `coe_fwdDiffₗ` / 引理 `coe_fwdDiffₗ`

English:
lemma coe_fwdDiffₗ
  statement: ↑(fwdDiffₗ M G h) = fwdDiff h
  proof: rfl

中文:
引理 coe_fwdDiffₗ
  结论: ↑(fwdDiffₗ M G h) = fwdDiff h
  证明: rfl
-/
lemma coe_fwdDiffₗ : ↑(fwdDiffₗ M G h) = fwdDiff h := rfl

/--
lemma `coe_fwdDiffₗ_pow` / 引理 `coe_fwdDiffₗ_pow`

English:
lemma coe_fwdDiffₗ_pow
  given: (n : Nat)
  statement: ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n]
  proof: by
  ext; rw [Module.End.pow_apply, coe_fwdDiffₗ]

中文:
引理 coe_fwdDiffₗ_pow
  条件: (n : 自然数)
  结论: ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n]
  证明: by
  ext; rw [Module.End.pow_apply, coe_fwdDiffₗ]

Depends on / 依赖: Module, Module.End.pow_apply, pow_apply
-/
lemma coe_fwdDiffₗ_pow (n : Nat) : ↑(fwdDiffₗ M G h ^ n) = (fwdDiff h)^[n] := by
  ext; rw [Module.End.pow_apply, coe_fwdDiffₗ]

variable (M G) in
/--
Definition of `shiftₗ` / `shiftₗ` 的定义

English:
definition shiftₗ
  signature: : Module.End Int (M -> G)
  body: fwdDiffₗ M G h + 1

中文:
定义 shiftₗ
  签名: : 模.End 整数 (M -> G)
  定义体: fwdDiffₗ M G h + 1
-/
def shiftₗ : Module.End Int (M -> G) := fwdDiffₗ M G h + 1

/--
lemma `shiftₗ_apply` / 引理 `shiftₗ_apply`

English:
lemma shiftₗ_apply
  given: (f : M -> G) (y : M)
  statement: shiftₗ M G h f y = f (y + h)
  proof: by simp [shiftₗ, fwdDiff]

中文:
引理 shiftₗ_apply
  条件: (f : M -> G) (y : M)
  结论: shiftₗ M G h f y = f (y + h)
  证明: by simp [shiftₗ, fwdDiff]

Depends on / 依赖: fwdDiff
-/
lemma shiftₗ_apply (f : M -> G) (y : M) : shiftₗ M G h f y = f (y + h) := by simp [shiftₗ, fwdDiff]

/--
lemma `shiftₗ_pow_apply` / 引理 `shiftₗ_pow_apply`

English:
lemma shiftₗ_pow_apply
  given: (f : M -> G) (k : Nat) (y : M)
  statement: (shiftₗ M G h ^ k) f y = f (y + k • h)
  proof: by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

中文:
引理 shiftₗ_pow_apply
  条件: (f : M -> G) (k : 自然数) (y : M)
  结论: (shiftₗ M G h ^ k) f y = f (y + k • h)
  证明: by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

Depends on / 依赖: add_assoc, add_nsmul, generalizing, pow_add
-/
lemma shiftₗ_pow_apply (f : M -> G) (k : Nat) (y : M) : (shiftₗ M G h ^ k) f y = f (y + k • h) := by
  induction k generalizing f with
  | zero => simp
  | succ k IH => simp [pow_add, IH (shiftₗ M G h f), shiftₗ_apply, add_assoc, add_nsmul]

end fwdDiff_aux

open fwdDiff_aux

/--
lemma `fwdDiff_finsetSum` / 引理 `fwdDiff_finsetSum`

English:
lemma fwdDiff_finsetSum
  given: {α : Type*} (s : Finset α) (f : α -> M -> G)
  proof: map_sum (fwdDiffₗ M G h) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_finset_sum := fwdDiff_finsetSum

中文:
引理 fwdDiff_finsetSum
  条件: {α : 类型} (s : 有限集 α) (f : α -> M -> G)
  证明: map_sum (fwdDiffₗ M G h) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_finset_sum := fwdDiff_finsetSum
-/
@[simp] lemma fwdDiff_finsetSum {α : Type*} (s : Finset α) (f : α -> M -> G) :
    Δ_[h] (∑ k in s, f k) = ∑ k in s, Δ_[h] (f k) :=
  map_sum (fwdDiffₗ M G h) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_finset_sum := fwdDiff_finsetSum

/--
lemma `fwdDiff_iter_add` / 引理 `fwdDiff_iter_add`

English:
lemma fwdDiff_iter_add
  given: (f g : M -> G) (n : Nat)
  proof: by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g

中文:
引理 fwdDiff_iter_add
  条件: (f g : M -> G) (n : 自然数)
  证明: by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g
-/
@[simp] lemma fwdDiff_iter_add (f g : M -> G) (n : Nat) :
    Δ_[h]^[n] (f + g) = Δ_[h]^[n] f + Δ_[h]^[n] g := by
  simpa only [coe_fwdDiffₗ_pow] using map_add (fwdDiffₗ M G h ^ n) f g

/--
lemma `fwdDiff_iter_const_smul` / 引理 `fwdDiff_iter_const_smul`

English:
lemma fwdDiff_iter_const_smul
  statement: {R : Type*} [Monoid R] [DistribMulAction R G]
  proof: by
  induction n generalizing f with
  | zero => simp only [iterate_zero, id_eq]
  | succ n IH => simp only [iterate_succ_apply, fwdDiff_const_smul, IH]

中文:
引理 fwdDiff_iter_const_smul
  结论: {R : 类型} [幺半群 R] [分配乘法作用 R G]
  证明: by
  induction n generalizing f with
  | zero => simp only [iterate_zero, id_eq]
  | succ n IH => simp only [iterate_succ_apply, fwdDiff_const_smul, IH]
-/
@[simp] lemma fwdDiff_iter_const_smul {R : Type*} [Monoid R] [DistribMulAction R G]
    (r : R) (f : M -> G) (n : Nat) : Δ_[h]^[n] (r • f) = r • Δ_[h]^[n] f := by
  induction n generalizing f with
  | zero => simp only [iterate_zero, id_eq]
  | succ n IH => simp only [iterate_succ_apply, fwdDiff_const_smul, IH]

/--
lemma `fwdDiff_iter_finsetSum` / 引理 `fwdDiff_iter_finsetSum`

English:
lemma fwdDiff_iter_finsetSum
  given: {α : Type*} (s : Finset α) (f : α -> M -> G) (n : Nat)
  proof: by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_iter_finset_sum := fwdDiff_iter_finsetSum

中文:
引理 fwdDiff_iter_finsetSum
  条件: {α : 类型} (s : 有限集 α) (f : α -> M -> G) (n : 自然数)
  证明: by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_iter_finset_sum := fwdDiff_iter_finsetSum
-/
@[simp] lemma fwdDiff_iter_finsetSum {α : Type*} (s : Finset α) (f : α -> M -> G) (n : Nat) :
    Δ_[h]^[n] (∑ k in s, f k) = ∑ k in s, Δ_[h]^[n] (f k) := by
  simpa only [coe_fwdDiffₗ_pow] using map_sum (fwdDiffₗ M G h ^ n) f s

@[deprecated (since := "2026-04-08")] alias fwdDiff_iter_finset_sum := fwdDiff_iter_finsetSum

section newton_formulae

/--
theorem `fwdDiff_iter_eq_sum_shift` / 定理 `fwdDiff_iter_eq_sum_shift`

English:
theorem fwdDiff_iter_eq_sum_shift
  given: (f : M -> G) (n : Nat) (y : M)
  proof: by
  -- rewrite in terms of `(shiftₗ - 1) ^ n`
  have : fwdDiffₗ M G h = shiftₗ M G h - 1 := by simp only [shiftₗ, add_sub_cancel_right]
  rw [← coe_fwdDiffₗ]; rw [this]; rw [← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (shiftₗ M G h) (-1) := (C

中文:
定理 fwdDiff_iter_eq_sum_shift
  条件: (f : M -> G) (n : 自然数) (y : M)
  证明: by
  -- rewrite in terms of `(shiftₗ - 1) ^ n`
  have : fwdDiffₗ M G h = shiftₗ M G h - 1 := by simp only [shiftₗ, add_sub_cancel_right]
  rw [← coe_fwdDiffₗ]; rw [this]; rw [← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (shiftₗ M G h) (-1) := (C
-/
theorem fwdDiff_iter_eq_sum_shift (f : M -> G) (n : Nat) (y : M) :
    Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.choose k) • f (y + k • h) := by
  -- rewrite in terms of `(shiftₗ - 1) ^ n`
  have : fwdDiffₗ M G h = shiftₗ M G h - 1 := by simp only [shiftₗ, add_sub_cancel_right]
  rw [← coe_fwdDiffₗ]; rw [this]; rw [← Module.End.pow_apply]
  -- use binomial theorem `Commute.add_pow` to expand this
  have : Commute (shiftₗ M G h) (-1) := (Commute.one_right _).neg_right
  convert congr_fun (LinearMap.congr_fun (this.add_pow n) f) y
  · simp only [sub_eq_add_neg]
  · rw [LinearMap.sum_apply, sum_apply]
    congr 1 with k
    have : ((-1) ^ (n - k) * n.choose k : Module.End Int (M -> G))
              = ↑((-1) ^ (n - k) * n.choose k : Int) := by norm_cast
    rw [mul_assoc]; rw [Module.End.mul_apply]; rw [this]; rw [Module.End.intCast_apply]; rw [map_smul]; rw [Pi.smul_apply]; rw [shiftₗ_pow_apply]

/--
lemma `fwdDiff_iter_comp_add` / 引理 `fwdDiff_iter_comp_add`

English:
lemma fwdDiff_iter_comp_add
  given: (f : M -> G) (m : M) (n : Nat) (y : M)
  proof: by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]

中文:
引理 fwdDiff_iter_comp_add
  条件: (f : M -> G) (m : M) (n : 自然数) (y : M)
  证明: by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]

Depends on / 依赖: add_right_comm, fwdDiff_iter_eq_sum_shift
-/
lemma fwdDiff_iter_comp_add (f : M -> G) (m : M) (n : Nat) (y : M) :
    Δ_[h]^[n] (fun r => f (r + m)) y = (Δ_[h]^[n] f) (y + m) := by
  simp [fwdDiff_iter_eq_sum_shift, add_right_comm]

/--
lemma `fwdDiff_comp_add` / 引理 `fwdDiff_comp_add`

English:
lemma fwdDiff_comp_add
  given: (f : M -> G) (m : M) (y : M)
  proof: fwdDiff_iter_comp_add h f m 1 y

中文:
引理 fwdDiff_comp_add
  条件: (f : M -> G) (m : M) (y : M)
  证明: fwdDiff_iter_comp_add h f m 1 y

Depends on / 依赖: fwdDiff_iter_comp_add
-/
lemma fwdDiff_comp_add (f : M -> G) (m : M) (y : M) :
    Δ_[h] (fun r => f (r + m)) y = (Δ_[h] f) (y + m) :=
  fwdDiff_iter_comp_add h f m 1 y

/--
theorem `shift_eq_sum_fwdDiff_iter` / 定理 `shift_eq_sum_fwdDiff_iter`

English:
theorem shift_eq_sum_fwdDiff_iter
  given: (f : M -> G) (n : Nat) (y : M)
  proof: by
  convert!
    congr_fun (LinearMap.congr_fun ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp [Module.End.pow_apply, coe_fwdDiffₗ]

中文:
定理 shift_eq_sum_fwdDiff_iter
  条件: (f : M -> G) (n : 自然数) (y : M)
  证明: by
  convert!
    congr_fun (LinearMap.congr_fun ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp [Module.End.pow_apply, coe_fwdDiffₗ]

Depends on / 依赖: Commute, Commute.one_right, LinearMap, LinearMap.congr_fun, Module, Module.End.pow_apply, add_pow, congr_fun, convert, one_right, pow_apply
-/
theorem shift_eq_sum_fwdDiff_iter (f : M -> G) (n : Nat) (y : M) :
    f (y + n • h) = ∑ k in range (n + 1), n.choose k • Δ_[h]^[k] f y := by
  convert!
    congr_fun (LinearMap.congr_fun ((Commute.one_right (fwdDiffₗ M G h)).add_pow n) f) y using 1
  · rw [← shiftₗ_pow_apply h f, shiftₗ]
  · simp [Module.End.pow_apply, coe_fwdDiffₗ]

end newton_formulae

section choose

/--
lemma `fwdDiff_choose` / 引理 `fwdDiff_choose`

English:
lemma fwdDiff_choose
  given: (j : Nat)
  statement: Δ_[1] (fun x => x.choose (j + 1) : Nat -> Int) = fun x => x.choose j
  proof: by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

中文:
引理 fwdDiff_choose
  条件: (j : 自然数)
  结论: Δ_[1] (fun x => x.choose (j + 1) : 自然数 -> 整数) = fun x => x.choose j
  证明: by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

Depends on / 依赖: add_sub_cancel_right, cast_add, choose_succ_succ, fwdDiff
-/
lemma fwdDiff_choose (j : Nat) : Δ_[1] (fun x => x.choose (j + 1) : Nat -> Int) = fun x => x.choose j := by
  ext n
  simp only [fwdDiff, choose_succ_succ' n j, cast_add, add_sub_cancel_right]

/--
lemma `fwdDiff_iter_choose` / 引理 `fwdDiff_iter_choose`

English:
lemma fwdDiff_iter_choose
  given: (j k : Nat)
  proof: by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

中文:
引理 fwdDiff_iter_choose
  条件: (j k : 自然数)
  证明: by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

Depends on / 依赖: add_assoc, add_comm, fwdDiff_choose, generalizing, id_eq, iterate_succ_apply, iterate_zero, zero_add
-/
lemma fwdDiff_iter_choose (j k : Nat) :
    Δ_[1]^[k] (fun x => x.choose (k + j) : Nat -> Int) = fun x => x.choose j := by
  induction k generalizing j with
  | zero => simp only [zero_add, iterate_zero, id_eq]
  | succ k IH =>
    simp only [iterate_succ_apply', add_assoc, add_comm 1 j, IH, fwdDiff_choose]

/--
lemma `fwdDiff_iter_choose_zero` / 引理 `fwdDiff_iter_choose_zero`

English:
lemma fwdDiff_iter_choose_zero
  given: (m n : Nat)
  proof: by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwd

中文:
引理 fwdDiff_iter_choose_zero
  条件: (m n : 自然数)
  证明: by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwd

Depends on / 依赖: Nat.exists_eq_add_of_lt, add_zero, cast_one, choose_zero_right, exists_eq_add_of_lt, fwdDiff_const, fwdDiff_iter_choose, fwdDiff_iter_eq_sum_shift, hmn.ne, hnm.ne, if_false, if_true, iterate_add_apply, iterate_one, lt_trichotomy, simp_rw, smul_zero, sum_const_zero
-/
lemma fwdDiff_iter_choose_zero (m n : Nat) :
    Δ_[1]^[n] (fun x => x.choose m : Nat -> Int) 0 = if n = m then 1 else 0 := by
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · rcases Nat.exists_eq_add_of_lt hmn with ⟨k, rfl⟩
    simp_rw [hmn.ne', if_false, (by ring : m + k + 1 = k + 1 + m), iterate_add_apply,
      add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, iterate_one, cast_one, fwdDiff_const,
      fwdDiff_iter_eq_sum_shift, smul_zero, sum_const_zero]
  · simp only [if_true, add_zero m ▸ fwdDiff_iter_choose 0 m, choose_zero_right, cast_one]
  · rcases Nat.exists_eq_add_of_lt hnm with ⟨k, rfl⟩
    simp_rw [hnm.ne, if_false, add_assoc n k 1, fwdDiff_iter_choose, choose_zero_succ, cast_zero]

end choose

/--
lemma `fwdDiff_addChar_eq` / 引理 `fwdDiff_addChar_eq`

English:
lemma fwdDiff_addChar_eq
  statement: {M R : Type*} [AddCommMonoid M] [Ring R]
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul]; rw [← AddChar.map_add_eq_mul]; rw [add_comm h x]; rw [one_mul]

中文:
引理 fwdDiff_addChar_eq
  结论: {M R : 类型} [加法交换幺半群 M] [环 R]
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul]; rw [← AddChar.map_add_eq_mul]; rw [add_comm h x]; rw [one_mul]

Depends on / 依赖: AddChar, AddChar.map_add_eq_mul, add_comm, fwdDiff, generalizing, iterate_succ_apply, map_add_eq_mul, mul_assoc, mul_sub, one_mul, pow_succ, sub_mul
-/
lemma fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [Ring R]
    (φ : AddChar M R) (x h : M) (n : Nat) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * φ x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp only [pow_succ, iterate_succ_apply', fwdDiff, IH, ← mul_sub, mul_assoc]
    rw [sub_mul]; rw [← AddChar.map_add_eq_mul]; rw [add_comm h x]; rw [one_mul]

/-!
## Forward differences of polynomials

We prove formulae about the forward difference operator applied to polynomials:

* `fwdDiff_iter_pow_eq_zero_of_lt` :
  The `n`-th forward difference of the function `x ↦ x^j` is zero if `j < n`;
* `fwdDiff_iter_eq_factorial` :
  The `n`-th forward difference of the function `x ↦ x^n` is the constant function `n!`;
* `fwdDiff_iter_sum_mul_pow_eq_zero` :
  The `n`-th forward difference of a polynomial of degree `< n` is zero (formulated using explicit
    sums over `range n`).
-/

variable {R : Type*} [CommRing R]

/--
theorem `fwdDiff_iter_pow_eq_zero_of_lt` / 定理 `fwdDiff_iter_pow_eq_zero_of_lt`

English:
theorem fwdDiff_iter_pow_eq_zero_of_lt
  given: {j n : Nat} (h : j < n)
  proof: by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) => r ^ j) = ∑ i in range j, j.choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply]; rw [this]; rw [fwdDiff_it

中文:
定理 fwdDiff_iter_pow_eq_zero_of_lt
  条件: {j n : 自然数} (h : j < n)
  证明: by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) => r ^ j) = ∑ i in range j, j.choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply]; rw [this]; rw [fwdDiff_it

Depends on / 依赖: add_pow, fwdDiff, fwdDiff_iter_const_smul, fwdDiff_iter_finsetSum, generalizing, iterate_succ_apply, j.choose, mem_range, mul_comm, nsmul_eq_mul, nsmul_zero, sum_eq_zero, sum_range_succ
-/
theorem fwdDiff_iter_pow_eq_zero_of_lt {j n : Nat} (h : j < n) :
    Δ_[1]^[n] (fun (r : R) => r ^ j) = 0 := by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) => r ^ j) = ∑ i in range j, j.choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply]; rw [this]; rw [fwdDiff_iter_finsetSum]
    exact sum_eq_zero fun i hi => by
      rw [fwdDiff_iter_const_smul]; rw [ih (by have := mem_range.1 hi; lia)]; rw [nsmul_zero]

/--
theorem `fwdDiff_iter_eq_factorial` / 定理 `fwdDiff_iter_eq_factorial`

English:
theorem fwdDiff_iter_eq_factorial
  given: {n : Nat}
  proof: by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) => r ^ (n + 1)) =
      ∑ i in range (n + 1), (n + 1).choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDif

中文:
定理 fwdDiff_iter_eq_factorial
  条件: {n : 自然数}
  证明: by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) => r ^ (n + 1)) =
      ∑ i in range (n + 1), (n + 1).choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDif

Depends on / 依赖: add_pow, factorial_succ, fwdDiff, fwdDiff_iter_const_smul, fwdDiff_iter_finsetSum, fwdDiff_iter_pow_eq_zero_of_lt, iterate_succ_apply, mem_range, mul_comm, mul_zero, nsmul_eq_mul, simp_rw, sum_eq_zero, sum_range_succ
-/
theorem fwdDiff_iter_eq_factorial {n : Nat} :
    Δ_[1]^[n] (fun (r : R) => r ^ n) = n ! := by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) => r ^ (n + 1)) =
      ∑ i in range (n + 1), (n + 1).choose i • fun r => r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul,
       sum_range_succ]
    simpa [IH, factorial_succ] using sum_eq_zero fun i hi => by
      rw [fwdDiff_iter_pow_eq_zero_of_lt (by have := mem_range.1 hi; lia)]; rw [mul_zero]

/--
theorem `Polynomial.fwdDiff_iter_degree_eq_factorial` / 定理 `Polynomial.fwdDiff_iter_degree_eq_factorial`

English:
theorem Polynomial.fwdDiff_iter_degree_eq_factorial
  given: (P : R[X])
  proof: funext fun x => by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x => P.coeff i * x ^ i),
    fwdDiff_iter_finsetSum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply]; rw [sum_range_succ]; rw [sum_eq_zero (fun i hi => ?_)]; rw [zero_add]; rw [fwdDiff_it

中文:
定理 多项式.fwdDiff_iter_degree_eq_factorial
  条件: (P : R[X])
  证明: funext fun x => by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x => P.coeff i * x ^ i),
    fwdDiff_iter_finsetSum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply]; rw [sum_range_succ]; rw [sum_eq_zero (fun i hi => ?_)]; rw [zero_add]; rw [fwdDiff_it

Depends on / 依赖: P.coeff, P.eval_eq_sum_range, Pi.smul_apply, Pi.smul_def, Pi.zero_apply, eval_eq_sum_range, fwdDiff_iter_const_smul, fwdDiff_iter_eq_factorial, fwdDiff_iter_finsetSum, fwdDiff_iter_pow_eq_zero_of_lt, leadingCoeff, mem_range, mem_range.mp, simp_rw, smul_apply, smul_def, smul_eq_mul, smul_zero, sum_apply, sum_eq_zero
-/
theorem Polynomial.fwdDiff_iter_degree_eq_factorial (P : R[X]) :
    Δ_[1]^[P.natDegree] P.eval = P.leadingCoeff • P.natDegree ! := funext fun x => by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x => P.coeff i * x ^ i),
    fwdDiff_iter_finsetSum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply]; rw [sum_range_succ]; rw [sum_eq_zero (fun i hi => ?_)]; rw [zero_add]; rw [fwdDiff_iter_eq_factorial]; rw [leadingCoeff]; rw [Pi.smul_apply]
  rw [fwdDiff_iter_pow_eq_zero_of_lt (mem_range.mp hi)]; rw [smul_zero]; rw [Pi.zero_apply]

/--
theorem `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` / 定理 `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`

English:
theorem Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
  given: {P : R[X]} {n : Nat} (hP : P.natDegree < n)
  proof: funext fun x => by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc]; rw [add_comm]; rw [Function.iterate_add_apply]; rw [Function.iterate_succ_apply]; rw [P.fwdDiff_iter_degree_eq_factorial]; rw [Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]

中文:
定理 多项式.fwdDiff_iter_eq_zero_of_degree_lt
  条件: {P : R[X]} {n : 自然数} (hP : P.natDegree < n)
  证明: funext fun x => by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc]; rw [add_comm]; rw [Function.iterate_add_apply]; rw [Function.iterate_succ_apply]; rw [P.fwdDiff_iter_degree_eq_factorial]; rw [Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]

Depends on / 依赖: Function, Function.iterate_add_apply, Function.iterate_succ_apply, Nat.exists_eq_add_of_lt, P.fwdDiff_iter_degree_eq_factorial, Pi.smul_def, add_assoc, add_comm, exists_eq_add_of_lt, fwdDiff_iter_degree_eq_factorial, fwdDiff_iter_eq_sum_shift, iterate_add_apply, iterate_succ_apply, smul_def
-/
theorem Polynomial.fwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : Nat} (hP : P.natDegree < n) :
    Δ_[1]^[n] P.eval = 0 := funext fun x => by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hP
  rw [add_assoc]; rw [add_comm]; rw [Function.iterate_add_apply]; rw [Function.iterate_succ_apply]; rw [P.fwdDiff_iter_degree_eq_factorial]; rw [Pi.smul_def]
  simp [fwdDiff_iter_eq_sum_shift]

/--
theorem `Polynomial.fwdDiff_iter_degree_add_one_eq_zero` / 定理 `Polynomial.fwdDiff_iter_degree_add_one_eq_zero`

English:
theorem Polynomial.fwdDiff_iter_degree_add_one_eq_zero
  given: (P : R[X])
  proof: by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

中文:
定理 多项式.fwdDiff_iter_degree_add_one_eq_zero
  条件: (P : R[X])
  证明: by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

Depends on / 依赖: Nat.lt_succ_self, P.natDegree, Polynomial, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt, fwdDiff_iter_eq_zero_of_degree_lt, lt_succ_self, natDegree
-/
theorem Polynomial.fwdDiff_iter_degree_add_one_eq_zero (P : R[X]) :
    Δ_[1]^[P.natDegree + 1] P.eval = 0 := by
  have hP : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self P.natDegree
  exact Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP

/--
theorem `fwdDiff_iter_sum_mul_pow_eq_zero` / 定理 `fwdDiff_iter_sum_mul_pow_eq_zero`

English:
theorem fwdDiff_iter_sum_mul_pow_eq_zero
  given: {n : Nat} (P : Nat -> R)
  proof: by
  simp_rw [← sum_apply _ _ (fun i x => P i * x ^ i), fwdDiff_iter_finsetSum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
exact sum_eq_zero fun i hi => smul_eq_zero_of_right _ fwdDiff_iter_pow_eq_zero_of_lt
 mem_range.mp hi

中文:
定理 fwdDiff_iter_sum_mul_pow_eq_zero
  条件: {n : 自然数} (P : 自然数 -> R)
  证明: by
  simp_rw [← sum_apply _ _ (fun i x => P i * x ^ i), fwdDiff_iter_finsetSum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
exact sum_eq_zero fun i hi => smul_eq_zero_of_right _ fwdDiff_iter_pow_eq_zero_of_lt
 mem_range.mp hi

Depends on / 依赖: Pi.smul_def, fwdDiff_iter_const_smul, fwdDiff_iter_finsetSum, fwdDiff_iter_pow_eq_zero_of_lt, mem_range, mem_range.mp, simp_rw, smul_def, smul_eq_mul, smul_eq_zero_of_right, sum_apply, sum_eq_zero, sum_fn
-/
theorem fwdDiff_iter_sum_mul_pow_eq_zero {n : Nat} (P : Nat -> R) :
    Δ_[1]^[n] (fun r : R => ∑ k in range n, P k * r ^ k) = 0 := by
  simp_rw [← sum_apply _ _ (fun i x => P i * x ^ i), fwdDiff_iter_finsetSum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
exact sum_eq_zero fun i hi => smul_eq_zero_of_right _ fwdDiff_iter_pow_eq_zero_of_lt
 mem_range.mp hi
