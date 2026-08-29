/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Batteries.Logic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.DepRewrite

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries easily.
-/

@[expose] public section

open Nat

namespace Int

variable {a b c d m n : Int}

/--
theorem `neg_eq_neg` / 定理 `neg_eq_neg`

English:
theorem neg_eq_neg
  given: {a b : Int} (h : -a = -b)
  statement: a = b
  proof: Int.neg_inj.1 h

中文:
定理 neg_eq_neg
  条件: {a b : 整数} (h : -a = -b)
  结论: a = b
  证明: Int.neg_inj.1 h
-/
protected theorem neg_eq_neg {a b : Int} (h : -a = -b) : a = b := Int.neg_inj.1 h

/-! ### succ and pred -/

/--
Definition of `succ` / `succ` 的定义

English:
definition succ
  signature: (a : Int)
  body: a + 1

中文:
定义 succ
  签名: (a : 整数)
  定义体: a + 1
-/
def succ (a : Int) := a + 1

/--
Definition of `pred` / `pred` 的定义

English:
definition pred
  signature: (a : Int)
  body: a - 1

中文:
定义 pred
  签名: (a : 整数)
  定义体: a - 1
-/
def pred (a : Int) := a - 1

/--
lemma `pred_succ` / 引理 `pred_succ`

English:
lemma pred_succ
  given: (a : Int)
  statement: pred (succ a) = a
  proof: Int.add_sub_cancel _ _

中文:
引理 pred_succ
  条件: (a : 整数)
  结论: pred (succ a) = a
  证明: Int.add_sub_cancel _ _

Depends on / 依赖: Int.add_sub_cancel, add_sub_cancel
-/
lemma pred_succ (a : Int) : pred (succ a) = a := Int.add_sub_cancel _ _

/--
lemma `succ_pred` / 引理 `succ_pred`

English:
lemma succ_pred
  given: (a : Int)
  statement: succ (pred a) = a
  proof: Int.sub_add_cancel _ _

中文:
引理 succ_pred
  条件: (a : 整数)
  结论: succ (pred a) = a
  证明: Int.sub_add_cancel _ _

Depends on / 依赖: Int.sub_add_cancel, sub_add_cancel
-/
lemma succ_pred (a : Int) : succ (pred a) = a := Int.sub_add_cancel _ _

/--
lemma `neg_succ` / 引理 `neg_succ`

English:
lemma neg_succ
  given: (a : Int)
  statement: -succ a = pred (-a)
  proof: Int.neg_add

中文:
引理 neg_succ
  条件: (a : 整数)
  结论: -succ a = pred (-a)
  证明: Int.neg_add

Depends on / 依赖: Int.neg_add, neg_add
-/
lemma neg_succ (a : Int) : -succ a = pred (-a) := Int.neg_add

/--
lemma `succ_neg_succ` / 引理 `succ_neg_succ`

English:
lemma succ_neg_succ
  given: (a : Int)
  statement: succ (-succ a) = -a
  proof: by rw [neg_succ, succ_pred]

中文:
引理 succ_neg_succ
  条件: (a : 整数)
  结论: succ (-succ a) = -a
  证明: by rw [neg_succ, succ_pred]

Depends on / 依赖: neg_succ, succ_pred
-/
lemma succ_neg_succ (a : Int) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

/--
lemma `neg_pred` / 引理 `neg_pred`

English:
lemma neg_pred
  given: (a : Int)
  statement: -pred a = succ (-a)
  proof: by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a))]; rw [Int.neg_neg]

中文:
引理 neg_pred
  条件: (a : 整数)
  结论: -pred a = succ (-a)
  证明: by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a))]; rw [Int.neg_neg]

Depends on / 依赖: Int.neg_eq_comm.mp, Int.neg_neg, neg_eq_comm, neg_neg, neg_succ
-/
lemma neg_pred (a : Int) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a))]; rw [Int.neg_neg]

/--
lemma `pred_neg_pred` / 引理 `pred_neg_pred`

English:
lemma pred_neg_pred
  given: (a : Int)
  statement: pred (-pred a) = -a
  proof: by rw [neg_pred, pred_succ]

中文:
引理 pred_neg_pred
  条件: (a : 整数)
  结论: pred (-pred a) = -a
  证明: by rw [neg_pred, pred_succ]

Depends on / 依赖: neg_pred, pred_succ
-/
lemma pred_neg_pred (a : Int) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

/--
lemma `pred_nat_succ` / 引理 `pred_nat_succ`

English:
lemma pred_nat_succ
  given: (n : Nat)
  statement: pred (Nat.succ n) = n
  proof: pred_succ n

中文:
引理 pred_nat_succ
  条件: (n : 自然数)
  结论: pred (自然数.succ n) = n
  证明: pred_succ n

Depends on / 依赖: pred_succ
-/
lemma pred_nat_succ (n : Nat) : pred (Nat.succ n) = n := pred_succ n

/--
lemma `neg_nat_succ` / 引理 `neg_nat_succ`

English:
lemma neg_nat_succ
  given: (n : Nat)
  statement: -(Nat.succ n : Int) = pred (-n)
  proof: neg_succ n

中文:
引理 neg_nat_succ
  条件: (n : 自然数)
  结论: -(自然数.succ n : 整数) = pred (-n)
  证明: neg_succ n

Depends on / 依赖: neg_succ
-/
lemma neg_nat_succ (n : Nat) : -(Nat.succ n : Int) = pred (-n) := neg_succ n

/--
lemma `succ_neg_natCast_succ` / 引理 `succ_neg_natCast_succ`

English:
lemma succ_neg_natCast_succ
  given: (n : Nat)
  statement: succ (-Nat.succ n) = -n
  proof: succ_neg_succ n

中文:
引理 succ_neg_natCast_succ
  条件: (n : 自然数)
  结论: succ (-自然数.succ n) = -n
  证明: succ_neg_succ n

Depends on / 依赖: succ_neg_succ
-/
lemma succ_neg_natCast_succ (n : Nat) : succ (-Nat.succ n) = -n := succ_neg_succ n

/--
lemma `natCast_pred_of_pos` / 引理 `natCast_pred_of_pos`

English:
lemma natCast_pred_of_pos
  given: {n : Nat} (h : 0 < n)
  statement: ((n - 1 : Nat) : Int) = (n : Int) - 1
  proof: by
  grind

中文:
引理 natCast_pred_of_pos
  条件: {n : 自然数} (h : 0 < n)
  结论: ((n - 1 : 自然数) : 整数) = (n : 整数) - 1
  证明: by
  grind
-/
@[norm_cast] lemma natCast_pred_of_pos {n : Nat} (h : 0 < n) : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by
  grind

/--
lemma `lt_succ_self` / 引理 `lt_succ_self`

English:
lemma lt_succ_self
  given: (a : Int)
  statement: a < succ a
  proof: by unfold succ; lia

中文:
引理 lt_succ_self
  条件: (a : 整数)
  结论: a < succ a
  证明: by unfold succ; lia
-/
lemma lt_succ_self (a : Int) : a < succ a := by unfold succ; lia

/--
lemma `pred_self_lt` / 引理 `pred_self_lt`

English:
lemma pred_self_lt
  given: (a : Int)
  statement: pred a < a
  proof: by unfold pred; lia

中文:
引理 pred_self_lt
  条件: (a : 整数)
  结论: pred a < a
  证明: by unfold pred; lia
-/
lemma pred_self_lt (a : Int) : pred a < a := by unfold pred; lia

/--
lemma `induction_on` / 引理 `induction_on`

English:
lemma induction_on
  statement: {motive : Int -> Prop} (i : Int)
  proof: by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact zero
    | succ i ih => exact succ _ ih
  | negSucc i =>
    suffices forall n : Nat, motive (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [zero]
    | succ n ih => simpa [natCast_succ, Int.neg_add, I

中文:
引理 induction_on
  结论: {motive : 整数 -> 命题} (i : 整数)
  证明: by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact zero
    | succ i ih => exact succ _ ih
  | negSucc i =>
    suffices forall n : Nat, motive (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [zero]
    | succ n ih => simpa [natCast_succ, Int.neg_add, I
-/
@[elab_as_elim, induction_eliminator] protected lemma induction_on {motive : Int -> Prop} (i : Int)
    (zero : motive 0) (succ : forall i : Nat, motive i -> motive (i + 1))
    (pred : forall i : Nat, motive (-i) -> motive (-i - 1)) : motive i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact zero
    | succ i ih => exact succ _ ih
  | negSucc i =>
    suffices forall n : Nat, motive (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [zero]
    | succ n ih => simpa [natCast_succ, Int.neg_add, Int.sub_eq_add_neg] using pred _ ih

section inductionOn'

variable {motive : Int -> Sort*} (z b : Int) (zero : motive b)
  (succ : forall k, b <= k -> motive k -> motive (k + 1)) (pred : forall k <= b, motive k -> motive (k - 1))

/--
Definition of `inductionOn'` / `inductionOn'` 的定义

English:
definition inductionOn'
  signature: : motive z
  body: cast (congrArg motive <| show b + (z - b) = z by lia)
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n

中文:
定义 inductionOn'
  签名: : motive z
  定义体: cast (congrArg motive <| show b + (z - b) = z by lia)
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
-/
@[elab_as_elim] protected def inductionOn' : motive z :=
cast (congrArg motive <| show b + (z - b) = z by lia)
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : forall n : Nat, motive (b + n)
  | 0 => cast (by simp) zero
| n + 1 => cast (by lia) succ _ (Int.le_add_of_nonneg_right (natCast_nonneg _)) (pos n)
  /-- The negative case of `Int.inductionOn'`. -/
  neg : forall n : Nat, motive (b + -[n+1])
  | 0 => pred _ Int.le_rfl zero
| n + 1 => cast (by lia) pred _ (by lia) (neg n)

variable {z b zero succ pred}

/--
lemma `inductionOn'_self` / 引理 `inductionOn'_self`

English:
lemma inductionOn'_self
  statement: b.inductionOn' b zero succ pred = zero
  proof: cast_eq_iff_heq.mpr .symm by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

中文:
引理 inductionOn'_self
  结论: b.inductionOn' b zero succ pred = zero
  证明: cast_eq_iff_heq.mpr .symm by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

Depends on / 依赖: b.sub_self, cast_eq_iff_heq, cast_eq_iff_heq.mpr, sub_self
-/
lemma inductionOn'_self : b.inductionOn' b zero succ pred = zero :=
cast_eq_iff_heq.mpr .symm by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

/--
theorem `inductionOn'_add_one` / 定理 `inductionOn'_add_one`

English:
theorem inductionOn'_add_one
  given: (hz : b <= z)
  proof: by
  unfold Int.inductionOn'
  rw! [show z - b = (z - b).toNat by lia, show z + 1 - b = ((z - b).toNat + 1 : Nat) by lia]
  grind [inductionOn'.pos, show b + (z - b).toNat = z by lia]

中文:
定理 inductionOn'_add_one
  条件: (hz : b <= z)
  证明: by
  unfold Int.inductionOn'
  rw! [show z - b = (z - b).toNat by lia, show z + 1 - b = ((z - b).toNat + 1 : Nat) by lia]
  grind [inductionOn'.pos, show b + (z - b).toNat = z by lia]
-/
theorem inductionOn'_add_one (hz : b <= z) :
    (z + 1).inductionOn' b zero succ pred = succ z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  rw! [show z - b = (z - b).toNat by lia, show z + 1 - b = ((z - b).toNat + 1 : Nat) by lia]
  grind [inductionOn'.pos, show b + (z - b).toNat = z by lia]

/--
theorem `inductionOn'_sub_one` / 定理 `inductionOn'_sub_one`

English:
theorem inductionOn'_sub_one
  given: (hz : z <= b)
  proof: by
  unfold Int.inductionOn'
  conv => lhs; unfold inductionOn'.neg
  by_cases z = b
  · rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = 0 by lia]
    grind [inductionOn'.pos]
  rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = -[(b - z - 1).toNat+1] by lia]
  grind

中文:
定理 inductionOn'_sub_one
  条件: (hz : z <= b)
  证明: by
  unfold Int.inductionOn'
  conv => lhs; unfold inductionOn'.neg
  by_cases z = b
  · rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = 0 by lia]
    grind [inductionOn'.pos]
  rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = -[(b - z - 1).toNat+1] by lia]
  grind
-/
theorem inductionOn'_sub_one (hz : z <= b) :
    (z - 1).inductionOn' b zero succ pred = pred z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  conv => lhs; unfold inductionOn'.neg
  by_cases z = b
  · rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = 0 by lia]
    grind [inductionOn'.pos]
  rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = -[(b - z - 1).toNat+1] by lia]
  grind

end inductionOn'

/--
Definition of `negInduction` / `negInduction` 的定义

English:
definition negInduction
  signature: {motive : Int -> Sort*} (nat : forall n : Nat, motive n)

中文:
定义 negInduction
  签名: {motive : 整数 -> Sort*} (nat : 对任意 n : 自然数, motive n)
-/
@[elab_as_elim] protected def negInduction {motive : Int -> Sort*} (nat : forall n : Nat, motive n)
    (neg : (forall n : Nat, motive n) -> forall n : Nat, motive (-n)) : forall n : Int, motive n
  | .ofNat n => nat n
| .negSucc n => neg nat n + 1

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
/--
Definition of `leInduction` / `leInduction` 的定义

English:
definition leInduction
  signature: {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
  body: fun n => n.inductionOn' m
    (fun _ => base) (fun k hle ih _ => succ k hle <| ih hle) (fun _ _ _ _ => False.elim <| by lia)

@[deprecated (since := "2026-03-25")] protected alias le_induction := Int.leInduction

中文:
定义 leInduction
  签名: {m : 整数} {motive : 对任意 n, m <= n -> Sort*} (base : motive m m.le_refl)
  定义体: fun n => n.inductionOn' m
    (fun _ => base) (fun k hle ih _ => succ k hle <| ih hle) (fun _ _ _ _ => False.elim <| by lia)

@[deprecated (since := "2026-03-25")] protected alias le_induction := Int.leInduction
-/
protected def leInduction {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
    (succ : forall n hmn, motive n hmn -> motive (n + 1) (le_add_one hmn)) : forall n hmn, motive n hmn :=
  fun n => n.inductionOn' m
    (fun _ => base) (fun k hle ih _ => succ k hle <| ih hle) (fun _ _ _ _ => False.elim <| by lia)

@[deprecated (since := "2026-03-25")] protected alias le_induction := Int.leInduction

/--
theorem `leInduction_base` / 定理 `leInduction_base`

English:
theorem leInduction_base
  statement: {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
  proof: by
  rw [Int.leInduction]; rw [inductionOn'_self]

中文:
定理 leInduction_base
  结论: {m : 整数} {motive : 对任意 n, m <= n -> Sort*} (base : motive m m.le_refl)
  证明: by
  rw [Int.leInduction]; rw [inductionOn'_self]

Depends on / 依赖: Int.leInduction, _self, inductionOn, leInduction, le_refl, m.le_refl, motive
-/
theorem leInduction_base {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
    (succ : forall n hmn, motive n hmn -> motive (n + 1) (le_add_one hmn)) :
    Int.leInduction (motive := motive) base succ m m.le_refl = base := by
  rw [Int.leInduction]; rw [inductionOn'_self]

/--
theorem `leInduction_add_one` / 定理 `leInduction_add_one`

English:
theorem leInduction_add_one
  statement: {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
  proof: by
  rw [Int.leInduction]; rw [inductionOn'_add_one hmn]
  rfl

中文:
定理 leInduction_add_one
  结论: {m : 整数} {motive : 对任意 n, m <= n -> Sort*} (base : motive m m.le_refl)
  证明: by
  rw [Int.leInduction]; rw [inductionOn'_add_one hmn]
  rfl

Depends on / 依赖: motive
-/
theorem leInduction_add_one {m : Int} {motive : forall n, m <= n -> Sort*} (base : motive m m.le_refl)
    (succ : forall n hmn, motive n hmn -> motive (n + 1) (le_add_one hmn)) (n : Int) (hmn : m <= n) :
    Int.leInduction (motive := motive) base succ (n + 1) (by lia) =
      succ n hmn (Int.leInduction (motive := motive) base succ n hmn) := by
  rw [Int.leInduction]; rw [inductionOn'_add_one hmn]
  rfl

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
/--
Definition of `leInductionDown` / `leInductionDown` 的定义

English:
definition leInductionDown
  signature: {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
  body: fun n => n.inductionOn' m
    (fun _ => base) (fun _ _ _ _ => False.elim <| by lia) (fun k hle ih _ => pred k hle <| ih hle)

中文:
定义 leInductionDown
  签名: {m : 整数} {motive : 对任意 n, n <= m -> Sort*} (base : motive m m.le_refl)
  定义体: fun n => n.inductionOn' m
    (fun _ => base) (fun _ _ _ _ => False.elim <| by lia) (fun k hle ih _ => pred k hle <| ih hle)
-/
protected def leInductionDown {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
    (pred : forall n hnm, motive n hnm -> motive (n - 1) (by lia)) : forall n hnm, motive n hnm :=
  fun n => n.inductionOn' m
    (fun _ => base) (fun _ _ _ _ => False.elim <| by lia) (fun k hle ih _ => pred k hle <| ih hle)

/--
theorem `leInductionDown_base` / 定理 `leInductionDown_base`

English:
theorem leInductionDown_base
  statement: {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
  proof: by
  rw [Int.leInductionDown]; rw [inductionOn'_self]

中文:
定理 leInductionDown_base
  结论: {m : 整数} {motive : 对任意 n, n <= m -> Sort*} (base : motive m m.le_refl)
  证明: by
  rw [Int.leInductionDown]; rw [inductionOn'_self]

Depends on / 依赖: Int.leInductionDown, _self, inductionOn, leInductionDown, le_refl, m.le_refl, motive
-/
theorem leInductionDown_base {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
    (pred : forall n hnm, motive n hnm -> motive (n - 1) (by lia)) :
    Int.leInductionDown (motive := motive) base pred m m.le_refl = base := by
  rw [Int.leInductionDown]; rw [inductionOn'_self]

/--
theorem `leInductionDown_sub_one` / 定理 `leInductionDown_sub_one`

English:
theorem leInductionDown_sub_one
  statement: {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
  proof: by
  rw [Int.leInductionDown]; rw [inductionOn'_sub_one hnm]
  rfl

@[deprecated (since := "2026-03-25")] protected alias le_induction_down := Int.leInductionDown

中文:
定理 leInductionDown_sub_one
  结论: {m : 整数} {motive : 对任意 n, n <= m -> Sort*} (base : motive m m.le_refl)
  证明: by
  rw [Int.leInductionDown]; rw [inductionOn'_sub_one hnm]
  rfl

@[deprecated (since := "2026-03-25")] protected alias le_induction_down := Int.leInductionDown

Depends on / 依赖: motive
-/
theorem leInductionDown_sub_one {m : Int} {motive : forall n, n <= m -> Sort*} (base : motive m m.le_refl)
    (pred : forall n hnm, motive n hnm -> motive (n - 1) (by lia)) (n : Int) (hnm : n <= m) :
    Int.leInductionDown (motive := motive) base pred (n - 1) (by lia) =
      pred n hnm (Int.leInductionDown (motive := motive) base pred n hnm) := by
  rw [Int.leInductionDown]; rw [inductionOn'_sub_one hnm]
  rfl

@[deprecated (since := "2026-03-25")] protected alias le_induction_down := Int.leInductionDown

section strongRec

variable {motive : Int -> Sort*} (lt : forall n < m, motive n)
  (ge : forall n >= m, (forall k < n, motive k) -> motive n)

/--
Definition of `strongRec` / `strongRec` 的定义

English:
definition strongRec
  signature: (n : Int)
  body: by
  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ => ih k (by lia)
  · exact fun n _ hn l _ => hn l (by lia)

中文:
定义 strongRec
  签名: (n : 整数)
  定义体: by
  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ => ih k (by lia)
  · exact fun n _ hn l _ => hn l (by lia)
-/
@[elab_as_elim] protected def strongRec (n : Int) : motive n := by
  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ => ih k (by lia)
  · exact fun n _ hn l _ => hn l (by lia)

variable {lt ge}
/--
lemma `strongRec_of_lt` / 引理 `strongRec_of_lt`

English:
lemma strongRec_of_lt
  given: (hn : n < m)
  statement: m.strongRec lt ge n = lt n hn
  proof: dif_pos _

中文:
引理 strongRec_of_lt
  条件: (hn : n < m)
  结论: m.strongRec lt ge n = lt n hn
  证明: dif_pos _

Depends on / 依赖: dif_pos
-/
lemma strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn := dif_pos _

end strongRec

/-! ### mul -/

/-! ### natAbs -/

alias natAbs_sq := natAbs_pow_two

/--
theorem `sign_mul_self_eq_natAbs` / 定理 `sign_mul_self_eq_natAbs`

English:
theorem sign_mul_self_eq_natAbs
  given: (a : Int)
  statement: sign a * a = natAbs a
  proof: sign_mul_self a

中文:
定理 sign_mul_self_eq_natAbs
  条件: (a : 整数)
  结论: sign a * a = natAbs a
  证明: sign_mul_self a

Depends on / 依赖: sign_mul_self
-/
theorem sign_mul_self_eq_natAbs (a : Int) : sign a * a = natAbs a :=
  sign_mul_self a


/--
lemma `natCast_div` / 引理 `natCast_div`

English:
lemma natCast_div
  given: (m n : Nat)
  statement: ((m / n : Nat) : Int) = m / n
  proof: natCast_ediv m n

中文:
引理 natCast_div
  条件: (m n : 自然数)
  结论: ((m / n : 自然数) : 整数) = m / n
  证明: natCast_ediv m n

Depends on / 依赖: natCast_ediv
-/
lemma natCast_div (m n : Nat) : ((m / n : Nat) : Int) = m / n := natCast_ediv m n

/--
lemma `ediv_of_neg_of_pos` / 引理 `ediv_of_neg_of_pos`

English:
lemma ediv_of_neg_of_pos
  given: {a b : Int} (Ha : a < 0) (Hb : 0 < b)
  statement: ediv a b = -((-a - 1) / b + 1)
  proof: match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : Int) = (m + 1 : Int) by rfl]; rw [Int.add_sub_cancel]; rfl

中文:
引理 ediv_of_neg_of_pos
  条件: {a b : 整数} (Ha : a < 0) (Hb : 0 < b)
  结论: ediv a b = -((-a - 1) / b + 1)
  证明: match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : Int) = (m + 1 : Int) by rfl]; rw [Int.add_sub_cancel]; rfl

Depends on / 依赖: Int.add_sub_cancel, add_sub_cancel, eq_negSucc_of_lt_zero, eq_succ_of_zero_lt
-/
lemma ediv_of_neg_of_pos {a b : Int} (Ha : a < 0) (Hb : 0 < b) : ediv a b = -((-a - 1) / b + 1) :=
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [show (- -[m+1] : Int) = (m + 1 : Int) by rfl]; rw [Int.add_sub_cancel]; rfl


/--
lemma `natCast_mod` / 引理 `natCast_mod`

English:
lemma natCast_mod
  given: (m n : Nat)
  statement: (↑(m % n) : Int) = ↑m % ↑n
  proof: rfl

中文:
引理 natCast_mod
  条件: (m n : 自然数)
  结论: (↑(m % n) : 整数) = ↑m % ↑n
  证明: rfl
-/
@[simp, norm_cast] lemma natCast_mod (m n : Nat) : (↑(m % n) : Int) = ↑m % ↑n := rfl

/--
lemma `div_le_iff_of_dvd_of_pos` / 引理 `div_le_iff_of_dvd_of_pos`

English:
lemma div_le_iff_of_dvd_of_pos
  given: (hb : 0 < b) (hba : b ∣ a)
  statement: a / b <= c ↔ a <= b * c
  proof: ediv_le_iff_of_dvd_of_pos hb hba

中文:
引理 div_le_iff_of_dvd_of_pos
  条件: (hb : 0 < b) (hba : b ∣ a)
  结论: a / b <= c ↔ a <= b * c
  证明: ediv_le_iff_of_dvd_of_pos hb hba

Depends on / 依赖: ediv_le_iff_of_dvd_of_pos
-/
lemma div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b <= c ↔ a <= b * c :=
  ediv_le_iff_of_dvd_of_pos hb hba

/--
lemma `div_le_iff_of_dvd_of_neg` / 引理 `div_le_iff_of_dvd_of_neg`

English:
lemma div_le_iff_of_dvd_of_neg
  given: (hb : b < 0) (hba : b ∣ a)
  statement: a / b <= c ↔ b * c <= a
  proof: ediv_le_iff_of_dvd_of_neg hb hba

中文:
引理 div_le_iff_of_dvd_of_neg
  条件: (hb : b < 0) (hba : b ∣ a)
  结论: a / b <= c ↔ b * c <= a
  证明: ediv_le_iff_of_dvd_of_neg hb hba

Depends on / 依赖: ediv_le_iff_of_dvd_of_neg
-/
lemma div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b <= c ↔ b * c <= a :=
  ediv_le_iff_of_dvd_of_neg hb hba

/--
lemma `div_lt_iff_of_dvd_of_pos` / 引理 `div_lt_iff_of_dvd_of_pos`

English:
lemma div_lt_iff_of_dvd_of_pos
  given: (hb : 0 < b) (hba : b ∣ a)
  statement: a / b < c ↔ a < b * c
  proof: ediv_lt_iff_of_dvd_of_pos hb hba

中文:
引理 div_lt_iff_of_dvd_of_pos
  条件: (hb : 0 < b) (hba : b ∣ a)
  结论: a / b < c ↔ a < b * c
  证明: ediv_lt_iff_of_dvd_of_pos hb hba

Depends on / 依赖: ediv_lt_iff_of_dvd_of_pos
-/
lemma div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) : a / b < c ↔ a < b * c :=
  ediv_lt_iff_of_dvd_of_pos hb hba

/--
lemma `div_lt_iff_of_dvd_of_neg` / 引理 `div_lt_iff_of_dvd_of_neg`

English:
lemma div_lt_iff_of_dvd_of_neg
  given: (hb : b < 0) (hba : b ∣ a)
  statement: a / b < c ↔ b * c < a
  proof: ediv_lt_iff_of_dvd_of_neg hb hba

中文:
引理 div_lt_iff_of_dvd_of_neg
  条件: (hb : b < 0) (hba : b ∣ a)
  结论: a / b < c ↔ b * c < a
  证明: ediv_lt_iff_of_dvd_of_neg hb hba

Depends on / 依赖: ediv_lt_iff_of_dvd_of_neg
-/
lemma div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) : a / b < c ↔ b * c < a :=
  ediv_lt_iff_of_dvd_of_neg hb hba

/--
lemma `le_div_iff_of_dvd_of_pos` / 引理 `le_div_iff_of_dvd_of_pos`

English:
lemma le_div_iff_of_dvd_of_pos
  given: (hc : 0 < c) (hcb : c ∣ b)
  statement: a <= b / c ↔ c * a <= b
  proof: le_ediv_iff_of_dvd_of_pos hc hcb

中文:
引理 le_div_iff_of_dvd_of_pos
  条件: (hc : 0 < c) (hcb : c ∣ b)
  结论: a <= b / c ↔ c * a <= b
  证明: le_ediv_iff_of_dvd_of_pos hc hcb

Depends on / 依赖: le_ediv_iff_of_dvd_of_pos
-/
lemma le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a <= b / c ↔ c * a <= b :=
  le_ediv_iff_of_dvd_of_pos hc hcb

/--
lemma `le_div_iff_of_dvd_of_neg` / 引理 `le_div_iff_of_dvd_of_neg`

English:
lemma le_div_iff_of_dvd_of_neg
  given: (hc : c < 0) (hcb : c ∣ b)
  statement: a <= b / c ↔ b <= c * a
  proof: le_ediv_iff_of_dvd_of_neg hc hcb

中文:
引理 le_div_iff_of_dvd_of_neg
  条件: (hc : c < 0) (hcb : c ∣ b)
  结论: a <= b / c ↔ b <= c * a
  证明: le_ediv_iff_of_dvd_of_neg hc hcb

Depends on / 依赖: le_ediv_iff_of_dvd_of_neg
-/
lemma le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a <= b / c ↔ b <= c * a :=
  le_ediv_iff_of_dvd_of_neg hc hcb

/--
lemma `lt_div_iff_of_dvd_of_pos` / 引理 `lt_div_iff_of_dvd_of_pos`

English:
lemma lt_div_iff_of_dvd_of_pos
  given: (hc : 0 < c) (hcb : c ∣ b)
  statement: a < b / c ↔ c * a < b
  proof: lt_ediv_iff_of_dvd_of_pos hc hcb

中文:
引理 lt_div_iff_of_dvd_of_pos
  条件: (hc : 0 < c) (hcb : c ∣ b)
  结论: a < b / c ↔ c * a < b
  证明: lt_ediv_iff_of_dvd_of_pos hc hcb

Depends on / 依赖: lt_ediv_iff_of_dvd_of_pos
-/
lemma lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) : a < b / c ↔ c * a < b :=
  lt_ediv_iff_of_dvd_of_pos hc hcb

/--
lemma `lt_div_iff_of_dvd_of_neg` / 引理 `lt_div_iff_of_dvd_of_neg`

English:
lemma lt_div_iff_of_dvd_of_neg
  given: (hc : c < 0) (hcb : c ∣ b)
  statement: a < b / c ↔ b < c * a
  proof: lt_ediv_iff_of_dvd_of_neg hc hcb

中文:
引理 lt_div_iff_of_dvd_of_neg
  条件: (hc : c < 0) (hcb : c ∣ b)
  结论: a < b / c ↔ b < c * a
  证明: lt_ediv_iff_of_dvd_of_neg hc hcb

Depends on / 依赖: lt_ediv_iff_of_dvd_of_neg
-/
lemma lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) : a < b / c ↔ b < c * a :=
  lt_ediv_iff_of_dvd_of_neg hc hcb

/--
lemma `div_le_div_iff_of_dvd_of_pos_of_pos` / 引理 `div_le_div_iff_of_dvd_of_pos_of_pos`

English:
lemma div_le_div_iff_of_dvd_of_pos_of_pos
  statement: (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
  proof: ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba hdc

中文:
引理 div_le_div_iff_of_dvd_of_pos_of_pos
  结论: (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
  证明: ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba hdc

Depends on / 依赖: ediv_le_ediv_iff_of_dvd_of_pos_of_pos
-/
lemma div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b <= c / d ↔ d * a <= c * b :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba hdc

/--
lemma `div_le_div_iff_of_dvd_of_pos_of_neg` / 引理 `div_le_div_iff_of_dvd_of_pos_of_neg`

English:
lemma div_le_div_iff_of_dvd_of_pos_of_neg
  given: (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_le_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

中文:
引理 div_le_div_iff_of_dvd_of_pos_of_neg
  条件: (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_le_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

Depends on / 依赖: ediv_le_ediv_iff_of_dvd_of_pos_of_neg
-/
lemma div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b <= c / d ↔ c * b <= d * a :=
  ediv_le_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

/--
lemma `div_le_div_iff_of_dvd_of_neg_of_pos` / 引理 `div_le_div_iff_of_dvd_of_neg_of_pos`

English:
lemma div_le_div_iff_of_dvd_of_neg_of_pos
  given: (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_le_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

中文:
引理 div_le_div_iff_of_dvd_of_neg_of_pos
  条件: (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_le_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

Depends on / 依赖: ediv_le_ediv_iff_of_dvd_of_neg_of_pos
-/
lemma div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b <= c / d ↔ c * b <= d * a :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

/--
lemma `div_le_div_iff_of_dvd_of_neg_of_neg` / 引理 `div_le_div_iff_of_dvd_of_neg_of_neg`

English:
lemma div_le_div_iff_of_dvd_of_neg_of_neg
  given: (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

中文:
引理 div_le_div_iff_of_dvd_of_neg_of_neg
  条件: (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

Depends on / 依赖: ediv_le_ediv_iff_of_dvd_of_neg_of_neg
-/
lemma div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b <= c / d ↔ d * a <= c * b :=
  ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

/--
lemma `div_lt_div_iff_of_dvd_of_pos` / 引理 `div_lt_div_iff_of_dvd_of_pos`

English:
lemma div_lt_div_iff_of_dvd_of_pos
  given: (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_lt_ediv_iff_of_dvd_of_pos hb hd hba hdc

中文:
引理 div_lt_div_iff_of_dvd_of_pos
  条件: (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_lt_ediv_iff_of_dvd_of_pos hb hd hba hdc

Depends on / 依赖: ediv_lt_ediv_iff_of_dvd_of_pos
-/
lemma div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_pos hb hd hba hdc

/--
lemma `div_lt_div_iff_of_dvd_of_pos_of_neg` / 引理 `div_lt_div_iff_of_dvd_of_pos_of_neg`

English:
lemma div_lt_div_iff_of_dvd_of_pos_of_neg
  given: (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_lt_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

中文:
引理 div_lt_div_iff_of_dvd_of_pos_of_neg
  条件: (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_lt_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

Depends on / 依赖: ediv_lt_ediv_iff_of_dvd_of_pos_of_neg
-/
lemma div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_pos_of_neg hb hd hba hdc

/--
lemma `div_lt_div_iff_of_dvd_of_neg_of_pos` / 引理 `div_lt_div_iff_of_dvd_of_neg_of_pos`

English:
lemma div_lt_div_iff_of_dvd_of_neg_of_pos
  given: (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_lt_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

中文:
引理 div_lt_div_iff_of_dvd_of_neg_of_pos
  条件: (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_lt_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

Depends on / 依赖: ediv_lt_ediv_iff_of_dvd_of_neg_of_pos
-/
lemma div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ c * b < d * a :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_pos hb hd hba hdc

/--
lemma `div_lt_div_iff_of_dvd_of_neg_of_neg` / 引理 `div_lt_div_iff_of_dvd_of_neg_of_neg`

English:
lemma div_lt_div_iff_of_dvd_of_neg_of_neg
  given: (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  proof: ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

中文:
引理 div_lt_div_iff_of_dvd_of_neg_of_neg
  条件: (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c)
  证明: ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc

Depends on / 依赖: ediv_lt_ediv_iff_of_dvd_of_neg_of_neg
-/
lemma div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    a / b < c / d ↔ d * a < c * b :=
  ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba hdc


/--
lemma `emod_two_eq_zero_or_one` / 引理 `emod_two_eq_zero_or_one`

English:
lemma emod_two_eq_zero_or_one
  given: (n : Int)
  statement: n % 2 = 0 ∨ n % 2 = 1
  proof: emod_two_eq n

中文:
引理 emod_two_eq_zero_or_one
  条件: (n : 整数)
  结论: n % 2 = 0 ∨ n % 2 = 1
  证明: emod_two_eq n

Depends on / 依赖: emod_two_eq
-/
lemma emod_two_eq_zero_or_one (n : Int) : n % 2 = 0 ∨ n % 2 = 1 :=
  emod_two_eq n


/--
lemma `dvd_mul_of_div_dvd` / 引理 `dvd_mul_of_div_dvd`

English:
lemma dvd_mul_of_div_dvd
  given: (h : b ∣ a) (hdiv : a / b ∣ c)
  statement: a ∣ b * c
  proof: dvd_mul_of_ediv_dvd h hdiv

中文:
引理 dvd_mul_of_div_dvd
  条件: (h : b ∣ a) (hdiv : a / b ∣ c)
  结论: a ∣ b * c
  证明: dvd_mul_of_ediv_dvd h hdiv

Depends on / 依赖: dvd_mul_of_ediv_dvd
-/
lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c :=
  dvd_mul_of_ediv_dvd h hdiv

/--
lemma `div_dvd_iff_dvd_mul` / 引理 `div_dvd_iff_dvd_mul`

English:
lemma div_dvd_iff_dvd_mul
  given: (h : b ∣ a) (hb : b != 0)
  statement: a / b ∣ c ↔ a ∣ b * c
  proof: ediv_dvd_iff_dvd_mul h hb

中文:
引理 div_dvd_iff_dvd_mul
  条件: (h : b ∣ a) (hb : b != 0)
  结论: a / b ∣ c ↔ a ∣ b * c
  证明: ediv_dvd_iff_dvd_mul h hb

Depends on / 依赖: ediv_dvd_iff_dvd_mul
-/
lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b != 0) : a / b ∣ c ↔ a ∣ b * c :=
  ediv_dvd_iff_dvd_mul h hb

/--
lemma `mul_dvd_of_dvd_div` / 引理 `mul_dvd_of_dvd_div`

English:
lemma mul_dvd_of_dvd_div
  given: (hcb : c ∣ b) (h : a ∣ b / c)
  statement: c * a ∣ b
  proof: mul_dvd_of_dvd_ediv hcb h

中文:
引理 mul_dvd_of_dvd_div
  条件: (hcb : c ∣ b) (h : a ∣ b / c)
  结论: c * a ∣ b
  证明: mul_dvd_of_dvd_ediv hcb h

Depends on / 依赖: mul_dvd_of_dvd_ediv
-/
lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  mul_dvd_of_dvd_ediv hcb h

/--
lemma `dvd_div_of_mul_dvd` / 引理 `dvd_div_of_mul_dvd`

English:
lemma dvd_div_of_mul_dvd
  given: (h : a * b ∣ c)
  statement: b ∣ c / a
  proof: dvd_ediv_of_mul_dvd h

中文:
引理 dvd_div_of_mul_dvd
  条件: (h : a * b ∣ c)
  结论: b ∣ c / a
  证明: dvd_ediv_of_mul_dvd h

Depends on / 依赖: dvd_ediv_of_mul_dvd
-/
lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  dvd_ediv_of_mul_dvd h

/--
lemma `dvd_div_iff_mul_dvd` / 引理 `dvd_div_iff_mul_dvd`

English:
lemma dvd_div_iff_mul_dvd
  given: (hbc : c ∣ b)
  statement: a ∣ b / c ↔ c * a ∣ b
  proof: by
  simp [hbc]

中文:
引理 dvd_div_iff_mul_dvd
  条件: (hbc : c ∣ b)
  结论: a ∣ b / c ↔ c * a ∣ b
  证明: by
  simp [hbc]
-/
lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b := by
  simp [hbc]

/--
lemma `exists_lt_and_lt_iff_not_dvd` / 引理 `exists_lt_and_lt_iff_not_dvd`

English:
lemma exists_lt_and_lt_iff_not_dvd
  given: (m : Int) (hn : 0 < n)
  proof: (not_dvd_iff_lt_mul_succ m hn).symm

中文:
引理 exists_lt_and_lt_iff_not_dvd
  条件: (m : 整数) (hn : 0 < n)
  证明: (not_dvd_iff_lt_mul_succ m hn).symm

Depends on / 依赖: not_dvd_iff_lt_mul_succ
-/
lemma exists_lt_and_lt_iff_not_dvd (m : Int) (hn : 0 < n) :
    (exists k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m :=
  (not_dvd_iff_lt_mul_succ m hn).symm

/--
lemma `eq_mul_div_of_mul_eq_mul_of_dvd_left` / 引理 `eq_mul_div_of_mul_eq_mul_of_dvd_left`

English:
lemma eq_mul_div_of_mul_eq_mul_of_dvd_left
  given: (hb : b != 0) (hbc : b ∣ c) (h : b * a = c * d)
  proof: by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h

中文:
引理 eq_mul_div_of_mul_eq_mul_of_dvd_left
  条件: (hb : b != 0) (hbc : b ∣ c) (h : b * a = c * d)
  证明: by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h

Depends on / 依赖: Int.mul_assoc, Int.mul_ediv_cancel_left, Int.mul_eq_mul_left_iff, mul_assoc, mul_ediv_cancel_left, mul_eq_mul_left_iff
-/
lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b != 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = c / b * d := by
  obtain ⟨k, rfl⟩ := hbc
  rw [Int.mul_ediv_cancel_left _ hb]
  rwa [Int.mul_assoc, Int.mul_eq_mul_left_iff hb] at h

/--
lemma `ofNat_add_negSucc_of_ge` / 引理 `ofNat_add_negSucc_of_ge`

English:
lemma ofNat_add_negSucc_of_ge
  given: {m n : Nat} (h : n.succ <= m)
  proof: by
  rw [negSucc_eq]; rw [ofNat_eq_natCast]; rw [ofNat_eq_natCast]; rw [← Int.natCast_one]; rw [← Int.natCast_add]; rw [← Int.sub_eq_add_neg]; rw [← Int.natCast_sub h]

中文:
引理 ofNat_add_negSucc_of_ge
  条件: {m n : 自然数} (h : n.succ <= m)
  证明: by
  rw [negSucc_eq]; rw [ofNat_eq_natCast]; rw [ofNat_eq_natCast]; rw [← Int.natCast_one]; rw [← Int.natCast_add]; rw [← Int.sub_eq_add_neg]; rw [← Int.natCast_sub h]

Depends on / 依赖: Int.natCast_add, Int.natCast_one, Int.natCast_sub, Int.sub_eq_add_neg, natCast_add, natCast_one, natCast_sub, negSucc_eq, ofNat_eq_natCast, sub_eq_add_neg
-/
lemma ofNat_add_negSucc_of_ge {m n : Nat} (h : n.succ <= m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq]; rw [ofNat_eq_natCast]; rw [ofNat_eq_natCast]; rw [← Int.natCast_one]; rw [← Int.natCast_add]; rw [← Int.sub_eq_add_neg]; rw [← Int.natCast_sub h]


/--
lemma `le_iff_pos_of_dvd` / 引理 `le_iff_pos_of_dvd`

English:
lemma le_iff_pos_of_dvd
  given: (ha : 0 < a) (hab : a ∣ b)
  statement: a <= b ↔ 0 < b
  proof: ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

中文:
引理 le_iff_pos_of_dvd
  条件: (ha : 0 < a) (hab : a ∣ b)
  结论: a <= b ↔ 0 < b
  证明: ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

Depends on / 依赖: Int.le_of_dvd, Int.lt_of_lt_of_le, le_of_dvd, lt_of_lt_of_le
-/
lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a <= b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

/--
lemma `le_add_iff_lt_of_dvd_sub` / 引理 `le_add_iff_lt_of_dvd_sub`

English:
lemma le_add_iff_lt_of_dvd_sub
  given: (ha : 0 < a) (hab : a ∣ c - b)
  statement: a + b <= c ↔ b < c
  proof: by
  rw [Int.add_le_iff_le_sub]; rw [← Int.sub_pos]; rw [le_iff_pos_of_dvd ha hab]

中文:
引理 le_add_iff_lt_of_dvd_sub
  条件: (ha : 0 < a) (hab : a ∣ c - b)
  结论: a + b <= c ↔ b < c
  证明: by
  rw [Int.add_le_iff_le_sub]; rw [← Int.sub_pos]; rw [le_iff_pos_of_dvd ha hab]

Depends on / 依赖: Int.add_le_iff_le_sub, Int.sub_pos, add_le_iff_le_sub, le_iff_pos_of_dvd, sub_pos
-/
lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b <= c ↔ b < c := by
  rw [Int.add_le_iff_le_sub]; rw [← Int.sub_pos]; rw [le_iff_pos_of_dvd ha hab]


/--
lemma `sign_add_eq_of_sign_eq` / 引理 `sign_add_eq_of_sign_eq`

English:
lemma sign_add_eq_of_sign_eq
  statement: forall {m n : Int}, m.sign = n.sign -> (m + n).sign = n.sign
  proof: by
  lia

中文:
引理 sign_add_eq_of_sign_eq
  结论: 对任意 {m n : 整数}, m.sign = n.sign -> (m + n).sign = n.sign
  证明: by
  lia
-/
lemma sign_add_eq_of_sign_eq : forall {m n : Int}, m.sign = n.sign -> (m + n).sign = n.sign := by
  lia

/-! ### toNat -/

/-
The following lemma is non-confluent with
```
simp only [*, @Int.lt_toNat, CharP.cast_eq_zero, @Nat.cast_pred, Int.ofNat_toNat]
```
from the default simp set, which simplifies the LHS to `max i 0 - 1`.
Therefore we mark this lemma as `@[simp high]`.
-/
@[simp high]
/--
lemma `toNat_pred_coe_of_pos` / 引理 `toNat_pred_coe_of_pos`

English:
lemma toNat_pred_coe_of_pos
  given: {i : Int} (h : 0 < i)
  statement: ((i.toNat - 1 : Nat) : Int) = i - 1
  proof: by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

中文:
引理 toNat_pred_coe_of_pos
  条件: {i : 整数} (h : 0 < i)
  结论: ((i.to自然数 - 1 : 自然数) : 整数) = i - 1
  证明: by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

Depends on / 依赖: Int.cast_ofNat_Int, Int.le_of_lt, cast_ofNat_Int, le_of_lt, lt_toNat, natCast_pred_of_pos, toNat_of_nonneg
-/
lemma toNat_pred_coe_of_pos {i : Int} (h : 0 < i) : ((i.toNat - 1 : Nat) : Int) = i - 1 := by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

/--
lemma `toNat_lt_of_ne_zero` / 引理 `toNat_lt_of_ne_zero`

English:
lemma toNat_lt_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  statement: m.toNat < n ↔ m < n
  proof: by lia

中文:
引理 toNat_lt_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: m.to自然数 < n ↔ m < n
  证明: by lia
-/
lemma toNat_lt_of_ne_zero {n : Nat} (hn : n != 0) : m.toNat < n ↔ m < n := by lia

/--
Definition of `natMod` / `natMod` 的定义

English:
definition natMod
  signature: (m n : Int)
  body: (m % n).toNat

中文:
定义 natMod
  签名: (m n : 整数)
  定义体: (m % n).toNat
-/
def natMod (m n : Int) : Nat := (m % n).toNat

/--
lemma `natMod_lt` / 引理 `natMod_lt`

English:
lemma natMod_lt
  given: {n : Nat} (hn : n != 0)
  statement: m.natMod n < n
  proof: (toNat_lt_of_ne_zero hn).2 emod_lt_of_pos _ by lia

中文:
引理 natMod_lt
  条件: {n : 自然数} (hn : n != 0)
  结论: m.natMod n < n
  证明: (toNat_lt_of_ne_zero hn).2 emod_lt_of_pos _ by lia

Depends on / 依赖: emod_lt_of_pos, toNat_lt_of_ne_zero
-/
lemma natMod_lt {n : Nat} (hn : n != 0) : m.natMod n < n :=
(toNat_lt_of_ne_zero hn).2 emod_lt_of_pos _ by lia

/--
lemma `pow_eq` / 引理 `pow_eq`

English:
lemma pow_eq
  given: (m : Int) (n : Nat)
  statement: m.pow n = m ^ n
  proof: rfl

中文:
引理 pow_eq
  条件: (m : 整数) (n : 自然数)
  结论: m.pow n = m ^ n
  证明: rfl
-/
@[simp] lemma pow_eq (m : Int) (n : Nat) : m.pow n = m ^ n := rfl

/--
lemma `gcd_ofNat_negSucc` / 引理 `gcd_ofNat_negSucc`

English:
lemma gcd_ofNat_negSucc
  given: (m n : Nat)
  statement: gcd m (negSucc n) = m.gcd (n + 1)
  proof: by simp [gcd]

中文:
引理 gcd_ofNat_negSucc
  条件: (m n : 自然数)
  结论: gcd m (negSucc n) = m.gcd (n + 1)
  证明: by simp [gcd]
-/
@[simp] lemma gcd_ofNat_negSucc (m n : Nat) : gcd m (negSucc n) = m.gcd (n + 1) := by simp [gcd]
/--
lemma `gcd_negSucc_ofNat` / 引理 `gcd_negSucc_ofNat`

English:
lemma gcd_negSucc_ofNat
  given: (m n : Nat)
  statement: gcd (negSucc m) n = (m + 1).gcd n
  proof: by simp [gcd]

中文:
引理 gcd_negSucc_ofNat
  条件: (m n : 自然数)
  结论: gcd (negSucc m) n = (m + 1).gcd n
  证明: by simp [gcd]
-/
@[simp] lemma gcd_negSucc_ofNat (m n : Nat) : gcd (negSucc m) n = (m + 1).gcd n := by simp [gcd]
/--
lemma `gcd_negSucc_negSucc` / 引理 `gcd_negSucc_negSucc`

English:
lemma gcd_negSucc_negSucc
  given: (m n : Nat)
  proof: by simp [gcd]

中文:
引理 gcd_negSucc_negSucc
  条件: (m n : 自然数)
  证明: by simp [gcd]
-/
@[simp] lemma gcd_negSucc_negSucc (m n : Nat) :
    (negSucc m).gcd (negSucc n) = (m + 1).gcd (n + 1) := by simp [gcd]

/--
theorem `gcd_right_comm` / 定理 `gcd_right_comm`

English:
theorem gcd_right_comm
  given: (a b c : Int)
  statement: gcd (gcd a b) c = gcd (gcd a c) b
  proof: by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

中文:
定理 gcd_right_comm
  条件: (a b c : 整数)
  结论: gcd (gcd a b) c = gcd (gcd a c) b
  证明: by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

Depends on / 依赖: gcd_assoc, gcd_comm
-/
theorem gcd_right_comm (a b c : Int) : gcd (gcd a b) c = gcd (gcd a c) b := by
  rw [gcd_assoc]; rw [gcd_assoc]; rw [gcd_comm b c]

end Int
