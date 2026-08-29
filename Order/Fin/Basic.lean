/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
module

public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Hom.Basic

/-!
# `Fin n` forms a bounded linear order

This file contains the linear ordered instance on `Fin n`.

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `Fin.orderIsoSubtype` : coercion to `{i // i < n}` as an `OrderIso`;
* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.valOrderEmb` : coercion to natural numbers as an `OrderEmbedding`;
* `Fin.succOrderEmb` : `Fin.succ` as an `OrderEmbedding`;
* `Fin.castLEOrderEmb h` : `Fin.castLE` as an `OrderEmbedding`, embed `Fin n` into `Fin m` when
  `h : n ≤ m`;
* `Fin.castOrderIso` : `Fin.cast` as an `OrderIso`, order isomorphism between `Fin n` and `Fin m`
  provided that `n = m`, see also `Equiv.finCongr`;
* `Fin.castAddOrderEmb m` : `Fin.castAdd` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccOrderEmb` : `Fin.castSucc` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatOrderEmb m i` : `Fin.addNat` as an `OrderEmbedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddOrderEmb n i` : `Fin.natAdd` as an `OrderEmbedding`, adds `n` on `i` on the left;
* `Fin.revOrderIso`: `Fin.rev` as an `OrderIso`, the antitone involution given by `i ↦ n-(i+1)`
-/

@[expose] public section

assert_not_exists Monoid

open Function Nat Set

namespace Fin
variable {m n : Nat}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Fin n)
  body: ⟨max x y, max_rec' (· < n) x.2 y.2⟩

中文:
实例 :
  签名: 最大值 (有限集 n)
  定义体: ⟨max x y, max_rec' (· < n) x.2 y.2⟩

Depends on / 依赖: max_rec
-/
instance : Max (Fin n) where max x y := ⟨max x y, max_rec' (· < n) x.2 y.2⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Fin n)
  body: ⟨min x y, min_rec' (· < n) x.2 y.2⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (有限集 n)
  定义体: ⟨min x y, min_rec' (· < n) x.2 y.2⟩

@[simp, norm_cast]

Depends on / 依赖: min_rec
-/
instance : Min (Fin n) where min x y := ⟨min x y, min_rec' (· < n) x.2 y.2⟩

@[simp, norm_cast]
/--
theorem `coe_max` / 定理 `coe_max`

English:
theorem coe_max
  given: (a b : Fin n)
  statement: ↑(max a b) = (max a b : Nat)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_max
  条件: (a b : 有限集 n)
  结论: ↑(最大值 a b) = (最大值 a b : 自然数)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_max (a b : Fin n) : ↑(max a b) = (max a b : Nat) := rfl

@[simp, norm_cast]
/--
theorem `coe_min` / 定理 `coe_min`

English:
theorem coe_min
  given: (a b : Fin n)
  statement: ↑(min a b) = (min a b : Nat)
  proof: rfl

中文:
定理 coe_min
  条件: (a b : 有限集 n)
  结论: ↑(最小值 a b) = (最小值 a b : 自然数)
  证明: rfl
-/
theorem coe_min (a b : Fin n) : ↑(min a b) = (min a b : Nat) := rfl

/--
theorem `compare_eq_compare_val` / 定理 `compare_eq_compare_val`

English:
theorem compare_eq_compare_val
  given: (a b : Fin n)
  statement: compare a b = compare a.val b.val
  proof: rfl

中文:
定理 compare_eq_compare_val
  条件: (a b : 有限集 n)
  结论: compare a b = compare a.val b.val
  证明: rfl
-/
theorem compare_eq_compare_val (a b : Fin n) : compare a b = compare a.val b.val := rfl

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder (Fin n)
  body: Fin.val_injective.linearOrder _
    Fin.le_iff_val_le_val Fin.lt_def coe_min coe_max compare_eq_compare_val

中文:
实例 instLinearOrder
  签名: : 线性序 (有限集 n)
  定义体: Fin.val_injective.linearOrder _
    Fin.le_iff_val_le_val Fin.lt_def coe_min coe_max compare_eq_compare_val

Depends on / 依赖: Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_injective.linearOrder, coe_max, coe_min, compare_eq_compare_val, le_iff_val_le_val, linearOrder, lt_def, val_injective
-/
instance instLinearOrder : LinearOrder (Fin n) :=
  Fin.val_injective.linearOrder _
    Fin.le_iff_val_le_val Fin.lt_def coe_min coe_max compare_eq_compare_val

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [NeZero n]
  body: rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le

中文:
实例 instBoundedOrder
  签名: [NeZero n]
  定义体: rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le
-/
instance instBoundedOrder [NeZero n] : BoundedOrder (Fin n) where
  top := rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le

/--
Instance `instBiheytingAlgebra` / 实例 `instBiheytingAlgebra`

English:
instance instBiheytingAlgebra
  signature: [NeZero n]
  body: LinearOrder.toBiheytingAlgebra (Fin n)

中文:
实例 instBiheytingAlgebra
  签名: [NeZero n]
  定义体: LinearOrder.toBiheytingAlgebra (Fin n)

Depends on / 依赖: LinearOrder, LinearOrder.toBiheytingAlgebra, toBiheytingAlgebra
-/
instance instBiheytingAlgebra [NeZero n] : BiheytingAlgebra (Fin n) :=
  LinearOrder.toBiheytingAlgebra (Fin n)

/- There is a slight asymmetry here, in the sense that `0` is of type `Fin n` when we have
`[NeZero n]` whereas `last n` is of type `Fin (n + 1)`. To address this properly would
require a change to std4, defining `NeZero n` and thus re-defining `last n`
(and possibly make its argument implicit) as `rev 0`, of type `Fin n`. As we can see from these
lemmas, this would be equivalent to the existing definition. -/


/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Fin n)
  body: inferInstance

中文:
实例 instPartialOrder
  签名: : 偏序 (有限集 n)
  定义体: inferInstance
-/
instance instPartialOrder : PartialOrder (Fin n) := inferInstance
/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (Fin n)
  body: inferInstance

中文:
实例 instLattice
  签名: : 格 (有限集 n)
  定义体: inferInstance
-/
instance instLattice : Lattice (Fin n) := inferInstance
/--
Instance `instHeytingAlgebra` / 实例 `instHeytingAlgebra`

English:
instance instHeytingAlgebra
  signature: [NeZero n]
  body: inferInstance

中文:
实例 instHeytingAlgebra
  签名: [NeZero n]
  定义体: inferInstance
-/
instance instHeytingAlgebra [NeZero n] : HeytingAlgebra (Fin n) := inferInstance
/--
Instance `instCoheytingAlgebra` / 实例 `instCoheytingAlgebra`

English:
instance instCoheytingAlgebra
  signature: [NeZero n]
  body: inferInstance

中文:
实例 instCoheytingAlgebra
  签名: [NeZero n]
  定义体: inferInstance
-/
instance instCoheytingAlgebra [NeZero n] : CoheytingAlgebra (Fin n) := inferInstance


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: n] : IsBotZeroClass (Fin n) where
  body: isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]

中文:
实例 [NeZero
  签名: n] : 是BotZero类 (有限集 n) where
  定义体: isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]

Depends on / 依赖: isBot_bot
-/
instance [NeZero n] : IsBotZeroClass (Fin n) where
  isBot_zero := isBot_bot

@[deprecated _root_.bot_eq_zero (since := "2026-05-07")]
/--
lemma `bot_eq_zero` / 引理 `bot_eq_zero`

English:
lemma bot_eq_zero
  given: (n : Nat) [NeZero n]
  statement: ⊥ = (0 : Fin n)
  proof: _root_.bot_eq_zero

中文:
引理 bot_eq_zero
  条件: (n : 自然数) [NeZero n]
  结论: ⊥ = (0 : 有限集 n)
  证明: _root_.bot_eq_zero
-/
protected lemma bot_eq_zero (n : Nat) [NeZero n] : ⊥ = (0 : Fin n) := _root_.bot_eq_zero

/--
lemma `top_eq_last` / 引理 `top_eq_last`

English:
lemma top_eq_last
  given: (n : Nat)
  statement: ⊤ = Fin.last n
  proof: rfl

中文:
引理 top_eq_last
  条件: (n : 自然数)
  结论: ⊤ = 有限集.last n
  证明: rfl
-/
lemma top_eq_last (n : Nat) : ⊤ = Fin.last n := rfl

/--
theorem `rev_bot` / 定理 `rev_bot`

English:
theorem rev_bot
  given: [NeZero n]
  statement: rev (⊥ : Fin n) = ⊤
  proof: rfl

中文:
定理 rev_bot
  条件: [NeZero n]
  结论: rev (⊥ : 有限集 n) = ⊤
  证明: rfl
-/
@[simp] theorem rev_bot [NeZero n] : rev (⊥ : Fin n) = ⊤ := rfl
/--
theorem `rev_top` / 定理 `rev_top`

English:
theorem rev_top
  given: [NeZero n]
  statement: rev (⊤ : Fin n) = ⊥
  proof: rev_rev _

中文:
定理 rev_top
  条件: [NeZero n]
  结论: rev (⊤ : 有限集 n) = ⊥
  证明: rev_rev _
-/
@[simp] theorem rev_top [NeZero n] : rev (⊤ : Fin n) = ⊥ := rev_rev _

/--
theorem `rev_zero_eq_top` / 定理 `rev_zero_eq_top`

English:
theorem rev_zero_eq_top
  given: (n : Nat) [NeZero n]
  statement: rev (0 : Fin n) = ⊤
  proof: rfl

中文:
定理 rev_zero_eq_top
  条件: (n : 自然数) [NeZero n]
  结论: rev (0 : 有限集 n) = ⊤
  证明: rfl
-/
theorem rev_zero_eq_top (n : Nat) [NeZero n] : rev (0 : Fin n) = ⊤ := rfl
/--
theorem `rev_last_eq_bot` / 定理 `rev_last_eq_bot`

English:
theorem rev_last_eq_bot
  given: (n : Nat)
  statement: rev (last n) = ⊥
  proof: by rw [rev_last, bot_eq_zero]

@[simp]

中文:
定理 rev_last_eq_bot
  条件: (n : 自然数)
  结论: rev (last n) = ⊥
  证明: by rw [rev_last, bot_eq_zero]

@[simp]

Depends on / 依赖: bot_eq_zero, rev_last
-/
theorem rev_last_eq_bot (n : Nat) : rev (last n) = ⊥ := by rw [rev_last, bot_eq_zero]

@[simp]
/--
theorem `succ_top` / 定理 `succ_top`

English:
theorem succ_top
  given: (n : Nat) [NeZero n]
  statement: (⊤ : Fin n).succ = ⊤
  proof: by
  rw [← rev_zero_eq_top]; rw [← rev_zero_eq_top]; rw [← rev_castSucc]; rw [castSucc_zero']

@[simp]

中文:
定理 succ_top
  条件: (n : 自然数) [NeZero n]
  结论: (⊤ : 有限集 n).succ = ⊤
  证明: by
  rw [← rev_zero_eq_top]; rw [← rev_zero_eq_top]; rw [← rev_castSucc]; rw [castSucc_zero']

@[simp]

Depends on / 依赖: castSucc_zero, rev_castSucc, rev_zero_eq_top
-/
theorem succ_top (n : Nat) [NeZero n] : (⊤ : Fin n).succ = ⊤ := by
  rw [← rev_zero_eq_top]; rw [← rev_zero_eq_top]; rw [← rev_castSucc]; rw [castSucc_zero']

@[simp]
/--
theorem `val_top` / 定理 `val_top`

English:
theorem val_top
  given: (n : Nat) [NeZero n]
  statement: ((⊤ : Fin n) : Nat) = n - 1
  proof: rfl

@[simp]

中文:
定理 val_top
  条件: (n : 自然数) [NeZero n]
  结论: ((⊤ : 有限集 n) : 自然数) = n - 1
  证明: rfl

@[simp]
-/
theorem val_top (n : Nat) [NeZero n] : ((⊤ : Fin n) : Nat) = n - 1 := rfl

@[simp]
/--
theorem `zero_eq_top` / 定理 `zero_eq_top`

English:
theorem zero_eq_top
  given: {n : Nat} [NeZero n]
  statement: (0 : Fin n) = ⊤ ↔ n = 1
  proof: by
  rw [← bot_eq_zero]; rw [subsingleton_iff_bot_eq_top]; rw [subsingleton_iff_le_one]; rw [le_one_iff_eq_zero_or_eq_one]; rw [or_iff_right (NeZero.ne n)]

@[simp]

中文:
定理 zero_eq_top
  条件: {n : 自然数} [NeZero n]
  结论: (0 : 有限集 n) = ⊤ ↔ n = 1
  证明: by
  rw [← bot_eq_zero]; rw [subsingleton_iff_bot_eq_top]; rw [subsingleton_iff_le_one]; rw [le_one_iff_eq_zero_or_eq_one]; rw [or_iff_right (NeZero.ne n)]

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, bot_eq_zero, le_one_iff_eq_zero_or_eq_one, or_iff_right, subsingleton_iff_bot_eq_top, subsingleton_iff_le_one
-/
theorem zero_eq_top {n : Nat} [NeZero n] : (0 : Fin n) = ⊤ ↔ n = 1 := by
  rw [← bot_eq_zero]; rw [subsingleton_iff_bot_eq_top]; rw [subsingleton_iff_le_one]; rw [le_one_iff_eq_zero_or_eq_one]; rw [or_iff_right (NeZero.ne n)]

@[simp]
/--
theorem `top_eq_zero` / 定理 `top_eq_zero`

English:
theorem top_eq_zero
  given: {n : Nat} [NeZero n]
  statement: (⊤ : Fin n) = 0 ↔ n = 1
  proof: eq_comm.trans zero_eq_top

@[simp]

中文:
定理 top_eq_zero
  条件: {n : 自然数} [NeZero n]
  结论: (⊤ : 有限集 n) = 0 ↔ n = 1
  证明: eq_comm.trans zero_eq_top

@[simp]

Depends on / 依赖: eq_comm, eq_comm.trans, zero_eq_top
-/
theorem top_eq_zero {n : Nat} [NeZero n] : (⊤ : Fin n) = 0 ↔ n = 1 :=
  eq_comm.trans zero_eq_top

@[simp]
/--
theorem `cast_top` / 定理 `cast_top`

English:
theorem cast_top
  given: {m n : Nat} [NeZero m] [NeZero n] (h : m = n)
  statement: (⊤ : Fin m).cast h = ⊤
  proof: by
  simp [← val_inj, h]

中文:
定理 cast_top
  条件: {m n : 自然数} [NeZero m] [NeZero n] (h : m = n)
  结论: (⊤ : 有限集 m).cast h = ⊤
  证明: by
  simp [← val_inj, h]

Depends on / 依赖: val_inj
-/
theorem cast_top {m n : Nat} [NeZero m] [NeZero n] (h : m = n) : (⊤ : Fin m).cast h = ⊤ := by
  simp [← val_inj, h]

section ToFin
variable {α : Type*} [Preorder α] {f : α -> Fin (n + 1)}

/--
lemma `strictMono_pred_comp` / 引理 `strictMono_pred_comp`

English:
lemma strictMono_pred_comp
  given: (hf : forall a, f a != 0) (hf₂ : StrictMono f)
  proof: fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)

中文:
引理 strictMono_pred_comp
  条件: (hf : 对任意 a, f a != 0) (hf₂ : 严格递增 f)
  证明: fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)

Depends on / 依赖: pred_lt_pred_iff
-/
lemma strictMono_pred_comp (hf : forall a, f a != 0) (hf₂ : StrictMono f) :
    StrictMono (fun a => pred (f a) (hf a)) := fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)

/--
lemma `monotone_pred_comp` / 引理 `monotone_pred_comp`

English:
lemma monotone_pred_comp
  given: (hf : forall a, f a != 0) (hf₂ : Monotone f)
  proof: fun _ _ h => pred_le_pred_iff.2 (hf₂ h)

中文:
引理 monotone_pred_comp
  条件: (hf : 对任意 a, f a != 0) (hf₂ : 递增 f)
  证明: fun _ _ h => pred_le_pred_iff.2 (hf₂ h)

Depends on / 依赖: pred_le_pred_iff
-/
lemma monotone_pred_comp (hf : forall a, f a != 0) (hf₂ : Monotone f) :
    Monotone (fun a => pred (f a) (hf a)) := fun _ _ h => pred_le_pred_iff.2 (hf₂ h)

/--
lemma `strictMono_castPred_comp` / 引理 `strictMono_castPred_comp`

English:
lemma strictMono_castPred_comp
  given: (hf : forall a, f a != last n) (hf₂ : StrictMono f)
  proof: fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)

中文:
引理 strictMono_castPred_comp
  条件: (hf : 对任意 a, f a != last n) (hf₂ : 严格递增 f)
  证明: fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)

Depends on / 依赖: castPred_lt_castPred_iff
-/
lemma strictMono_castPred_comp (hf : forall a, f a != last n) (hf₂ : StrictMono f) :
    StrictMono (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)

/--
lemma `monotone_castPred_comp` / 引理 `monotone_castPred_comp`

English:
lemma monotone_castPred_comp
  given: (hf : forall a, f a != last n) (hf₂ : Monotone f)
  proof: fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

中文:
引理 monotone_castPred_comp
  条件: (hf : 对任意 a, f a != last n) (hf₂ : 递增 f)
  证明: fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

Depends on / 依赖: castPred_le_castPred_iff
-/
lemma monotone_castPred_comp (hf : forall a, f a != last n) (hf₂ : Monotone f) :
    Monotone (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

end ToFin

section FromFin
variable {α : Type*} [Preorder α] {f : Fin (n + 1) -> α}

/--
lemma `strictMono_iff_lt_succ` / 引理 `strictMono_iff_lt_succ`

English:
lemma strictMono_iff_lt_succ
  statement: StrictMono f ↔ forall i : Fin n, f (castSucc i) < f i.succ
  proof: liftFun_iff_succ (· < ·)

中文:
引理 strictMono_iff_lt_succ
  结论: 严格递增 f ↔ 对任意 i : 有限集 n, f (castSucc i) < f i.succ
  证明: liftFun_iff_succ (· < ·)

Depends on / 依赖: liftFun_iff_succ
-/
lemma strictMono_iff_lt_succ : StrictMono f ↔ forall i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)

/--
lemma `monotone_iff_le_succ` / 引理 `monotone_iff_le_succ`

English:
lemma monotone_iff_le_succ
  statement: Monotone f ↔ forall i : Fin n, f (castSucc i) <= f i.succ
  proof: monotone_iff_forall_lt.trans liftFun_iff_succ (· <= ·)

中文:
引理 monotone_iff_le_succ
  结论: 递增 f ↔ 对任意 i : 有限集 n, f (castSucc i) <= f i.succ
  证明: monotone_iff_forall_lt.trans liftFun_iff_succ (· <= ·)

Depends on / 依赖: liftFun_iff_succ, monotone_iff_forall_lt, monotone_iff_forall_lt.trans
-/
lemma monotone_iff_le_succ : Monotone f ↔ forall i : Fin n, f (castSucc i) <= f i.succ :=
monotone_iff_forall_lt.trans liftFun_iff_succ (· <= ·)

/--
lemma `strictAnti_iff_succ_lt` / 引理 `strictAnti_iff_succ_lt`

English:
lemma strictAnti_iff_succ_lt
  statement: StrictAnti f ↔ forall i : Fin n, f i.succ < f (castSucc i)
  proof: liftFun_iff_succ (· > ·)

中文:
引理 strictAnti_iff_succ_lt
  结论: 严格递减 f ↔ 对任意 i : 有限集 n, f i.succ < f (castSucc i)
  证明: liftFun_iff_succ (· > ·)

Depends on / 依赖: liftFun_iff_succ
-/
lemma strictAnti_iff_succ_lt : StrictAnti f ↔ forall i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)

/--
lemma `antitone_iff_succ_le` / 引理 `antitone_iff_succ_le`

English:
lemma antitone_iff_succ_le
  statement: Antitone f ↔ forall i : Fin n, f i.succ <= f (castSucc i)
  proof: antitone_iff_forall_lt.trans liftFun_iff_succ (· >= ·)

中文:
引理 antitone_iff_succ_le
  结论: 递减 f ↔ 对任意 i : 有限集 n, f i.succ <= f (castSucc i)
  证明: antitone_iff_forall_lt.trans liftFun_iff_succ (· >= ·)

Depends on / 依赖: antitone_iff_forall_lt, antitone_iff_forall_lt.trans, liftFun_iff_succ
-/
lemma antitone_iff_succ_le : Antitone f ↔ forall i : Fin n, f i.succ <= f (castSucc i) :=
antitone_iff_forall_lt.trans liftFun_iff_succ (· >= ·)

/--
lemma `orderHom_injective_iff` / 引理 `orderHom_injective_iff`

English:
lemma orderHom_injective_iff
  given: {α : Type*} [PartialOrder α] {n : Nat} (f : Fin (n + 1) ->o α)
  proof: by
  constructor
  · intro hf i hi
    have := hf hi
    simp [Fin.ext_iff] at this
  · intro hf
    refine (strictMono_iff_lt_succ (f := f).2 fun i => ?_).injective
    exact lt_of_le_of_ne (f.monotone (Fin.castSucc_le_succ i)) (hf i)

中文:
引理 orderHom_injective_iff
  条件: {α : 类型} [偏序 α] {n : 自然数} (f : 有限集 (n + 1) ->o α)
  证明: by
  constructor
  · intro hf i hi
    have := hf hi
    simp [Fin.ext_iff] at this
  · intro hf
    refine (strictMono_iff_lt_succ (f := f).2 fun i => ?_).injective
    exact lt_of_le_of_ne (f.monotone (Fin.castSucc_le_succ i)) (hf i)

Depends on / 依赖: Fin.castSucc_le_succ, Fin.ext_iff, castSucc_le_succ, ext_iff, f.monotone, injective, lt_of_le_of_ne, monotone, strictMono_iff_lt_succ
-/
lemma orderHom_injective_iff {α : Type*} [PartialOrder α] {n : Nat} (f : Fin (n + 1) ->o α) :
    Function.Injective f ↔ forall (i : Fin n), f i.castSucc != f i.succ := by
  constructor
  · intro hf i hi
    have := hf hi
    simp [Fin.ext_iff] at this
  · intro hf
    refine (strictMono_iff_lt_succ (f := f).2 fun i => ?_).injective
    exact lt_of_le_of_ne (f.monotone (Fin.castSucc_le_succ i)) (hf i)

end FromFin


/--
lemma `val_strictMono` / 引理 `val_strictMono`

English:
lemma val_strictMono
  statement: StrictMono (val : Fin n -> Nat)
  proof: fun _ _ => id

中文:
引理 val_strictMono
  结论: 严格递增 (val : 有限集 n -> 自然数)
  证明: fun _ _ => id
-/
lemma val_strictMono : StrictMono (val : Fin n -> Nat) := fun _ _ => id
/--
lemma `cast_strictMono` / 引理 `cast_strictMono`

English:
lemma cast_strictMono
  given: {k l : Nat} (h : k = l)
  statement: StrictMono (Fin.cast h)
  proof: fun {_ _} h => h

中文:
引理 cast_strictMono
  条件: {k l : 自然数} (h : k = l)
  结论: 严格递增 (有限集.cast h)
  证明: fun {_ _} h => h
-/
lemma cast_strictMono {k l : Nat} (h : k = l) : StrictMono (Fin.cast h) := fun {_ _} h => h

/--
lemma `strictMono_succ` / 引理 `strictMono_succ`

English:
lemma strictMono_succ
  statement: StrictMono (succ : Fin n -> Fin (n + 1))
  proof: fun _ _ => succ_lt_succ

中文:
引理 strictMono_succ
  结论: 严格递增 (succ : 有限集 n -> 有限集 (n + 1))
  证明: fun _ _ => succ_lt_succ

Depends on / 依赖: succ_lt_succ
-/
lemma strictMono_succ : StrictMono (succ : Fin n -> Fin (n + 1)) := fun _ _ => succ_lt_succ
/--
lemma `strictMono_castLE` / 引理 `strictMono_castLE`

English:
lemma strictMono_castLE
  given: (h : n <= m)
  statement: StrictMono (castLE h : Fin n -> Fin m)
  proof: fun _ _ => id

中文:
引理 strictMono_castLE
  条件: (h : n <= m)
  结论: 严格递增 (castLE h : 有限集 n -> 有限集 m)
  证明: fun _ _ => id
-/
lemma strictMono_castLE (h : n <= m) : StrictMono (castLE h : Fin n -> Fin m) := fun _ _ => id
/--
lemma `strictMono_castAdd` / 引理 `strictMono_castAdd`

English:
lemma strictMono_castAdd
  given: (m)
  statement: StrictMono (castAdd m : Fin n -> Fin (n + m))
  proof: strictMono_castLE _

中文:
引理 strictMono_castAdd
  条件: (m)
  结论: 严格递增 (castAdd m : 有限集 n -> 有限集 (n + m))
  证明: strictMono_castLE _

Depends on / 依赖: strictMono_castLE
-/
lemma strictMono_castAdd (m) : StrictMono (castAdd m : Fin n -> Fin (n + m)) := strictMono_castLE _
/--
lemma `strictMono_castSucc` / 引理 `strictMono_castSucc`

English:
lemma strictMono_castSucc
  statement: StrictMono (castSucc : Fin n -> Fin (n + 1))
  proof: strictMono_castAdd _

中文:
引理 strictMono_castSucc
  结论: 严格递增 (castSucc : 有限集 n -> 有限集 (n + 1))
  证明: strictMono_castAdd _

Depends on / 依赖: strictMono_castAdd
-/
lemma strictMono_castSucc : StrictMono (castSucc : Fin n -> Fin (n + 1)) := strictMono_castAdd _
/--
lemma `strictMono_natAdd` / 引理 `strictMono_natAdd`

English:
lemma strictMono_natAdd
  given: (n)
  statement: StrictMono (natAdd n : Fin m -> Fin (n + m))
  proof: fun i j h => Nat.add_lt_add_left (show i.val < j.val from h) _

中文:
引理 strictMono_natAdd
  条件: (n)
  结论: 严格递增 (natAdd n : 有限集 m -> 有限集 (n + m))
  证明: fun i j h => Nat.add_lt_add_left (show i.val < j.val from h) _

Depends on / 依赖: Nat.add_lt_add_left, add_lt_add_left, i.val, j.val
-/
lemma strictMono_natAdd (n) : StrictMono (natAdd n : Fin m -> Fin (n + m)) :=
  fun i j h => Nat.add_lt_add_left (show i.val < j.val from h) _
/--
lemma `strictMono_addNat` / 引理 `strictMono_addNat`

English:
lemma strictMono_addNat
  given: (m)
  statement: StrictMono ((addNat · m) : Fin n -> Fin (n + m))
  proof: fun i j h => Nat.add_lt_add_right (show i.val < j.val from h) _

中文:
引理 strictMono_add自然数
  条件: (m)
  结论: 严格递增 ((add自然数 · m) : 有限集 n -> 有限集 (n + m))
  证明: fun i j h => Nat.add_lt_add_right (show i.val < j.val from h) _

Depends on / 依赖: Nat.add_lt_add_right, add_lt_add_right, i.val, j.val
-/
lemma strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n -> Fin (n + m)) :=
  fun i j h => Nat.add_lt_add_right (show i.val < j.val from h) _

/--
lemma `strictMono_succAbove` / 引理 `strictMono_succAbove`

English:
lemma strictMono_succAbove
  given: (p : Fin (n + 1))
  statement: StrictMono (succAbove p)
  proof: strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun _ => castSucc_lt_succ.le

中文:
引理 strictMono_succAbove
  条件: (p : 有限集 (n + 1))
  结论: 严格递增 (succAbove p)
  证明: strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun _ => castSucc_lt_succ.le

Depends on / 依赖: castSucc_lt_castSucc_iff, castSucc_lt_castSucc_iff.mpr, castSucc_lt_succ, castSucc_lt_succ.le, strictMono_castSucc, strictMono_castSucc.ite, strictMono_succ
-/
lemma strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun _ => castSucc_lt_succ.le

variable {p : Fin (n + 1)} {i j : Fin n}

@[simp]
/--
lemma `succAbove_inj` / 引理 `succAbove_inj`

English:
lemma succAbove_inj
  statement: succAbove p i = succAbove p j ↔ i = j
  proof: (strictMono_succAbove p).injective.eq_iff

@[simp, gcongr]

中文:
引理 succAbove_inj
  结论: succAbove p i = succAbove p j ↔ i = j
  证明: (strictMono_succAbove p).injective.eq_iff

@[simp, gcongr]

Depends on / 依赖: eq_iff, injective, injective.eq_iff, strictMono_succAbove
-/
lemma succAbove_inj : succAbove p i = succAbove p j ↔ i = j :=
  (strictMono_succAbove p).injective.eq_iff

@[simp, gcongr]
/--
lemma `succAbove_le_succAbove_iff` / 引理 `succAbove_le_succAbove_iff`

English:
lemma succAbove_le_succAbove_iff
  statement: succAbove p i <= succAbove p j ↔ i <= j
  proof: (strictMono_succAbove p).le_iff_le

@[simp, gcongr]

中文:
引理 succAbove_le_succAbove_iff
  结论: succAbove p i <= succAbove p j ↔ i <= j
  证明: (strictMono_succAbove p).le_iff_le

@[simp, gcongr]

Depends on / 依赖: le_iff_le, strictMono_succAbove
-/
lemma succAbove_le_succAbove_iff : succAbove p i <= succAbove p j ↔ i <= j :=
  (strictMono_succAbove p).le_iff_le

@[simp, gcongr]
/--
lemma `succAbove_lt_succAbove_iff` / 引理 `succAbove_lt_succAbove_iff`

English:
lemma succAbove_lt_succAbove_iff
  statement: succAbove p i < succAbove p j ↔ i < j
  proof: (strictMono_succAbove p).lt_iff_lt

@[simp]

中文:
引理 succAbove_lt_succAbove_iff
  结论: succAbove p i < succAbove p j ↔ i < j
  证明: (strictMono_succAbove p).lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, strictMono_succAbove
-/
lemma succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j :=
  (strictMono_succAbove p).lt_iff_lt

@[simp]
/--
theorem `natAdd_inj` / 定理 `natAdd_inj`

English:
theorem natAdd_inj
  given: (m) {i j : Fin n}
  statement: natAdd m i = natAdd m j ↔ i = j
  proof: (strictMono_natAdd _).injective.eq_iff

中文:
定理 natAdd_inj
  条件: (m) {i j : 有限集 n}
  结论: natAdd m i = natAdd m j ↔ i = j
  证明: (strictMono_natAdd _).injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff, strictMono_natAdd
-/
theorem natAdd_inj (m) {i j : Fin n} : natAdd m i = natAdd m j ↔ i = j :=
  (strictMono_natAdd _).injective.eq_iff

/--
theorem `natAdd_injective` / 定理 `natAdd_injective`

English:
theorem natAdd_injective
  given: (m n : Nat)
  proof: (strictMono_natAdd _).injective

@[simp, gcongr]

中文:
定理 natAdd_injective
  条件: (m n : 自然数)
  证明: (strictMono_natAdd _).injective

@[simp, gcongr]

Depends on / 依赖: injective, strictMono_natAdd
-/
theorem natAdd_injective (m n : Nat) :
    Function.Injective (Fin.natAdd n : Fin m -> _) :=
  (strictMono_natAdd _).injective

@[simp, gcongr]
/--
theorem `natAdd_le_natAdd_iff` / 定理 `natAdd_le_natAdd_iff`

English:
theorem natAdd_le_natAdd_iff
  given: (m) {i j : Fin n}
  statement: natAdd m i <= natAdd m j ↔ i <= j
  proof: (strictMono_natAdd _).le_iff_le

@[simp, gcongr]

中文:
定理 natAdd_le_natAdd_iff
  条件: (m) {i j : 有限集 n}
  结论: natAdd m i <= natAdd m j ↔ i <= j
  证明: (strictMono_natAdd _).le_iff_le

@[simp, gcongr]

Depends on / 依赖: le_iff_le, strictMono_natAdd
-/
theorem natAdd_le_natAdd_iff (m) {i j : Fin n} : natAdd m i <= natAdd m j ↔ i <= j :=
  (strictMono_natAdd _).le_iff_le

@[simp, gcongr]
/--
theorem `natAdd_lt_natAdd_iff` / 定理 `natAdd_lt_natAdd_iff`

English:
theorem natAdd_lt_natAdd_iff
  given: (m) {i j : Fin n}
  statement: natAdd m i < natAdd m j ↔ i < j
  proof: (strictMono_natAdd _).lt_iff_lt

@[simp]

中文:
定理 natAdd_lt_natAdd_iff
  条件: (m) {i j : 有限集 n}
  结论: natAdd m i < natAdd m j ↔ i < j
  证明: (strictMono_natAdd _).lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, strictMono_natAdd
-/
theorem natAdd_lt_natAdd_iff (m) {i j : Fin n} : natAdd m i < natAdd m j ↔ i < j :=
  (strictMono_natAdd _).lt_iff_lt

@[simp]
/--
theorem `addNat_inj` / 定理 `addNat_inj`

English:
theorem addNat_inj
  given: (m) {i j : Fin n}
  statement: i.addNat m = j.addNat m ↔ i = j
  proof: (strictMono_addNat _).injective.eq_iff

@[simp, gcongr]

中文:
定理 add自然数_inj
  条件: (m) {i j : 有限集 n}
  结论: i.add自然数 m = j.add自然数 m ↔ i = j
  证明: (strictMono_addNat _).injective.eq_iff

@[simp, gcongr]

Depends on / 依赖: eq_iff, injective, injective.eq_iff, strictMono_addNat
-/
theorem addNat_inj (m) {i j : Fin n} : i.addNat m = j.addNat m ↔ i = j :=
  (strictMono_addNat _).injective.eq_iff

@[simp, gcongr]
/--
theorem `addNat_le_addNat_iff` / 定理 `addNat_le_addNat_iff`

English:
theorem addNat_le_addNat_iff
  given: (m) {i j : Fin n}
  statement: i.addNat m <= j.addNat m ↔ i <= j
  proof: (strictMono_addNat _).le_iff_le

@[simp, gcongr]

中文:
定理 add自然数_le_add自然数_iff
  条件: (m) {i j : 有限集 n}
  结论: i.add自然数 m <= j.add自然数 m ↔ i <= j
  证明: (strictMono_addNat _).le_iff_le

@[simp, gcongr]

Depends on / 依赖: le_iff_le, strictMono_addNat
-/
theorem addNat_le_addNat_iff (m) {i j : Fin n} : i.addNat m <= j.addNat m ↔ i <= j :=
  (strictMono_addNat _).le_iff_le

@[simp, gcongr]
/--
theorem `addNat_lt_addNat_iff` / 定理 `addNat_lt_addNat_iff`

English:
theorem addNat_lt_addNat_iff
  given: (m) {i j : Fin n}
  statement: i.addNat m < j.addNat m ↔ i < j
  proof: (strictMono_addNat _).lt_iff_lt

@[simp, gcongr]

中文:
定理 add自然数_lt_add自然数_iff
  条件: (m) {i j : 有限集 n}
  结论: i.add自然数 m < j.add自然数 m ↔ i < j
  证明: (strictMono_addNat _).lt_iff_lt

@[simp, gcongr]

Depends on / 依赖: lt_iff_lt, strictMono_addNat
-/
theorem addNat_lt_addNat_iff (m) {i j : Fin n} : i.addNat m < j.addNat m ↔ i < j :=
  (strictMono_addNat _).lt_iff_lt

@[simp, gcongr]
/--
theorem `castLE_le_castLE_iff` / 定理 `castLE_le_castLE_iff`

English:
theorem castLE_le_castLE_iff
  given: {i j : Fin n} (h : n <= m)
  statement: i.castLE h <= j.castLE h ↔ i <= j
  proof: .rfl

@[simp, gcongr]

中文:
定理 castLE_le_castLE_iff
  条件: {i j : 有限集 n} (h : n <= m)
  结论: i.castLE h <= j.castLE h ↔ i <= j
  证明: .rfl

@[simp, gcongr]
-/
theorem castLE_le_castLE_iff {i j : Fin n} (h : n <= m) : i.castLE h <= j.castLE h ↔ i <= j := .rfl

@[simp, gcongr]
/--
theorem `castLE_lt_castLE_iff` / 定理 `castLE_lt_castLE_iff`

English:
theorem castLE_lt_castLE_iff
  given: {i j : Fin n} (h : n <= m)
  statement: i.castLE h < j.castLE h ↔ i < j
  proof: .rfl

中文:
定理 castLE_lt_castLE_iff
  条件: {i j : 有限集 n} (h : n <= m)
  结论: i.castLE h < j.castLE h ↔ i < j
  证明: .rfl
-/
theorem castLE_lt_castLE_iff {i j : Fin n} (h : n <= m) : i.castLE h < j.castLE h ↔ i < j := .rfl

/--
lemma `predAbove_right_monotone` / 引理 `predAbove_right_monotone`

English:
lemma predAbove_right_monotone
  given: (p : Fin n)
  statement: Monotone p.predAbove
  proof: fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, val_pred]
  · exact pred_le_pred H
  · calc
      _ <= _ := Nat.pred_le _
      _ <= _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H

中文:
引理 predAbove_right_monotone
  条件: (p : 有限集 n)
  结论: 递增 p.predAbove
  证明: fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, val_pred]
  · exact pred_le_pred H
  · calc
      _ <= _ := Nat.pred_le _
      _ <= _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H

Depends on / 依赖: Nat.pred_le, all_goals, le_iff_val_le_val, le_pred_of_lt, not_lt, not_lt.mp, predAbove, pred_le, pred_le_pred, split_ifs, trans_lt, val_pred
-/
lemma predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, val_pred]
  · exact pred_le_pred H
  · calc
      _ <= _ := Nat.pred_le _
      _ <= _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H

/--
lemma `predAbove_left_monotone` / 引理 `predAbove_left_monotone`

English:
lemma predAbove_left_monotone
  given: (i : Fin (n + 1))
  statement: Monotone fun p => predAbove p i
  proof: fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_ge
  · rfl

@[gcongr]

中文:
引理 predAbove_left_monotone
  条件: (i : 有限集 (n + 1))
  结论: 递增 fun p => predAbove p i
  证明: fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_ge
  · rfl

@[gcongr]

Depends on / 依赖: absurd, castSucc_lt_castSucc_iff, castSucc_lt_castSucc_iff.mpr, hb.trans_le, le_of_not_gt, not_ge, predAbove, pred_le, split_ifs, this.not_ge, trans_le
-/
lemma predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p => predAbove p i := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_ge
  · rfl

@[gcongr]
/--
lemma `predAbove_le_predAbove` / 引理 `predAbove_le_predAbove`

English:
lemma predAbove_le_predAbove
  given: {p q : Fin n} (hpq : p <= q) {i j : Fin (n + 1)} (hij : i <= j)
  proof: (predAbove_right_monotone p hij).trans (predAbove_left_monotone j hpq)

中文:
引理 predAbove_le_predAbove
  条件: {p q : 有限集 n} (hpq : p <= q) {i j : 有限集 (n + 1)} (hij : i <= j)
  证明: (predAbove_right_monotone p hij).trans (predAbove_left_monotone j hpq)

Depends on / 依赖: predAbove_left_monotone, predAbove_right_monotone
-/
lemma predAbove_le_predAbove {p q : Fin n} (hpq : p <= q) {i j : Fin (n + 1)} (hij : i <= j) :
    p.predAbove i <= q.predAbove j :=
  (predAbove_right_monotone p hij).trans (predAbove_left_monotone j hpq)

/--
Definition of `predAboveOrderHom` / `predAboveOrderHom` 的定义

English:
definition predAboveOrderHom
  signature: (p : Fin n)
  body: ⟨p.predAbove, p.predAbove_right_monotone⟩

中文:
定义 predAboveOrderHom
  签名: (p : 有限集 n)
  定义体: ⟨p.predAbove, p.predAbove_right_monotone⟩
-/
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) ->o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩

/--
lemma `predAbove_left_injective` / 引理 `predAbove_left_injective`

English:
lemma predAbove_left_injective
  statement: Injective (@predAbove n)
  proof: by
  intro i j hij
  obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.2 i.size_positive
  wlog! h : i < j generalizing i j
  · obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  replace hij := congr_fun hij i.succ
  rw [predAbove_succ_self]; rw [Fin.predAbove_of_le_castSucc _ _ (by simpa)]; rw [← Fin.castSucc_inj]; rw [castSucc_castPred] at hij
  exact (i.castSucc_lt_succ.ne hij).elim

中文:
引理 predAbove_left_injective
  结论: 单射 (@predAbove n)
  证明: by
  intro i j hij
  obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.2 i.size_positive
  wlog! h : i < j generalizing i j
  · obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  replace hij := congr_fun hij i.succ
  rw [predAbove_succ_self]; rw [Fin.predAbove_of_le_castSucc _ _ (by simpa)]; rw [← Fin.castSucc_inj]; rw [castSucc_castPred] at hij
  exact (i.castSucc_lt_succ.ne hij).elim

Depends on / 依赖: Fin.castSucc_inj, Fin.predAbove_of_le_castSucc, Nat.exists_add_one_eq, castSucc_castPred, castSucc_inj, castSucc_lt_succ, congr_fun, exists_add_one_eq, generalizing, h.lt_or_eq, hij.symm, i.castSucc_lt_succ.ne, i.size_positive, i.succ, lt_or_eq, predAbove_of_le_castSucc, predAbove_succ_self, replace, size_positive
-/
lemma predAbove_left_injective : Injective (@predAbove n) := by
  intro i j hij
  obtain ⟨n, rfl⟩ := Nat.exists_add_one_eq.2 i.size_positive
  wlog! h : i < j generalizing i j
  · obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  replace hij := congr_fun hij i.succ
  rw [predAbove_succ_self]; rw [Fin.predAbove_of_le_castSucc _ _ (by simpa)]; rw [← Fin.castSucc_inj]; rw [castSucc_castPred] at hij
  exact (i.castSucc_lt_succ.ne hij).elim

/--
lemma `predAbove_left_inj` / 引理 `predAbove_left_inj`

English:
lemma predAbove_left_inj
  given: {x y : Fin n}
  statement: x.predAbove = y.predAbove ↔ x = y
  proof: predAbove_left_injective.eq_iff

中文:
引理 predAbove_left_inj
  条件: {x y : 有限集 n}
  结论: x.predAbove = y.predAbove ↔ x = y
  证明: predAbove_left_injective.eq_iff
-/
@[simp] lemma predAbove_left_inj {x y : Fin n} : x.predAbove = y.predAbove ↔ x = y :=
  predAbove_left_injective.eq_iff

/-! #### Order isomorphisms -/

/-- The equivalence `Fin n ≃ {i // i < n}` is an order isomorphism. -/
@[simps! apply symm_apply]
/--
Definition of `orderIsoSubtype` / `orderIsoSubtype` 的定义

English:
definition orderIsoSubtype
  signature: : Fin n ≃o {i // i < n}
  body: equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

中文:
定义 orderIsoSubtype
  签名: : 有限集 n ≃o {i // i < n}
  定义体: equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

Depends on / 依赖: Monotone, equivSubtype, equivSubtype.toOrderIso, toOrderIso
-/
def orderIsoSubtype : Fin n ≃o {i // i < n} :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

/-- `Fin.cast` as an `OrderIso`.

`castOrderIso eq i` embeds `i` into an equal `Fin` type. -/
@[simps]
/--
Definition of `castOrderIso` / `castOrderIso` 的定义

English:
definition castOrderIso
  signature: (eq : n = m)
  body: ⟨Fin.cast eq, Fin.cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq

@[simp]

中文:
定义 castOrderIso
  签名: (eq : n = m)
  定义体: ⟨Fin.cast eq, Fin.cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq

@[simp]

Depends on / 依赖: Fin.cast, eq.symm, leftInverse_cast, rightInverse_cast
-/
def castOrderIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨Fin.cast eq, Fin.cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq

@[simp]
/--
lemma `symm_castOrderIso` / 引理 `symm_castOrderIso`

English:
lemma symm_castOrderIso
  given: (h : n = m)
  statement: (castOrderIso h).symm = castOrderIso h.symm
  proof: by subst h; rfl

@[simp]

中文:
引理 symm_castOrderIso
  条件: (h : n = m)
  结论: (castOrderIso h).symm = castOrderIso h.symm
  证明: by subst h; rfl

@[simp]
-/
lemma symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm := by subst h; rfl

@[simp]
/--
lemma `castOrderIso_refl` / 引理 `castOrderIso_refl`

English:
lemma castOrderIso_refl
  given: (h : n = n := rfl)
  statement: castOrderIso h = OrderIso.refl (Fin n)
  proof: by ext; simp

中文:
引理 castOrderIso_refl
  条件: (h : n = n := rfl)
  结论: castOrderIso h = OrderIso.refl (有限集 n)
  证明: by ext; simp

Depends on / 依赖: OrderIso, OrderIso.refl, castOrderIso
-/
lemma castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; simp

/--
lemma `castOrderIso_toEquiv` / 引理 `castOrderIso_toEquiv`

English:
lemma castOrderIso_toEquiv
  given: (h : n = m)
  statement: (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl)
  proof: by
  subst h; rfl

中文:
引理 castOrderIso_toEquiv
  条件: (h : n = m)
  结论: (castOrderIso h).toEquiv = 等价.cast (h ▸ rfl)
  证明: by
  subst h; rfl
-/
lemma castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; rfl

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
/--
Definition of `revOrderIso` / `revOrderIso` 的定义

English:
definition revOrderIso
  signature: : (Fin n)ᵒᵈ ≃o Fin n
  body: ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩

@[simp]

中文:
定义 revOrderIso
  签名: : (有限集 n)ᵒᵈ ≃o 有限集 n
  定义体: ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩

@[simp]

Depends on / 依赖: OrderDual, OrderDual.ofDual.trans, ofDual, revPerm, rev_le_rev
-/
def revOrderIso : (Fin n)ᵒᵈ ≃o Fin n := ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩

@[simp]
/--
lemma `revOrderIso_symm_apply` / 引理 `revOrderIso_symm_apply`

English:
lemma revOrderIso_symm_apply
  given: (i : Fin n)
  statement: revOrderIso.symm i = OrderDual.toDual (rev i)
  proof: rfl

中文:
引理 revOrderIso_symm_apply
  条件: (i : 有限集 n)
  结论: revOrderIso.symm i = OrderDual.toDual (rev i)
  证明: rfl
-/
lemma revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) := rfl

/--
lemma `rev_strictAnti` / 引理 `rev_strictAnti`

English:
lemma rev_strictAnti
  statement: StrictAnti (@rev n)
  proof: fun _ _ => rev_lt_rev.mpr

中文:
引理 rev_strictAnti
  结论: 严格递减 (@rev n)
  证明: fun _ _ => rev_lt_rev.mpr

Depends on / 依赖: rev_lt_rev, rev_lt_rev.mpr
-/
lemma rev_strictAnti : StrictAnti (@rev n) := fun _ _ => rev_lt_rev.mpr

/--
lemma `rev_anti` / 引理 `rev_anti`

English:
lemma rev_anti
  statement: Antitone (@rev n)
  proof: rev_strictAnti.antitone

中文:
引理 rev_anti
  结论: 递减 (@rev n)
  证明: rev_strictAnti.antitone

Depends on / 依赖: antitone, rev_strictAnti, rev_strictAnti.antitone
-/
lemma rev_anti : Antitone (@rev n) := rev_strictAnti.antitone

/-! #### Order embeddings -/

/-- The inclusion map `Fin n → ℕ` is an order embedding. -/
@[simps! apply]
/--
Definition of `valOrderEmb` / `valOrderEmb` 的定义

English:
definition valOrderEmb
  signature: (n)
  body: ⟨valEmbedding, Iff.rfl⟩

中文:
定义 valOrderEmb
  签名: (n)
  定义体: ⟨valEmbedding, Iff.rfl⟩

Depends on / 依赖: Iff.rfl, valEmbedding
-/
def valOrderEmb (n) : Fin n ↪o Nat := ⟨valEmbedding, Iff.rfl⟩

namespace OrderEmbedding

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Fin n ↪o Nat)
  body: Fin.valOrderEmb n

中文:
实例 :
  签名: 可居 (有限集 n ↪o 自然数)
  定义体: Fin.valOrderEmb n

Depends on / 依赖: Fin.valOrderEmb, valOrderEmb
-/
instance : Inhabited (Fin n ↪o Nat) where
  default := Fin.valOrderEmb n

end OrderEmbedding

/--
Instance `Lt.isWellOrder` / 实例 `Lt.isWellOrder`

English:
instance Lt.isWellOrder
  signature: (n)
  body: (valOrderEmb n).isWellOrder

中文:
实例 Lt.isWellOrder
  签名: (n)
  定义体: (valOrderEmb n).isWellOrder

Depends on / 依赖: isWellOrder, valOrderEmb
-/
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) := (valOrderEmb n).isWellOrder

/--
Definition of `succOrderEmb` / `succOrderEmb` 的定义

English:
definition succOrderEmb
  signature: (n : Nat)
  body: .ofStrictMono succ strictMono_succ

中文:
定义 succOrderEmb
  签名: (n : 自然数)
  定义体: .ofStrictMono succ strictMono_succ

Depends on / 依赖: ofStrictMono, strictMono_succ
-/
def succOrderEmb (n : Nat) : Fin n ↪o Fin (n + 1) := .ofStrictMono succ strictMono_succ

/--
lemma `coe_succOrderEmb` / 引理 `coe_succOrderEmb`

English:
lemma coe_succOrderEmb
  statement: ⇑(succOrderEmb n) = Fin.succ
  proof: rfl

中文:
引理 coe_succOrderEmb
  结论: ⇑(succOrderEmb n) = 有限集.succ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_succOrderEmb : ⇑(succOrderEmb n) = Fin.succ := rfl

/--
lemma `succOrderEmb_toEmbedding` / 引理 `succOrderEmb_toEmbedding`

English:
lemma succOrderEmb_toEmbedding
  statement: (succOrderEmb n).toEmbedding = succEmb n
  proof: rfl

中文:
引理 succOrderEmb_toEmbedding
  结论: (succOrderEmb n).toEmbedding = succEmb n
  证明: rfl
-/
@[simp] lemma succOrderEmb_toEmbedding : (succOrderEmb n).toEmbedding = succEmb n := rfl

/-- `Fin.castLE` as an `OrderEmbedding`.

`castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps! apply toEmbedding]
/--
Definition of `castLEOrderEmb` / `castLEOrderEmb` 的定义

English:
definition castLEOrderEmb
  signature: (h : n <= m)
  body: .ofStrictMono (castLE h) (strictMono_castLE h)

中文:
定义 castLEOrderEmb
  签名: (h : n <= m)
  定义体: .ofStrictMono (castLE h) (strictMono_castLE h)

Depends on / 依赖: castLE, ofStrictMono, strictMono_castLE
-/
def castLEOrderEmb (h : n <= m) : Fin n ↪o Fin m := .ofStrictMono (castLE h) (strictMono_castLE h)

/-- `Fin.castAdd` as an `OrderEmbedding`.

`castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
/--
Definition of `castAddOrderEmb` / `castAddOrderEmb` 的定义

English:
definition castAddOrderEmb
  signature: (m)
  body: .ofStrictMono (castAdd m) (strictMono_castAdd m)

中文:
定义 castAddOrderEmb
  签名: (m)
  定义体: .ofStrictMono (castAdd m) (strictMono_castAdd m)

Depends on / 依赖: castAdd, ofStrictMono, strictMono_castAdd
-/
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (castAdd m) (strictMono_castAdd m)

/-- `Fin.castSucc` as an `OrderEmbedding`.

`castSuccOrderEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
/--
Definition of `castSuccOrderEmb` / `castSuccOrderEmb` 的定义

English:
definition castSuccOrderEmb
  signature: : Fin n ↪o Fin (n + 1)
  body: .ofStrictMono castSucc strictMono_castSucc

中文:
定义 castSuccOrderEmb
  签名: : 有限集 n ↪o 有限集 (n + 1)
  定义体: .ofStrictMono castSucc strictMono_castSucc

Depends on / 依赖: castSucc, ofStrictMono, strictMono_castSucc
-/
def castSuccOrderEmb : Fin n ↪o Fin (n + 1) := .ofStrictMono castSucc strictMono_castSucc

/-- `Fin.addNat` as an `OrderEmbedding`.

`addNatOrderEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply toEmbedding]
/--
Definition of `addNatOrderEmb` / `addNatOrderEmb` 的定义

English:
definition addNatOrderEmb
  signature: (m)
  body: .ofStrictMono (addNat · m) (strictMono_addNat m)

中文:
定义 add自然数OrderEmb
  签名: (m)
  定义体: .ofStrictMono (addNat · m) (strictMono_addNat m)

Depends on / 依赖: addNat, ofStrictMono, strictMono_addNat
-/
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (addNat · m) (strictMono_addNat m)

/-- `Fin.natAdd` as an `OrderEmbedding`.

`natAddOrderEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply toEmbedding]
/--
Definition of `natAddOrderEmb` / `natAddOrderEmb` 的定义

English:
definition natAddOrderEmb
  signature: (n)
  body: .ofStrictMono (natAdd n) (strictMono_natAdd n)

中文:
定义 natAddOrderEmb
  签名: (n)
  定义体: .ofStrictMono (natAdd n) (strictMono_natAdd n)

Depends on / 依赖: natAdd, ofStrictMono, strictMono_natAdd
-/
def natAddOrderEmb (n) : Fin m ↪o Fin (n + m) := .ofStrictMono (natAdd n) (strictMono_natAdd n)

/-- `Fin.succAbove p` as an `OrderEmbedding`. -/
@[simps! apply toEmbedding]
/--
Definition of `succAboveOrderEmb` / `succAboveOrderEmb` 的定义

English:
definition succAboveOrderEmb
  signature: (p : Fin (n + 1))
  body: OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)

@[simp]

中文:
定义 succAboveOrderEmb
  签名: (p : 有限集 (n + 1))
  定义体: OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, strictMono_succAbove, succAbove
-/
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)

@[simp]
/--
lemma `range_succAboveOrderEmb` / 引理 `range_succAboveOrderEmb`

English:
lemma range_succAboveOrderEmb
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  aesop

中文:
引理 range_succAboveOrderEmb
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: by
  aesop
-/
lemma range_succAboveOrderEmb {n : Nat} (i : Fin (n + 1)) :
    Set.range (Fin.succAboveOrderEmb i) = {i}ᶜ := by
  aesop

/-! ### Uniqueness of order isomorphisms -/

variable {α : Type*} [Preorder α]

/--
lemma `coe_orderIso_apply` / 引理 `coe_orderIso_apply`

English:
lemma coe_orderIso_apply
  given: (e : Fin n ≃o Fin m) (i : Fin n)
  statement: (e i : Nat) = i
  proof: by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction i using Nat.strong_induction_on with | _ i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_symm_apply.1 (mk_lt_of_lt_val hj)
    specialize h _ this (e.symm _).is_lt
    simp only [Fin.eta, OrderIso.apply_symm_apply] at h
    rwa [h]
  · rwa [← h j hj (hj.trans hi), ← lt_def, e.lt_iff_lt]

中文:
引理 coe_orderIso_apply
  条件: (e : 有限集 n ≃o 有限集 m) (i : 有限集 n)
  结论: (e i : 自然数) = i
  证明: by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction i using Nat.strong_induction_on with | _ i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_symm_apply.1 (mk_lt_of_lt_val hj)
    specialize h _ this (e.symm _).is_lt
    simp only [Fin.eta, OrderIso.apply_symm_apply] at h
    rwa [h]
  · rwa [← h j hj (hj.trans hi), ← lt_def, e.lt_iff_lt]
-/
@[simp] lemma coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : Nat) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction i using Nat.strong_induction_on with | _ i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_symm_apply.1 (mk_lt_of_lt_val hj)
    specialize h _ this (e.symm _).is_lt
    simp only [Fin.eta, OrderIso.apply_symm_apply] at h
    rwa [h]
  · rwa [← h j hj (hj.trans hi), ← lt_def, e.lt_iff_lt]

end Fin
