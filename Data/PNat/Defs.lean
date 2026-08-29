/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.PNat.Notation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe
public import Mathlib.Tactic.Lift

/-!
# The positive natural numbers

This file contains the definitions, and basic results.
Most algebraic facts are deferred to `Data.PNat.Basic`, as they need more imports.
-/

@[expose] public section

deriving instance LinearOrder for PNat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Nat+
  body: ⟨⟨1, Nat.zero_lt_one⟩⟩

中文:
实例 :
  签名: 幺 自然数+
  定义体: ⟨⟨1, Nat.zero_lt_one⟩⟩

Depends on / 依赖: Nat.zero_lt_one, zero_lt_one
-/
instance : One Nat+ :=
  ⟨⟨1, Nat.zero_lt_one⟩⟩

instance (n : Nat) [NeZero n] : OfNat Nat+ n :=
⟨⟨n, Nat.pos_of_ne_zero NeZero.ne n⟩⟩

namespace PNat

-- Note: similar to Subtype.coe_mk
@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (n h)
  statement: (PNat.val (⟨n, h⟩ : Nat+) : Nat) = n
  proof: rfl

中文:
定理 mk_coe
  条件: (n h)
  结论: (正自然数.val (⟨n, h⟩ : 自然数+) : 自然数) = n
  证明: rfl
-/
theorem mk_coe (n h) : (PNat.val (⟨n, h⟩ : Nat+) : Nat) = n :=
  rfl

/--
Definition of `natPred` / `natPred` 的定义

English:
definition natPred
  signature: (i : Nat+)
  body: i - 1

@[simp]

中文:
定义 natPred
  签名: (i : 自然数+)
  定义体: i - 1

@[simp]
-/
def natPred (i : Nat+) : Nat :=
  i - 1

@[simp]
/--
theorem `natPred_eq_pred` / 定理 `natPred_eq_pred`

English:
theorem natPred_eq_pred
  given: {n : Nat} (h : 0 < n)
  statement: natPred (⟨n, h⟩ : Nat+) = n.pred
  proof: rfl

中文:
定理 natPred_eq_pred
  条件: {n : 自然数} (h : 0 < n)
  结论: natPred (⟨n, h⟩ : 自然数+) = n.pred
  证明: rfl
-/
theorem natPred_eq_pred {n : Nat} (h : 0 < n) : natPred (⟨n, h⟩ : Nat+) = n.pred :=
  rfl

end PNat

namespace Nat

/--
Definition of `toPNat` / `toPNat` 的定义

English:
definition toPNat
  signature: (n : Nat) (h : 0 < n := by decide)
  body: ⟨n, h⟩

中文:
定义 toP自然数
  签名: (n : 自然数) (h : 0 < n := by decide)
  定义体: ⟨n, h⟩
-/
def toPNat (n : Nat) (h : 0 < n := by decide) : Nat+ :=
  ⟨n, h⟩

/--
Definition of `succPNat` / `succPNat` 的定义

English:
definition succPNat
  signature: (n : Nat)
  body: ⟨succ n, succ_pos n⟩

@[simp]

中文:
定义 succP自然数
  签名: (n : 自然数)
  定义体: ⟨succ n, succ_pos n⟩

@[simp]

Depends on / 依赖: succ_pos
-/
def succPNat (n : Nat) : Nat+ :=
  ⟨succ n, succ_pos n⟩

@[simp]
/--
theorem `succPNat_coe` / 定理 `succPNat_coe`

English:
theorem succPNat_coe
  given: (n : Nat)
  statement: (succPNat n : Nat) = succ n
  proof: rfl

@[simp]

中文:
定理 succP自然数_coe
  条件: (n : 自然数)
  结论: (succP自然数 n : 自然数) = succ n
  证明: rfl

@[simp]
-/
theorem succPNat_coe (n : Nat) : (succPNat n : Nat) = succ n :=
  rfl

@[simp]
/--
theorem `natPred_succPNat` / 定理 `natPred_succPNat`

English:
theorem natPred_succPNat
  given: (n : Nat)
  statement: n.succPNat.natPred = n
  proof: rfl

@[simp]

中文:
定理 natPred_succP自然数
  条件: (n : 自然数)
  结论: n.succP自然数.natPred = n
  证明: rfl

@[simp]
-/
theorem natPred_succPNat (n : Nat) : n.succPNat.natPred = n :=
  rfl

@[simp]
/--
theorem `_root_.PNat.succPNat_natPred` / 定理 `_root_.PNat.succPNat_natPred`

English:
theorem _root_.PNat.succPNat_natPred
  given: (n : Nat+)
  statement: n.natPred.succPNat = n
  proof: Subtype.ext succ_pred_eq_of_pos n.2

中文:
定理 _root_.正自然数.succP自然数_natPred
  条件: (n : 自然数+)
  结论: n.natPred.succP自然数 = n
  证明: Subtype.ext succ_pred_eq_of_pos n.2

Depends on / 依赖: Subtype, Subtype.ext, succ_pred_eq_of_pos
-/
theorem _root_.PNat.succPNat_natPred (n : Nat+) : n.natPred.succPNat = n :=
Subtype.ext succ_pred_eq_of_pos n.2

/--
Definition of `toPNat'` / `toPNat'` 的定义

English:
definition toPNat'
  signature: (n : Nat)
  body: succPNat (pred n)

@[simp]

中文:
定义 toP自然数'
  签名: (n : 自然数)
  定义体: succPNat (pred n)

@[simp]

Depends on / 依赖: succPNat
-/
def toPNat' (n : Nat) : Nat+ :=
  succPNat (pred n)

@[simp]
/--
theorem `toPNat'_zero` / 定理 `toPNat'_zero`

English:
theorem toPNat'_zero
  statement: Nat.toPNat' 0 = 1
  proof: rfl

@[simp]

中文:
定理 toP自然数'_zero
  结论: 自然数.toP自然数' 0 = 1
  证明: rfl

@[simp]
-/
theorem toPNat'_zero : Nat.toPNat' 0 = 1 := rfl

@[simp]
/--
theorem `toPNat'_coe` / 定理 `toPNat'_coe`

English:
theorem toPNat'_coe
  statement: forall n : Nat, (toPNat' n : Nat) = ite (0 < n) n 1

中文:
定理 toP自然数'_coe
  结论: 对任意 n : 自然数, (toP自然数' n : 自然数) = ite (0 < n) n 1
-/
theorem toPNat'_coe : forall n : Nat, (toPNat' n : Nat) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace PNat

open Nat

/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: (n k : Nat) (hn : 0 < n) (hk : 0 < k)
  statement: (⟨n, hn⟩ : Nat+) <= ⟨k, hk⟩ ↔ n <= k
  proof: by simp

中文:
定理 mk_le_mk
  条件: (n k : 自然数) (hn : 0 < n) (hk : 0 < k)
  结论: (⟨n, hn⟩ : 自然数+) <= ⟨k, hk⟩ ↔ n <= k
  证明: by simp
-/
theorem mk_le_mk (n k : Nat) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : Nat+) <= ⟨k, hk⟩ ↔ n <= k := by simp

/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: (n k : Nat) (hn : 0 < n) (hk : 0 < k)
  statement: (⟨n, hn⟩ : Nat+) < ⟨k, hk⟩ ↔ n < k
  proof: by simp

@[simp, norm_cast]

中文:
定理 mk_lt_mk
  条件: (n k : 自然数) (hn : 0 < n) (hk : 0 < k)
  结论: (⟨n, hn⟩ : 自然数+) < ⟨k, hk⟩ ↔ n < k
  证明: by simp

@[simp, norm_cast]
-/
theorem mk_lt_mk (n k : Nat) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : Nat+) < ⟨k, hk⟩ ↔ n < k := by simp

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: (n k : Nat+)
  statement: (n : Nat) <= k ↔ n <= k
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_le_coe
  条件: (n k : 自然数+)
  结论: (n : 自然数) <= k ↔ n <= k
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe (n k : Nat+) : (n : Nat) <= k ↔ n <= k :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  given: (n k : Nat+)
  statement: (n : Nat) < k ↔ n < k
  proof: Iff.rfl

@[simp]

中文:
定理 coe_lt_coe
  条件: (n k : 自然数+)
  结论: (n : 自然数) < k ↔ n < k
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe (n k : Nat+) : (n : Nat) < k ↔ n < k :=
  Iff.rfl

@[simp]
/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  given: (n : Nat+)
  statement: 0 < (n : Nat)
  proof: n.2

中文:
定理 pos
  条件: (n : 自然数+)
  结论: 0 < (n : 自然数)
  证明: n.2
-/
theorem pos (n : Nat+) : 0 < (n : Nat) :=
  n.2

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {m n : Nat+}
  statement: (m : Nat) = n -> m = n
  proof: Subtype.ext

中文:
定理 eq
  条件: {m n : 自然数+}
  结论: (m : 自然数) = n -> m = n
  证明: Subtype.ext

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem eq {m n : Nat+} : (m : Nat) = n -> m = n :=
  Subtype.ext

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective PNat.val
  proof: Subtype.coe_injective

@[simp]

中文:
定理 coe_injective
  结论: 函数.单射 正自然数.val
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective PNat.val :=
  Subtype.coe_injective

@[simp]
/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (n : Nat+)
  statement: (n : Nat) != 0
  proof: n.2.ne'

中文:
定理 ne_zero
  条件: (n : 自然数+)
  结论: (n : 自然数) != 0
  证明: n.2.ne'

Depends on / 依赖: isConvexSet_coe, subtype
-/
theorem ne_zero (n : Nat+) : (n : Nat) != 0 :=
  n.2.ne'

/--
Instance `_root_.NeZero.pnat` / 实例 `_root_.NeZero.pnat`

English:
instance _root_.NeZero.pnat
  signature: {a : Nat+}
  body: ⟨a.ne_zero⟩

中文:
实例 _root_.NeZero.pnat
  签名: {a : 自然数+}
  定义体: ⟨a.ne_zero⟩

Depends on / 依赖: a.ne_zero, ne_zero
-/
instance _root_.NeZero.pnat {a : Nat+} : NeZero (a : Nat) :=
  ⟨a.ne_zero⟩

/--
theorem `toPNat'_coe` / 定理 `toPNat'_coe`

English:
theorem toPNat'_coe
  given: {n : Nat}
  statement: 0 < n -> (n.toPNat' : Nat) = n
  proof: succ_pred_eq_of_pos

@[simp]

中文:
定理 toP自然数'_coe
  条件: {n : 自然数}
  结论: 0 < n -> (n.toP自然数' : 自然数) = n
  证明: succ_pred_eq_of_pos

@[simp]

Depends on / 依赖: succ_pred_eq_of_pos
-/
theorem toPNat'_coe {n : Nat} : 0 < n -> (n.toPNat' : Nat) = n :=
  succ_pred_eq_of_pos

@[simp]
/--
theorem `coe_toPNat'` / 定理 `coe_toPNat'`

English:
theorem coe_toPNat'
  given: (n : Nat+)
  statement: (n : Nat).toPNat' = n
  proof: eq (toPNat'_coe n.pos)

@[deprecated "use `one_le`" (since := "2026-05-07")]

中文:
定理 coe_toP自然数'
  条件: (n : 自然数+)
  结论: (n : 自然数).toP自然数' = n
  证明: eq (toPNat'_coe n.pos)

@[deprecated "use `one_le`" (since := "2026-05-07")]

Depends on / 依赖: _coe, n.pos, toPNat
-/
theorem coe_toPNat' (n : Nat+) : (n : Nat).toPNat' = n :=
  eq (toPNat'_coe n.pos)

@[deprecated "use `one_le`" (since := "2026-05-07")]
/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: (n : Nat+)
  statement: (1 : Nat+) <= n
  proof: n.2

@[deprecated "use `not_lt_one`" (since := "2026-05-07")]

中文:
定理 one_le
  条件: (n : 自然数+)
  结论: (1 : 自然数+) <= n
  证明: n.2

@[deprecated "use `not_lt_one`" (since := "2026-05-07")]

Depends on / 依赖: Finsupp, Finsupp.sum
-/
protected theorem one_le (n : Nat+) : (1 : Nat+) <= n :=
  n.2

@[deprecated "use `not_lt_one`" (since := "2026-05-07")]
/--
theorem `not_lt_one` / 定理 `not_lt_one`

English:
theorem not_lt_one
  given: (n : Nat+)
  statement: ¬n < 1
  proof: not_lt_of_ge n.2

中文:
定理 not_lt_one
  条件: (n : 自然数+)
  结论: ¬n < 1
  证明: not_lt_of_ge n.2
-/
protected theorem not_lt_one (n : Nat+) : ¬n < 1 :=
  not_lt_of_ge n.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Nat+
  body: ⟨1⟩

中文:
实例 :
  签名: 可居 自然数+
  定义体: ⟨1⟩

Depends on / 依赖: Finsupp, Finsupp.sum
-/
instance : Inhabited Nat+ :=
  ⟨1⟩

-- Some lemmas that rewrite `PNat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
/--
theorem `mk_one` / 定理 `mk_one`

English:
theorem mk_one
  given: {h}
  statement: (⟨1, h⟩ : Nat+) = (1 : Nat+)
  proof: rfl

@[norm_cast]

中文:
定理 mk_one
  条件: {h}
  结论: (⟨1, h⟩ : 自然数+) = (1 : 自然数+)
  证明: rfl

@[norm_cast]

Depends on / 依赖: Finsupp, Finsupp.sum
-/
theorem mk_one {h} : (⟨1, h⟩ : Nat+) = (1 : Nat+) :=
  rfl

@[norm_cast]
/--
theorem `one_coe` / 定理 `one_coe`

English:
theorem one_coe
  statement: ((1 : Nat+) : Nat) = 1
  proof: rfl

@[simp, norm_cast]

中文:
定理 one_coe
  结论: ((1 : 自然数+) : 自然数) = 1
  证明: rfl

@[simp, norm_cast]
-/
theorem one_coe : ((1 : Nat+) : Nat) = 1 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_one_iff` / 定理 `coe_eq_one_iff`

English:
theorem coe_eq_one_iff
  given: {m : Nat+}
  statement: (m : Nat) = 1 ↔ m = 1
  proof: Subtype.coe_injective.eq_iff' one_coe

中文:
定理 coe_eq_one_iff
  条件: {m : 自然数+}
  结论: (m : 自然数) = 1 ↔ m = 1
  证明: Subtype.coe_injective.eq_iff' one_coe

Depends on / 依赖: Subtype, Subtype.coe_injective.eq_iff, coe_injective, eq_iff, one_coe
-/
theorem coe_eq_one_iff {m : Nat+} : (m : Nat) = 1 ↔ m = 1 :=
  Subtype.coe_injective.eq_iff' one_coe

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation Nat+
  body: measure (fun (a : Nat+) => (a : Nat))

中文:
实例 :
  签名: 良基关系 自然数+
  定义体: measure (fun (a : Nat+) => (a : Nat))

Depends on / 依赖: measure
-/
instance : WellFoundedRelation Nat+ :=
  measure (fun (a : Nat+) => (a : Nat))

/--
Definition of `strongInductionOn` / `strongInductionOn` 的定义

English:
definition strongInductionOn
  signature: {p : Nat+ -> Sort*} (n : Nat+)

中文:
定义 strongInductionOn
  签名: {p : 自然数+ -> 类型层*} (n : 自然数+)
-/
def strongInductionOn {p : Nat+ -> Sort*} (n : Nat+) : (forall k, (forall m, m < k -> p m) -> p k) -> p n
  | IH => IH _ fun a _ => strongInductionOn a IH
termination_by n.1

/--
Definition of `modDivAux` / `modDivAux` 的定义

English:
definition modDivAux
  signature: : Nat+ -> Nat -> Nat -> Nat+ × Nat

中文:
定义 modDivAux
  签名: : 自然数+ -> 自然数 -> 自然数 -> 自然数+ × 自然数
-/
def modDivAux : Nat+ -> Nat -> Nat -> Nat+ × Nat
  | k, 0, q => ⟨k, q.pred⟩
  | _, r + 1, q => ⟨⟨r + 1, Nat.succ_pos r⟩, q⟩

/--
Definition of `modDiv` / `modDiv` 的定义

English:
definition modDiv
  signature: (m k : Nat+)
  body: modDivAux k ((m : Nat) % (k : Nat)) ((m : Nat) / (k : Nat))

中文:
定义 modDiv
  签名: (m k : 自然数+)
  定义体: modDivAux k ((m : Nat) % (k : Nat)) ((m : Nat) / (k : Nat))

Depends on / 依赖: modDivAux
-/
def modDiv (m k : Nat+) : Nat+ × Nat :=
  modDivAux k ((m : Nat) % (k : Nat)) ((m : Nat) / (k : Nat))

/--
Definition of `mod` / `mod` 的定义

English:
definition mod
  signature: (m k : Nat+)
  body: (modDiv m k).1

中文:
定义 mod
  签名: (m k : 自然数+)
  定义体: (modDiv m k).1

Depends on / 依赖: modDiv
-/
def mod (m k : Nat+) : Nat+ :=
  (modDiv m k).1

/--
Definition of `div` / `div` 的定义

English:
definition div
  signature: (m k : Nat+)
  body: (modDiv m k).2

中文:
定义 div
  签名: (m k : 自然数+)
  定义体: (modDiv m k).2

Depends on / 依赖: modDiv
-/
def div (m k : Nat+) : Nat :=
  (modDiv m k).2

/--
theorem `mod_coe` / 定理 `mod_coe`

English:
theorem mod_coe
  given: (m k : Nat+)
  proof: by
  dsimp [mod, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

中文:
定理 mod_coe
  条件: (m k : 自然数+)
  证明: by
  dsimp [mod, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

Depends on / 依赖: if_neg, if_pos, modDiv, n.succ_ne_zero, succ_ne_zero
-/
theorem mod_coe (m k : Nat+) :
    (mod m k : Nat) = ite ((m : Nat) % (k : Nat) = 0) (k : Nat) ((m : Nat) % (k : Nat)) := by
  dsimp [mod, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

/--
theorem `div_coe` / 定理 `div_coe`

English:
theorem div_coe
  given: (m k : Nat+)
  proof: by
  dsimp [div, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

中文:
定理 div_coe
  条件: (m k : 自然数+)
  证明: by
  dsimp [div, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

Depends on / 依赖: if_neg, if_pos, modDiv, n.succ_ne_zero, succ_ne_zero
-/
theorem div_coe (m k : Nat+) :
    (div m k : Nat) = ite ((m : Nat) % (k : Nat) = 0) ((m : Nat) / (k : Nat)).pred ((m : Nat) / (k : Nat)) := by
  dsimp [div, modDiv]
  cases (m : Nat) % (k : Nat) with
  | zero =>
    rw [if_pos rfl]
    rfl
  | succ n =>
    rw [if_neg n.succ_ne_zero]
    rfl

/--
Definition of `divExact` / `divExact` 的定义

English:
definition divExact
  signature: (m k : Nat+)
  body: ⟨(div m k).succ, Nat.succ_pos _⟩

中文:
定义 divExact
  签名: (m k : 自然数+)
  定义体: ⟨(div m k).succ, Nat.succ_pos _⟩

Depends on / 依赖: Nat.succ_pos, succ_pos
-/
def divExact (m k : Nat+) : Nat+ :=
  ⟨(div m k).succ, Nat.succ_pos _⟩

end PNat

section CanLift

/--
Instance `Nat.canLiftPNat` / 实例 `Nat.canLiftPNat`

English:
instance Nat.canLiftPNat
  signature: : CanLift Nat Nat+ (↑) (fun n => 0 < n)
  body: ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩

中文:
实例 自然数.canLiftP自然数
  签名: : CanLift 自然数 自然数+ (↑) (fun n => 0 < n)
  定义体: ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩

Depends on / 依赖: Nat.toPNat, PNat.toPNat, _coe, toPNat
-/
instance Nat.canLiftPNat : CanLift Nat Nat+ (↑) (fun n => 0 < n) :=
  ⟨fun n hn => ⟨Nat.toPNat' n, PNat.toPNat'_coe hn⟩⟩

/--
Instance `Int.canLiftPNat` / 实例 `Int.canLiftPNat`

English:
instance Int.canLiftPNat
  signature: : CanLift Int Nat+ (↑) ((0 < ·))
  body: ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe]; rw [if_pos (Int.natAbs_pos.2 hn.ne')]; rw [Int.natAbs_of_nonneg hn.le]⟩⟩

中文:
实例 整数.canLiftP自然数
  签名: : CanLift 整数 自然数+ (↑) ((0 < ·))
  定义体: ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe]; rw [if_pos (Int.natAbs_pos.2 hn.ne')]; rw [Int.natAbs_of_nonneg hn.le]⟩⟩

Depends on / 依赖: Int.natAbs, Int.natAbs_of_nonneg, Int.natAbs_pos, Nat.toPNat, _coe, hn.le, hn.ne, if_pos, natAbs, natAbs_of_nonneg, natAbs_pos, toPNat
-/
instance Int.canLiftPNat : CanLift Int Nat+ (↑) ((0 < ·)) :=
  ⟨fun n hn =>
    ⟨Nat.toPNat' (Int.natAbs n), by
      rw [Nat.toPNat'_coe]; rw [if_pos (Int.natAbs_pos.2 hn.ne')]; rw [Int.natAbs_of_nonneg hn.le]⟩⟩

end CanLift
