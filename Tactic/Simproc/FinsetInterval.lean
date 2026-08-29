/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Util.Qq

/-!
# Simproc for intervals of natural numbers
-/

public meta section

open Qq Lean Finset

namespace Mathlib.Tactic.Simp
namespace Nat
variable {m n : Nat} {s : Finset Nat}

/--
lemma `Icc_eq_empty_of_lt` / 引理 `Icc_eq_empty_of_lt`

English:
lemma Icc_eq_empty_of_lt
  given: (hnm : n.blt m)
  statement: Icc m n = ∅
  proof: by simpa using hnm

中文:
引理 Icc_eq_empty_of_lt
  条件: (hnm : n.blt m)
  结论: 闭区间 m n = ∅
  证明: by simpa using hnm
-/
private lemma Icc_eq_empty_of_lt (hnm : n.blt m) : Icc m n = ∅ := by simpa using hnm

/--
lemma `Icc_eq_insert_of_Icc_succ_eq` / 引理 `Icc_eq_insert_of_Icc_succ_eq`

English:
lemma Icc_eq_insert_of_Icc_succ_eq
  given: (hmn : m.ble n) (hs : Icc (m + 1) n = s)
  proof: by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

中文:
引理 Icc_eq_insert_of_Icc_succ_eq
  条件: (hmn : m.ble n) (hs : 闭区间 (m + 1) n = s)
  证明: by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]
-/
private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m.ble n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

/--
lemma `Ico_succ_eq_of_Icc_eq` / 引理 `Ico_succ_eq_of_Icc_eq`

English:
lemma Ico_succ_eq_of_Icc_eq
  given: (hs : Icc m n = s)
  statement: Ico m (n + 1) = s
  proof: by
  rw [← hs]; rw [Ico_add_one_right_eq_Icc]

中文:
引理 Ico_succ_eq_of_Icc_eq
  条件: (hs : 闭区间 m n = s)
  结论: 左闭右开区间 m (n + 1) = s
  证明: by
  rw [← hs]; rw [Ico_add_one_right_eq_Icc]
-/
private lemma Ico_succ_eq_of_Icc_eq (hs : Icc m n = s) : Ico m (n + 1) = s := by
  rw [← hs]; rw [Ico_add_one_right_eq_Icc]

/--
lemma `Ico_zero` / 引理 `Ico_zero`

English:
lemma Ico_zero
  given: (m : Nat)
  statement: Ico m 0 = ∅
  proof: by simp

中文:
引理 Ico_zero
  条件: (m : 自然数)
  结论: 左闭右开区间 m 0 = ∅
  证明: by simp
-/
private lemma Ico_zero (m : Nat) : Ico m 0 = ∅ := by simp

/--
lemma `Ioc_eq_of_Icc_succ_eq` / 引理 `Ioc_eq_of_Icc_succ_eq`

English:
lemma Ioc_eq_of_Icc_succ_eq
  given: (hs : Icc (m + 1) n = s)
  statement: Ioc m n = s
  proof: by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]

中文:
引理 Ioc_eq_of_Icc_succ_eq
  条件: (hs : 闭区间 (m + 1) n = s)
  结论: 左开右闭区间 m n = s
  证明: by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]
-/
private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]

/--
lemma `Ioo_eq_of_Icc_succ_pred_eq` / 引理 `Ioo_eq_of_Icc_succ_pred_eq`

English:
lemma Ioo_eq_of_Icc_succ_pred_eq
  given: (hs : Icc (m + 1) (n - 1) = s)
  statement: Ioo m n = s
  proof: by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]

中文:
引理 Ioo_eq_of_Icc_succ_pred_eq
  条件: (hs : 闭区间 (m + 1) (n - 1) = s)
  结论: 开区间 m n = s
  证明: by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]
-/
private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]

/--
lemma `Iic_eq_of_Icc_zero_eq` / 引理 `Iic_eq_of_Icc_zero_eq`

English:
lemma Iic_eq_of_Icc_zero_eq
  given: (hs : Icc 0 n = s)
  statement: Iic n = s
  proof: hs

中文:
引理 Iic_eq_of_Icc_zero_eq
  条件: (hs : 闭区间 0 n = s)
  结论: 左无界右闭区间 n = s
  证明: hs
-/
private lemma Iic_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iic n = s := hs

/--
lemma `Iio_succ_eq_of_Icc_zero_eq` / 引理 `Iio_succ_eq_of_Icc_zero_eq`

English:
lemma Iio_succ_eq_of_Icc_zero_eq
  given: (hs : Icc 0 n = s)
  statement: Iio (n + 1) = s
  proof: by
  rw [Iio_eq_Ico]; rw [Ico_add_one_right_eq_Icc]; rw [bot_eq_zero]; rw [hs]

中文:
引理 Iio_succ_eq_of_Icc_zero_eq
  条件: (hs : 闭区间 0 n = s)
  结论: 左无界右开区间 (n + 1) = s
  证明: by
  rw [Iio_eq_Ico]; rw [Ico_add_one_right_eq_Icc]; rw [bot_eq_zero]; rw [hs]
-/
private lemma Iio_succ_eq_of_Icc_zero_eq (hs : Icc 0 n = s) : Iio (n + 1) = s := by
  rw [Iio_eq_Ico]; rw [Ico_add_one_right_eq_Icc]; rw [bot_eq_zero]; rw [hs]

/--
lemma `Iio_zero` / 引理 `Iio_zero`

English:
lemma Iio_zero
  statement: Iio 0 = ∅
  proof: by simp

中文:
引理 Iio_zero
  结论: 左无界右开区间 0 = ∅
  证明: by simp
-/
private lemma Iio_zero : Iio 0 = ∅ := by simp

end Nat

namespace Int
variable {m n : Int} {s : Finset Int}

/--
lemma `Icc_eq_empty_of_lt` / 引理 `Icc_eq_empty_of_lt`

English:
lemma Icc_eq_empty_of_lt
  given: (hnm : n < m)
  statement: Icc m n = ∅
  proof: by simpa using hnm

中文:
引理 Icc_eq_empty_of_lt
  条件: (hnm : n < m)
  结论: 闭区间 m n = ∅
  证明: by simpa using hnm

Depends on / 依赖: F.germ, F.obj, ToType, g.base, g.germ, generateFrom
-/
private lemma Icc_eq_empty_of_lt (hnm : n < m) : Icc m n = ∅ := by simpa using hnm

/--
lemma `Icc_eq_insert_of_Icc_succ_eq` / 引理 `Icc_eq_insert_of_Icc_succ_eq`

English:
lemma Icc_eq_insert_of_Icc_succ_eq
  given: (hmn : m <= n) (hs : Icc (m + 1) n = s)
  proof: by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

中文:
引理 Icc_eq_insert_of_Icc_succ_eq
  条件: (hmn : m <= n) (hs : 闭区间 (m + 1) n = s)
  证明: by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]
-/
private lemma Icc_eq_insert_of_Icc_succ_eq (hmn : m <= n) (hs : Icc (m + 1) n = s) :
    Icc m n = insert m s := by rw [← hs, insert_Icc_add_one_left_eq_Icc (by simpa using hmn)]

/--
lemma `Ico_eq_of_Icc_pred_eq` / 引理 `Ico_eq_of_Icc_pred_eq`

English:
lemma Ico_eq_of_Icc_pred_eq
  given: (hs : Icc m (n - 1) = s)
  statement: Ico m n = s
  proof: by
  rw [← hs]; rw [Icc_sub_one_right_eq_Ico]

中文:
引理 Ico_eq_of_Icc_pred_eq
  条件: (hs : 闭区间 m (n - 1) = s)
  结论: 左闭右开区间 m n = s
  证明: by
  rw [← hs]; rw [Icc_sub_one_right_eq_Ico]
-/
private lemma Ico_eq_of_Icc_pred_eq (hs : Icc m (n - 1) = s) : Ico m n = s := by
  rw [← hs]; rw [Icc_sub_one_right_eq_Ico]

/--
lemma `Ioc_eq_of_Icc_succ_eq` / 引理 `Ioc_eq_of_Icc_succ_eq`

English:
lemma Ioc_eq_of_Icc_succ_eq
  given: (hs : Icc (m + 1) n = s)
  statement: Ioc m n = s
  proof: by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]

中文:
引理 Ioc_eq_of_Icc_succ_eq
  条件: (hs : 闭区间 (m + 1) n = s)
  结论: 左开右闭区间 m n = s
  证明: by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]
-/
private lemma Ioc_eq_of_Icc_succ_eq (hs : Icc (m + 1) n = s) : Ioc m n = s := by
  rw [← hs]; rw [Icc_add_one_left_eq_Ioc]

/--
lemma `Ioo_eq_of_Icc_succ_pred_eq` / 引理 `Ioo_eq_of_Icc_succ_pred_eq`

English:
lemma Ioo_eq_of_Icc_succ_pred_eq
  given: (hs : Icc (m + 1) (n - 1) = s)
  statement: Ioo m n = s
  proof: by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]

中文:
引理 Ioo_eq_of_Icc_succ_pred_eq
  条件: (hs : 闭区间 (m + 1) (n - 1) = s)
  结论: 开区间 m n = s
  证明: by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]
-/
private lemma Ioo_eq_of_Icc_succ_pred_eq (hs : Icc (m + 1) (n - 1) = s) : Ioo m n = s := by
  rw [← hs]; rw [← Icc_add_one_sub_one_eq_Ioo]

/--
lemma `Iio_zero` / 引理 `Iio_zero`

English:
lemma Iio_zero
  statement: Iio 0 = ∅
  proof: by simp

中文:
引理 Iio_zero
  结论: 左无界右开区间 0 = ∅
  证明: by simp
-/
private lemma Iio_zero : Iio 0 = ∅ := by simp

end Int

/--
Definition of `evalFinsetIccNat` / `evalFinsetIccNat` 的定义

English:
definition evalFinsetIccNat
  signature: (m n : Nat) (em en : Q(Nat))
  body: do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc (m + 1) n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(Nat) := mkNatLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Nat.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Nat.Icc_eq_empty_of_lt $hnm)⟩

中文:
定义 evalFinsetIcc自然数
  签名: (m n : 自然数) (em en : Q(自然数))
  定义体: do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc (m + 1) n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(Nat) := mkNatLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Nat.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Nat.Icc_eq_empty_of_lt $hnm)⟩
-/
def evalFinsetIccNat (m n : Nat) (em en : Q(Nat)) :
    MetaM ((s : Q(Finset Nat)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc (m + 1) n)`.
  else if m < n then
    let hmn : Q(Nat.ble $em $en = true) := (q(Eq.refl true) :)
    have em' : Q(Nat) := mkNatLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccNat (m + 1) n em' en
    return ⟨q(insert $em $s), q(Nat.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm : Q(Nat.blt $en $em = true) := (q(Eq.refl true) :)
    return ⟨q(∅), q(Nat.Icc_eq_empty_of_lt $hnm)⟩

/--
Definition of `evalFinsetIccInt` / `evalFinsetIccInt` 的定义

English:
definition evalFinsetIccInt
  signature: (m n : Int) (em en : Q(Int))
  body: do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn ← mkDecideProofQ q($em <= $en)
    have em' : Q(Int) := mkIntLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccInt (m + 1) n em' en
    return ⟨q(insert $em $s), q(Int.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm ← mkDecideProofQ q($en < $em)
    return ⟨q(∅), q(Icc_eq_empty_of_lt $hnm)⟩

中文:
定义 evalFinsetIcc整数
  签名: (m n : 整数) (em en : Q(整数))
  定义体: do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn ← mkDecideProofQ q($em <= $en)
    have em' : Q(Int) := mkIntLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccInt (m + 1) n em' en
    return ⟨q(insert $em $s), q(Int.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm ← mkDecideProofQ q($en < $em)
    return ⟨q(∅), q(Icc_eq_empty_of_lt $hnm)⟩
-/
partial def evalFinsetIccInt (m n : Int) (em en : Q(Int)) :
    MetaM ((s : Q(Finset Int)) × Q(.Icc $em $en = $s)) := do
  -- If `m = n`, then `Icc m n = {m}`. We handle this case separately because `insert m ∅` is
  -- not syntactically `{m}`.
  if m = n then
have : em =Q en := ⟨⟩
    return ⟨q({$em}), q(Icc_self _)⟩
  -- If `m < n`, then `Icc m n = insert m (Icc m n)`.
  else if m < n then
    let hmn ← mkDecideProofQ q($em <= $en)
    have em' : Q(Int) := mkIntLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨s, hs⟩ ← evalFinsetIccInt (m + 1) n em' en
    return ⟨q(insert $em $s), q(Int.Icc_eq_insert_of_Icc_succ_eq $hmn $hs)⟩
  -- Else `n < m` and `Icc m n = ∅`.
  else
    let hnm ← mkDecideProofQ q($en < $em)
    return ⟨q(∅), q(Icc_eq_empty_of_lt $hnm)⟩

end Mathlib.Tactic.Simp

open Mathlib.Tactic.Simp

/-!
Note that these simprocs are not made simp to avoid simp blowing up on goals containing things of
the form `Iic (2 ^ 1024)`.
-/
namespace Finset

/-- Simproc to compute `Finset.Icc a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Icc_ofNat_ofNat (Icc _ _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Icc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat m n em en
return .done .mk es .some p
  | 1, ~q(Finset Int), ~q(Icc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccInt m n em en
return .done .mk es .some p
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ico a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ico_ofNat_ofNat (Ico _ _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Ico $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
have : en =Q 0 := ⟨⟩
return .done .mk q(∅) .some q(Nat.Ico_zero $em)
    | n + 1 =>
      have en' := mkNatLitQ n
have : en =Q en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat m n em en'
      return .done { expr := es, proof? := q(Nat.Ico_succ_eq_of_Icc_eq $p) }
  | 1, ~q(Finset Int), ~q(Ico $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have en' := mkIntLitQ (n - 1)
have : en' =Q en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt m (n - 1) em en'
    return .done { expr := es, proof? := q(Int.Ico_eq_of_Icc_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioc a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioc_ofNat_ofNat (Ioc _ _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Ioc $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    have em' := mkNatLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) n em' en
return .done .mk es .some q(Nat.Ioc_eq_of_Icc_succ_eq $p)
  | 1, ~q(Finset Int), ~q(Ioc $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) n em' en
    return .done { expr := es, proof? := q(Int.Ioc_eq_of_Icc_succ_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Ioo a b` where `a` and `b` are numerals.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Ioo_ofNat_ofNat (Ioo _ _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Ioo $em $en) =>
    let some m := em.nat? | return .continue
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat (m + 1) (n - 1) q($em + 1) q($en - 1)
return .done .mk es .some q(Nat.Ioo_eq_of_Icc_succ_pred_eq $p)
  | 1, ~q(Finset Int), ~q(Ioo $em $en) =>
    let some m := em.int? | return .continue
    let some n := en.int? | return .continue
    have em' := mkIntLitQ (m + 1)
have : em' =Q em + 1 := ⟨⟩
    have en' := mkIntLitQ (n - 1)
have : en' =Q en - 1 := ⟨⟩
    let ⟨es, p⟩ ← evalFinsetIccInt (m + 1) (n - 1) em' en'
    return .done { expr := es, proof? := q(Int.Ioo_eq_of_Icc_succ_pred_eq $p) }
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iic b` where `b` is a numeral.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iic_ofNat (Iic _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Iic $en) =>
    let some n := en.nat? | return .continue
    let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) en
return .done .mk es .some q(Nat.Iic_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

/-- Simproc to compute `Finset.Iio b` where `b` is a numeral.

**Warnings**:
* With the standard depth recursion limit, this simproc can compute intervals of size 250 at most.
* Make sure to exclude `Finset.insert_eq_of_mem` from your simp call when using this simproc. This
  avoids a quadratic time performance hit. -/
simproc_decl Iio_ofNat (Iio _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Finset Nat), ~q(Iio $en) =>
    let some n := en.nat? | return .continue
    match n with
    | 0 =>
have : en =Q 0 := ⟨⟩
return .done .mk q(∅) .some q(Nat.Iio_zero)
    | n + 1 =>
      have en' := mkNatLitQ n
have : en =Q en' + 1 := ⟨⟩
      let ⟨es, p⟩ ← evalFinsetIccNat 0 n q(0) q($en')
return .done .mk es some q(Nat.Iio_succ_eq_of_Icc_zero_eq $p)
  | _, _, _ => return .continue

attribute [nolint unusedHavesSuffices]
  Iio_ofNat Ico_ofNat_ofNat Ioc_ofNat_ofNat Ioo_ofNat_ofNat

/-! ### `ℕ` -/

example : Icc 1 0 = ∅ := by simp only [Icc_ofNat_ofNat]
example : Icc 1 1 = {1} := by simp only [Icc_ofNat_ofNat]
example : Icc 1 2 = {1, 2} := by simp only [Icc_ofNat_ofNat]

example : Ico 1 1 = ∅ := by simp only [Ico_ofNat_ofNat]
example : Ico 1 2 = {1} := by simp only [Ico_ofNat_ofNat]
example : Ico 1 3 = {1, 2} := by simp only [Ico_ofNat_ofNat]

example : Ioc 1 1 = ∅ := by simp only [Ioc_ofNat_ofNat]
example : Ioc 1 2 = {2} := by simp only [Ioc_ofNat_ofNat]
example : Ioc 1 3 = {2, 3} := by simp only [Ioc_ofNat_ofNat]

example : Ioo 1 2 = ∅ := by simp only [Ioo_ofNat_ofNat]
example : Ioo 1 3 = {2} := by simp only [Ioo_ofNat_ofNat]
example : Ioo 1 4 = {2, 3} := by simp only [Ioo_ofNat_ofNat]

example : Iic 0 = {0} := by simp only [Iic_ofNat]
example : Iic 1 = {0, 1} := by simp only [Iic_ofNat]
example : Iic 2 = {0, 1, 2} := by simp only [Iic_ofNat]

example : Iio 0 = ∅ := by simp only [Iio_ofNat]
example : Iio 1 = {0} := by simp only [Iio_ofNat]
example : Iio 2 = {0, 1} := by simp only [Iio_ofNat]

/-! ### `ℤ` -/

example : Icc (1 : Int) 0 = ∅ := by simp only [Icc_ofNat_ofNat]
example : Icc (1 : Int) 1 = {1} := by simp only [Icc_ofNat_ofNat]
example : Icc (1 : Int) 2 = {1, 2} := by simp only [Icc_ofNat_ofNat]

example : Ico (1 : Int) 1 = ∅ := by simp only [Ico_ofNat_ofNat]
example : Ico (1 : Int) 2 = {1} := by simp only [Ico_ofNat_ofNat]
example : Ico (1 : Int) 3 = {1, 2} := by simp only [Ico_ofNat_ofNat]

example : Ioc (1 : Int) 1 = ∅ := by simp only [Ioc_ofNat_ofNat]
example : Ioc (1 : Int) 2 = {2} := by simp only [Ioc_ofNat_ofNat]
example : Ioc (1 : Int) 3 = {2, 3} := by simp only [Ioc_ofNat_ofNat]

example : Ioo (1 : Int) 2 = ∅ := by simp only [Ioo_ofNat_ofNat]
example : Ioo (1 : Int) 3 = {2} := by simp only [Ioo_ofNat_ofNat]
example : Ioo (1 : Int) 4 = {2, 3} := by simp only [Ioo_ofNat_ofNat]

end Finset
