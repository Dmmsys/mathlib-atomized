/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# Successors and predecessor operations of `Fin n`

This file contains a number of definitions and lemmas
related to `Fin.succ`, `Fin.pred`, and related operations on `Fin n`.

## Main definitions

* `finCongr` : `Fin.cast` as an `Equiv`, equivalence between `Fin n` and `Fin m` when `n = m`;
* `Fin.succAbove` : embeds `Fin n` into `Fin (n + 1)` skipping `p`.
* `Fin.predAbove` : the (partial) inverse of `Fin.succAbove`.

-/

@[expose] public section

assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

namespace Fin

variable {n m : Nat}

section Succ


/--
lemma `succ_injective` / 引理 `succ_injective`

English:
lemma succ_injective
  given: (n : Nat)
  statement: Injective (@Fin.succ n)
  proof: fun a b => by simp [Fin.ext_iff]

@[simp]

中文:
引理 succ_injective
  条件: (n : 自然数)
  结论: 单射 (@有限集.succ n)
  证明: fun a b => by simp [Fin.ext_iff]

@[simp]

Depends on / 依赖: Fin.ext_iff, ext_iff
-/
lemma succ_injective (n : Nat) : Injective (@Fin.succ n) := fun a b => by simp [Fin.ext_iff]

@[simp]
/--
theorem `exists_succ_eq` / 定理 `exists_succ_eq`

English:
theorem exists_succ_eq
  given: {x : Fin (n + 1)}
  statement: (exists y, Fin.succ y = x) ↔ x != 0
  proof: ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩

中文:
定理 存在_succ_eq
  条件: {x : 有限集 (n + 1)}
  结论: (存在 y, 有限集.succ y = x) ↔ x != 0
  证明: ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩

Depends on / 依赖: h.irrefl.elim, irrefl, succ_ne_zero, x.cases
-/
theorem exists_succ_eq {x : Fin (n + 1)} : (exists y, Fin.succ y = x) ↔ x != 0 :=
  ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩

/--
theorem `exists_succ_eq_of_ne_zero` / 定理 `exists_succ_eq_of_ne_zero`

English:
theorem exists_succ_eq_of_ne_zero
  given: {x : Fin (n + 1)} (h : x != 0)
  proof: exists_succ_eq.mpr h

@[simp]

中文:
定理 存在_succ_eq_of_ne_zero
  条件: {x : 有限集 (n + 1)} (h : x != 0)
  证明: exists_succ_eq.mpr h

@[simp]

Depends on / 依赖: exists_succ_eq, exists_succ_eq.mpr
-/
theorem exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x != 0) :
    exists y, Fin.succ y = x := exists_succ_eq.mpr h

@[simp]
/--
theorem `succ_zero_eq_one'` / 定理 `succ_zero_eq_one'`

English:
theorem succ_zero_eq_one'
  given: [NeZero n]
  statement: Fin.succ (0 : Fin n) = 1
  proof: by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

中文:
定理 succ_zero_eq_one'
  条件: [NeZero n]
  结论: 有限集.succ (0 : 有限集 n) = 1
  证明: by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

/--
theorem `one_pos'` / 定理 `one_pos'`

English:
theorem one_pos'
  given: [NeZero n]
  statement: (0 : Fin (n + 1)) < 1
  proof: succ_zero_eq_one' (n := n) ▸ succ_pos _

中文:
定理 one_pos'
  条件: [NeZero n]
  结论: (0 : 有限集 (n + 1)) < 1
  证明: succ_zero_eq_one' (n := n) ▸ succ_pos _

Depends on / 依赖: succ_pos, succ_zero_eq_one
-/
theorem one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1 := succ_zero_eq_one' (n := n) ▸ succ_pos _
/--
theorem `zero_ne_one'` / 定理 `zero_ne_one'`

English:
theorem zero_ne_one'
  given: [NeZero n]
  statement: (0 : Fin (n + 1)) != 1
  proof: Fin.ne_of_lt one_pos'

中文:
定理 zero_ne_one'
  条件: [NeZero n]
  结论: (0 : 有限集 (n + 1)) != 1
  证明: Fin.ne_of_lt one_pos'

Depends on / 依赖: Fin.ne_of_lt, ne_of_lt, one_pos
-/
theorem zero_ne_one' [NeZero n] : (0 : Fin (n + 1)) != 1 := Fin.ne_of_lt one_pos'

/--
The `Fin.succ_one_eq_two` in `Lean` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/--
theorem `succ_one_eq_two'` / 定理 `succ_one_eq_two'`

English:
theorem succ_one_eq_two'
  given: [NeZero n]
  statement: Fin.succ (1 : Fin (n + 1)) = 2
  proof: by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

中文:
定理 succ_one_eq_two'
  条件: [NeZero n]
  结论: 有限集.succ (1 : 有限集 (n + 1)) = 2
  证明: by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

-- Version of `succ_one_eq_two` to be used by `dsimp`.
-- Note the `'` swapped around due to a move to std4.

/--
The `Fin.le_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[deprecated "use `nonpos_iff_eq_zero`" (since := "2026-05-11")]
/--
theorem `le_zero_iff'` / 定理 `le_zero_iff'`

English:
theorem le_zero_iff'
  given: {n : Nat} [NeZero n] {k : Fin n}
  statement: k <= 0 ↔ k = 0
  proof: ⟨fun h => Fin.ext by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩

中文:
定理 le_zero_iff'
  条件: {n : 自然数} [NeZero n] {k : 有限集 n}
  结论: k <= 0 ↔ k = 0
  证明: ⟨fun h => Fin.ext by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩

Depends on / 依赖: Fin.ext, Nat.eq_zero_of_le_zero, Nat.le_refl, eq_zero_of_le_zero, le_refl
-/
theorem le_zero_iff' {n : Nat} [NeZero n] {k : Fin n} : k <= 0 ↔ k = 0 :=
⟨fun h => Fin.ext by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩

-- TODO: Move to Batteries
/--
lemma `castLE_inj` / 引理 `castLE_inj`

English:
lemma castLE_inj
  given: {hmn : m <= n} {a b : Fin m}
  statement: castLE hmn a = castLE hmn b ↔ a = b
  proof: by
  simp [Fin.ext_iff]

中文:
引理 castLE_inj
  条件: {hmn : m <= n} {a b : 有限集 m}
  结论: castLE hmn a = castLE hmn b ↔ a = b
  证明: by
  simp [Fin.ext_iff]
-/
@[simp] lemma castLE_inj {hmn : m <= n} {a b : Fin m} : castLE hmn a = castLE hmn b ↔ a = b := by
  simp [Fin.ext_iff]

/--
lemma `castAdd_inj` / 引理 `castAdd_inj`

English:
lemma castAdd_inj
  given: {a b : Fin m}
  statement: castAdd n a = castAdd n b ↔ a = b
  proof: by simp [Fin.ext_iff]

中文:
引理 castAdd_inj
  条件: {a b : 有限集 m}
  结论: castAdd n a = castAdd n b ↔ a = b
  证明: by simp [Fin.ext_iff]
-/
@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [Fin.ext_iff]

attribute [simp] castSucc_inj

/--
lemma `castLE_injective` / 引理 `castLE_injective`

English:
lemma castLE_injective
  given: (hmn : m <= n)
  statement: Injective (castLE hmn)
  proof: fun _ _ hab => Fin.ext (congr_arg val hab :)

中文:
引理 castLE_injective
  条件: (hmn : m <= n)
  结论: 单射 (castLE hmn)
  证明: fun _ _ hab => Fin.ext (congr_arg val hab :)

Depends on / 依赖: Fin.ext, congr_arg
-/
lemma castLE_injective (hmn : m <= n) : Injective (castLE hmn) :=
  fun _ _ hab => Fin.ext (congr_arg val hab :)

/--
lemma `castAdd_injective` / 引理 `castAdd_injective`

English:
lemma castAdd_injective
  given: (m n : Nat)
  statement: Injective (@Fin.castAdd m n)
  proof: castLE_injective _

中文:
引理 castAdd_injective
  条件: (m n : 自然数)
  结论: 单射 (@有限集.castAdd m n)
  证明: castLE_injective _

Depends on / 依赖: castLE_injective
-/
lemma castAdd_injective (m n : Nat) : Injective (@Fin.castAdd m n) := castLE_injective _

/--
lemma `castSucc_injective` / 引理 `castSucc_injective`

English:
lemma castSucc_injective
  given: (n : Nat)
  statement: Injective (@Fin.castSucc n)
  proof: castAdd_injective _ _

中文:
引理 castSucc_injective
  条件: (n : 自然数)
  结论: 单射 (@有限集.castSucc n)
  证明: castAdd_injective _ _

Depends on / 依赖: castAdd_injective
-/
lemma castSucc_injective (n : Nat) : Injective (@Fin.castSucc n) := castAdd_injective _ _

/--
lemma `castLE_castSucc` / 引理 `castLE_castSucc`

English:
lemma castLE_castSucc
  given: {n m} (i : Fin n) (h : n + 1 <= m)
  proof: rfl

中文:
引理 castLE_castSucc
  条件: {n m} (i : 有限集 n) (h : n + 1 <= m)
  证明: rfl
-/
@[simp] lemma castLE_castSucc {n m} (i : Fin n) (h : n + 1 <= m) :
    i.castSucc.castLE h = i.castLE (Nat.le_of_succ_le h) :=
  rfl

/--
lemma `castLE_comp_castSucc` / 引理 `castLE_comp_castSucc`

English:
lemma castLE_comp_castSucc
  given: {n m} (h : n + 1 <= m)
  proof: rfl

中文:
引理 castLE_comp_castSucc
  条件: {n m} (h : n + 1 <= m)
  证明: rfl
-/
@[simp] lemma castLE_comp_castSucc {n m} (h : n + 1 <= m) :
    Fin.castLE h ∘ Fin.castSucc = Fin.castLE (Nat.le_of_succ_le h) :=
  rfl

/--
lemma `castLE_rfl` / 引理 `castLE_rfl`

English:
lemma castLE_rfl
  given: (n : Nat)
  statement: Fin.castLE (le_refl n) = id
  proof: rfl

@[simp]

中文:
引理 castLE_rfl
  条件: (n : 自然数)
  结论: 有限集.castLE (le_refl n) = id
  证明: rfl

@[simp]
-/
@[simp] lemma castLE_rfl (n : Nat) : Fin.castLE (le_refl n) = id :=
  rfl

@[simp]
/--
theorem `range_castLE` / 定理 `range_castLE`

English:
theorem range_castLE
  given: {n k : Nat} (h : n <= k)
  statement: Set.range (castLE h) = { i : Fin k | (i : Nat) < n }
  proof: Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

@[simp]

中文:
定理 range_castLE
  条件: {n k : 自然数} (h : n <= k)
  结论: 集合.range (castLE h) = { i : 有限集 k | (i : 自然数) < n }
  证明: Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

@[simp]

Depends on / 依赖: Set.ext
-/
theorem range_castLE {n k : Nat} (h : n <= k) : Set.range (castLE h) = { i : Fin k | (i : Nat) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

@[simp]
/--
theorem `coe_of_injective_castLE_symm` / 定理 `coe_of_injective_castLE_symm`

English:
theorem coe_of_injective_castLE_symm
  given: {n k : Nat} (h : n <= k) (i : Fin k) (hi)
  proof: by
  rw [← val_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)

中文:
定理 coe_of_injective_castLE_symm
  条件: {n k : 自然数} (h : n <= k) (i : 有限集 k) (hi)
  证明: by
  rw [← val_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)

Depends on / 依赖: Equiv.apply_ofInjective_symm, Fin.val, apply_ofInjective_symm, congr_arg, val_castLE
-/
theorem coe_of_injective_castLE_symm {n k : Nat} (h : n <= k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : Nat) = i := by
  rw [← val_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)

/--
theorem `leftInverse_cast` / 定理 `leftInverse_cast`

English:
theorem leftInverse_cast
  given: (eq : n = m)
  statement: LeftInverse (Fin.cast eq.symm) (Fin.cast eq)
  proof: fun _ => rfl

中文:
定理 leftInverse_cast
  条件: (eq : n = m)
  结论: 左逆 (有限集.cast eq.symm) (有限集.cast eq)
  证明: fun _ => rfl
-/
theorem leftInverse_cast (eq : n = m) : LeftInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl

/--
theorem `rightInverse_cast` / 定理 `rightInverse_cast`

English:
theorem rightInverse_cast
  given: (eq : n = m)
  statement: RightInverse (Fin.cast eq.symm) (Fin.cast eq)
  proof: fun _ => rfl

@[simp]

中文:
定理 rightInverse_cast
  条件: (eq : n = m)
  结论: 右逆 (有限集.cast eq.symm) (有限集.cast eq)
  证明: fun _ => rfl

@[simp]
-/
theorem rightInverse_cast (eq : n = m) : RightInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl

@[simp]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: (eq : n = m) {a b : Fin n}
  statement: a.cast eq = b.cast eq ↔ a = b
  proof: by
  simp [← val_inj]

@[simp]

中文:
定理 cast_inj
  条件: (eq : n = m) {a b : 有限集 n}
  结论: a.cast eq = b.cast eq ↔ a = b
  证明: by
  simp [← val_inj]

@[simp]

Depends on / 依赖: val_inj
-/
theorem cast_inj (eq : n = m) {a b : Fin n} : a.cast eq = b.cast eq ↔ a = b := by
  simp [← val_inj]

@[simp]
/--
theorem `cast_lt_cast` / 定理 `cast_lt_cast`

English:
theorem cast_lt_cast
  given: (eq : n = m) {a b : Fin n}
  statement: a.cast eq < b.cast eq ↔ a < b
  proof: Iff.rfl

@[simp]

中文:
定理 cast_lt_cast
  条件: (eq : n = m) {a b : 有限集 n}
  结论: a.cast eq < b.cast eq ↔ a < b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem cast_lt_cast (eq : n = m) {a b : Fin n} : a.cast eq < b.cast eq ↔ a < b :=
  Iff.rfl

@[simp]
/--
theorem `cast_le_cast` / 定理 `cast_le_cast`

English:
theorem cast_le_cast
  given: (eq : n = m) {a b : Fin n}
  statement: a.cast eq <= b.cast eq ↔ a <= b
  proof: Iff.rfl

中文:
定理 cast_le_cast
  条件: (eq : n = m) {a b : 有限集 n}
  结论: a.cast eq <= b.cast eq ↔ a <= b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem cast_le_cast (eq : n = m) {a b : Fin n} : a.cast eq <= b.cast eq ↔ a <= b :=
  Iff.rfl

/-- The 'identity' equivalence between `Fin m` and `Fin n` when `m = n`. -/
@[simps apply]
/--
Definition of `_root_.finCongr` / `_root_.finCongr` 的定义

English:
definition _root_.finCongr
  signature: (eq : n = m)
  body: Fin.cast eq
  invFun := Fin.cast eq.symm
  left_inv := leftInverse_cast eq
  right_inv := rightInverse_cast eq

中文:
定义 _root_.finCongr
  签名: (eq : n = m)
  定义体: Fin.cast eq
  invFun := Fin.cast eq.symm
  left_inv := leftInverse_cast eq
  right_inv := rightInverse_cast eq

Depends on / 依赖: Fin.cast
-/
def _root_.finCongr (eq : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast eq
  invFun := Fin.cast eq.symm
  left_inv := leftInverse_cast eq
  right_inv := rightInverse_cast eq

/--
theorem `_root_.finCongr_symm_apply` / 定理 `_root_.finCongr_symm_apply`

English:
theorem _root_.finCongr_symm_apply
  given: (eq : n = m) (a : Fin m)
  proof: rfl

中文:
定理 _root_.finCongr_symm_apply
  条件: (eq : n = m) (a : 有限集 m)
  证明: rfl

Depends on / 依赖: List.Nodup.filter, Quot.induction_on, filter, induction_on
-/
theorem _root_.finCongr_symm_apply (eq : n = m) (a : Fin m) :
    (finCongr eq).symm a = a.cast eq.symm := rfl

/--
lemma `_root_.finCongr_apply_mk` / 引理 `_root_.finCongr_apply_mk`

English:
lemma _root_.finCongr_apply_mk
  given: (h : m = n) (k : Nat) (hk : k < m)
  proof: rfl

@[simp]

中文:
引理 _root_.finCongr_apply_mk
  条件: (h : m = n) (k : 自然数) (hk : k < m)
  证明: rfl

@[simp]
-/
@[simp] lemma _root_.finCongr_apply_mk (h : m = n) (k : Nat) (hk : k < m) :
    finCongr h ⟨k, hk⟩ = ⟨k, h ▸ hk⟩ := rfl

@[simp]
/--
lemma `_root_.finCongr_refl` / 引理 `_root_.finCongr_refl`

English:
lemma _root_.finCongr_refl
  given: (h : n = n := rfl)
  statement: finCongr h = Equiv.refl (Fin n)
  proof: by ext; simp

中文:
引理 _root_.finCongr_refl
  条件: (h : n = n := rfl)
  结论: finCongr h = 等价.refl (有限集 n)
  证明: by ext; simp

Depends on / 依赖: Equiv.refl, finCongr
-/
lemma _root_.finCongr_refl (h : n = n := rfl) : finCongr h = Equiv.refl (Fin n) := by ext; simp

/--
lemma `_root_.finCongr_symm` / 引理 `_root_.finCongr_symm`

English:
lemma _root_.finCongr_symm
  given: (h : m = n)
  statement: (finCongr h).symm = finCongr h.symm
  proof: rfl

中文:
引理 _root_.finCongr_symm
  条件: (h : m = n)
  结论: (finCongr h).symm = finCongr h.symm
  证明: rfl
-/
@[simp] lemma _root_.finCongr_symm (h : m = n) : (finCongr h).symm = finCongr h.symm := rfl

/--
lemma `_root_.finCongr_apply_coe` / 引理 `_root_.finCongr_apply_coe`

English:
lemma _root_.finCongr_apply_coe
  given: (h : m = n) (k : Fin m)
  statement: (finCongr h k : Nat) = k
  proof: rfl

中文:
引理 _root_.finCongr_apply_coe
  条件: (h : m = n) (k : 有限集 m)
  结论: (finCongr h k : 自然数) = k
  证明: rfl
-/
@[simp] lemma _root_.finCongr_apply_coe (h : m = n) (k : Fin m) : (finCongr h k : Nat) = k := rfl

/--
lemma `_root_.finCongr_symm_apply_coe` / 引理 `_root_.finCongr_symm_apply_coe`

English:
lemma _root_.finCongr_symm_apply_coe
  given: (h : m = n) (k : Fin n)
  statement: ((finCongr h).symm k : Nat) = k
  proof: rfl

中文:
引理 _root_.finCongr_symm_apply_coe
  条件: (h : m = n) (k : 有限集 n)
  结论: ((finCongr h).symm k : 自然数) = k
  证明: rfl

Depends on / 依赖: Quotient, Quotient.inductionOn, _coe, _some, inductionOn, l.find, quot_mk_to_coe
-/
lemma _root_.finCongr_symm_apply_coe (h : m = n) (k : Fin n) : ((finCongr h).symm k : Nat) = k := rfl

/--
lemma `_root_.finCongr_eq_equivCast` / 引理 `_root_.finCongr_eq_equivCast`

English:
lemma _root_.finCongr_eq_equivCast
  given: (h : n = m)
  statement: finCongr h = .cast (h ▸ rfl)
  proof: by subst h; simp

中文:
引理 _root_.finCongr_eq_equivCast
  条件: (h : n = m)
  结论: finCongr h = .cast (h ▸ rfl)
  证明: by subst h; simp
-/
lemma _root_.finCongr_eq_equivCast (h : n = m) : finCongr h = .cast (h ▸ rfl) := by subst h; simp

/--
theorem `cast_eq_cast` / 定理 `cast_eq_cast`

English:
theorem cast_eq_cast
  given: (h : n = m)
  statement: (Fin.cast h : Fin n -> Fin m) = _root_.cast (h ▸ rfl)
  proof: by
  grind

中文:
定理 cast_eq_cast
  条件: (h : n = m)
  结论: (有限集.cast h : 有限集 n -> 有限集 m) = _root_.cast (h ▸ rfl)
  证明: by
  grind

Depends on / 依赖: Quotient, Quotient.inductionOn, cons_coe, inductionOn, quot_mk_to_coe
-/
theorem cast_eq_cast (h : n = m) : (Fin.cast h : Fin n -> Fin m) = _root_.cast (h ▸ rfl) := by
  grind

/--
theorem `castSucc_le_succ` / 定理 `castSucc_le_succ`

English:
theorem castSucc_le_succ
  given: {n} (i : Fin n)
  statement: i.castSucc <= i.succ
  proof: Nat.le_succ i

中文:
定理 castSucc_le_succ
  条件: {n} (i : 有限集 n)
  结论: i.castSucc <= i.succ
  证明: Nat.le_succ i

Depends on / 依赖: Nat.le_succ, _cons, le_succ
-/
theorem castSucc_le_succ {n} (i : Fin n) : i.castSucc <= i.succ := Nat.le_succ i

/--
theorem `castSucc_le_castSucc_iff` / 定理 `castSucc_le_castSucc_iff`

English:
theorem castSucc_le_castSucc_iff
  given: {a b : Fin n}
  statement: castSucc a <= castSucc b ↔ a <= b
  proof: .rfl

中文:
定理 castSucc_le_castSucc_iff
  条件: {a b : 有限集 n}
  结论: castSucc a <= castSucc b ↔ a <= b
  证明: .rfl

Depends on / 依赖: List.find, Quotient, Quotient.inductionOn, _append
-/
@[simp] theorem castSucc_le_castSucc_iff {a b : Fin n} : castSucc a <= castSucc b ↔ a <= b := .rfl

/--
theorem `succ_le_castSucc_iff` / 定理 `succ_le_castSucc_iff`

English:
theorem succ_le_castSucc_iff
  given: {a b : Fin n}
  statement: succ a <= castSucc b ↔ a < b
  proof: by
  rw [le_castSucc_iff]; rw [succ_lt_succ_iff]

中文:
定理 succ_le_castSucc_iff
  条件: {a b : 有限集 n}
  结论: succ a <= castSucc b ↔ a < b
  证明: by
  rw [le_castSucc_iff]; rw [succ_lt_succ_iff]

Depends on / 依赖: Multiset, Multiset.induction_on, Set.Subsingleton, Subsingleton, _cons, induction_on, mem_cons_self, simp_rw, specialize
-/
@[simp] theorem succ_le_castSucc_iff {a b : Fin n} : succ a <= castSucc b ↔ a < b := by
  rw [le_castSucc_iff]; rw [succ_lt_succ_iff]

/--
theorem `castSucc_lt_succ_iff` / 定理 `castSucc_lt_succ_iff`

English:
theorem castSucc_lt_succ_iff
  given: {a b : Fin n}
  statement: castSucc a < succ b ↔ a <= b
  proof: by
  rw [castSucc_lt_iff_succ_le]; rw [succ_le_succ_iff]

中文:
定理 castSucc_lt_succ_iff
  条件: {a b : 有限集 n}
  结论: castSucc a < succ b ↔ a <= b
  证明: by
  rw [castSucc_lt_iff_succ_le]; rw [succ_le_succ_iff]

Depends on / 依赖: Multiset, Multiset.induction_on, Set.Subsingleton, Subsingleton, _cons, induction_on
-/
@[simp] theorem castSucc_lt_succ_iff {a b : Fin n} : castSucc a < succ b ↔ a <= b := by
  rw [castSucc_lt_iff_succ_le]; rw [succ_le_succ_iff]

/--
theorem `le_of_castSucc_lt_of_succ_lt` / 定理 `le_of_castSucc_lt_of_succ_lt`

English:
theorem le_of_castSucc_lt_of_succ_lt
  statement: {a b : Fin (n + 1)} {i : Fin n}
  proof: by
  simp [Fin.lt_def, -val_fin_lt] at *; lia

中文:
定理 le_of_castSucc_lt_of_succ_lt
  结论: {a b : 有限集 (n + 1)} {i : 有限集 n}
  证明: by
  simp [Fin.lt_def, -val_fin_lt] at *; lia

Depends on / 依赖: Fin.lt_def, List.find, Quotient, Quotient.ind, _congr, lt_def, val_fin_lt
-/
theorem le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n}
    (hl : castSucc i < a) (hu : b < succ i) : b < a := by
  simp [Fin.lt_def, -val_fin_lt] at *; lia

/--
theorem `castSucc_lt_or_lt_succ` / 定理 `castSucc_lt_or_lt_succ`

English:
theorem castSucc_lt_or_lt_succ
  given: (p : Fin (n + 1)) (i : Fin n)
  statement: castSucc i < p ∨ p < i.succ
  proof: by
  simp [Fin.lt_def, -val_fin_lt]
  lia

中文:
定理 castSucc_lt_or_lt_succ
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  结论: castSucc i < p ∨ p < i.succ
  证明: by
  simp [Fin.lt_def, -val_fin_lt]
  lia

Depends on / 依赖: Fin.lt_def, Option.some.injEq, _eq_some_iff, choose_eq_iff, lt_def, val_fin_lt
-/
theorem castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ := by
  simp [Fin.lt_def, -val_fin_lt]
  lia

/--
theorem `succ_le_or_le_castSucc` / 定理 `succ_le_or_le_castSucc`

English:
theorem succ_le_or_le_castSucc
  given: (p : Fin (n + 1)) (i : Fin n)
  statement: succ i <= p ∨ p <= i.castSucc
  proof: by
  rw [le_castSucc_iff]; rw [← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

中文:
定理 succ_le_or_le_castSucc
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  结论: succ i <= p ∨ p <= i.castSucc
  证明: by
  rw [le_castSucc_iff]; rw [← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

Depends on / 依赖: castSucc_lt_iff_succ_le, castSucc_lt_or_lt_succ, le_castSucc_iff, p.castSucc_lt_or_lt_succ
-/
theorem succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i <= p ∨ p <= i.castSucc := by
  rw [le_castSucc_iff]; rw [← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

/--
theorem `eq_castSucc_of_ne_last` / 定理 `eq_castSucc_of_ne_last`

English:
theorem eq_castSucc_of_ne_last
  given: {x : Fin (n + 1)} (h : x != (last _))
  proof: exists_castSucc_eq.mpr h

中文:
定理 eq_castSucc_of_ne_last
  条件: {x : 有限集 (n + 1)} (h : x != (last _))
  证明: exists_castSucc_eq.mpr h

Depends on / 依赖: exists_castSucc_eq, exists_castSucc_eq.mpr
-/
theorem eq_castSucc_of_ne_last {x : Fin (n + 1)} (h : x != (last _)) :
    exists y, Fin.castSucc y = x := exists_castSucc_eq.mpr h

/--
theorem `forall_fin_succ'` / 定理 `forall_fin_succ'`

English:
theorem forall_fin_succ'
  given: {P : Fin (n + 1) -> Prop}
  proof: ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

中文:
定理 对任意_fin_succ'
  条件: {P : 有限集 (n + 1) -> 命题}
  证明: ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

Depends on / 依赖: Fin.lastCases, lastCases
-/
theorem forall_fin_succ' {P : Fin (n + 1) -> Prop} :
    (forall i, P i) ↔ (forall i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

-- to match `Fin.eq_zero_or_eq_succ`
/--
theorem `eq_castSucc_or_eq_last` / 定理 `eq_castSucc_or_eq_last`

English:
theorem eq_castSucc_or_eq_last
  given: {n : Nat} (i : Fin (n + 1))
  proof: i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

@[simp]

中文:
定理 eq_castSucc_or_eq_last
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

@[simp]

Depends on / 依赖: Or.inl, Or.inr, i.lastCases, lastCases
-/
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (exists j : Fin n, i = j.castSucc) ∨ i = last n := i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

@[simp]
/--
theorem `castSucc_ne_last` / 定理 `castSucc_ne_last`

English:
theorem castSucc_ne_last
  given: {n : Nat} (i : Fin n)
  statement: i.castSucc != .last n
  proof: Fin.ne_of_lt i.castSucc_lt_last

中文:
定理 castSucc_ne_last
  条件: {n : 自然数} (i : 有限集 n)
  结论: i.castSucc != .last n
  证明: Fin.ne_of_lt i.castSucc_lt_last

Depends on / 依赖: Fin.ne_of_lt, castSucc_lt_last, i.castSucc_lt_last, ne_of_lt
-/
theorem castSucc_ne_last {n : Nat} (i : Fin n) : i.castSucc != .last n :=
  Fin.ne_of_lt i.castSucc_lt_last

/--
theorem `exists_fin_succ'` / 定理 `exists_fin_succ'`

English:
theorem exists_fin_succ'
  given: {P : Fin (n + 1) -> Prop}
  proof: ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

中文:
定理 存在_fin_succ'
  条件: {P : 有限集 (n + 1) -> 命题}
  证明: ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

Depends on / 依赖: Fin.lastCases, Or.inl, Or.inr, castSucc, h.elim, i.castSucc, lastCases
-/
theorem exists_fin_succ' {P : Fin (n + 1) -> Prop} :
    (exists i, P i) ↔ (exists i : Fin n, P i.castSucc) ∨ P (.last _) :=
  ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

/--
The `Fin.castSucc_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
/--
theorem `castSucc_zero'` / 定理 `castSucc_zero'`

English:
theorem castSucc_zero'
  given: [NeZero n]
  statement: castSucc (0 : Fin n) = 0
  proof: rfl

@[simp]

中文:
定理 castSucc_zero'
  条件: [NeZero n]
  结论: castSucc (0 : 有限集 n) = 0
  证明: rfl

@[simp]
-/
theorem castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0 := rfl

@[simp]
/--
theorem `castSucc_pos_iff` / 定理 `castSucc_pos_iff`

English:
theorem castSucc_pos_iff
  given: [NeZero n] {i : Fin n}
  statement: 0 < castSucc i ↔ 0 < i
  proof: by simp [← val_pos_iff]

中文:
定理 castSucc_pos_iff
  条件: [NeZero n] {i : 有限集 n}
  结论: 0 < castSucc i ↔ 0 < i
  证明: by simp [← val_pos_iff]

Depends on / 依赖: val_pos_iff
-/
theorem castSucc_pos_iff [NeZero n] {i : Fin n} : 0 < castSucc i ↔ 0 < i := by simp [← val_pos_iff]

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis. -/
alias ⟨_, castSucc_pos'⟩ := castSucc_pos_iff

/--
theorem `castSucc_ne_zero_of_lt` / 定理 `castSucc_ne_zero_of_lt`

English:
theorem castSucc_ne_zero_of_lt
  given: {p i : Fin n} (h : p < i)
  statement: castSucc i != 0
  proof: by
  cases n
  · exact i.elim0
  · grind [castSucc_ne_zero_iff]

中文:
定理 castSucc_ne_zero_of_lt
  条件: {p i : 有限集 n} (h : p < i)
  结论: castSucc i != 0
  证明: by
  cases n
  · exact i.elim0
  · grind [castSucc_ne_zero_iff]

Depends on / 依赖: castSucc_ne_zero_iff, i.elim0
-/
theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i != 0 := by
  cases n
  · exact i.elim0
  · grind [castSucc_ne_zero_iff]

/--
theorem `succ_ne_last_iff` / 定理 `succ_ne_last_iff`

English:
theorem succ_ne_last_iff
  given: (a : Fin (n + 1))
  statement: succ a != last (n + 1) ↔ a != last n
  proof: not_iff_not.mpr succ_eq_last_succ

中文:
定理 succ_ne_last_iff
  条件: (a : 有限集 (n + 1))
  结论: succ a != last (n + 1) ↔ a != last n
  证明: not_iff_not.mpr succ_eq_last_succ

Depends on / 依赖: not_iff_not, not_iff_not.mpr, succ_eq_last_succ
-/
theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a != last (n + 1) ↔ a != last n :=
not_iff_not.mpr succ_eq_last_succ

/--
theorem `succ_ne_last_of_lt` / 定理 `succ_ne_last_of_lt`

English:
theorem succ_ne_last_of_lt
  given: {p i : Fin n} (h : i < p)
  statement: succ i != last n
  proof: by
  grind

中文:
定理 succ_ne_last_of_lt
  条件: {p i : 有限集 n} (h : i < p)
  结论: succ i != last n
  证明: by
  grind
-/
theorem succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i != last n := by
  grind

open Fin.NatCast in
@[norm_cast, simp]
/--
theorem `coe_eq_castSucc` / 定理 `coe_eq_castSucc`

English:
theorem coe_eq_castSucc
  given: {a : Fin n}
  statement: ((a : Nat) : Fin (n + 1)) = castSucc a
  proof: by
  ext
  exact val_cast_of_lt (Nat.lt_succ_of_lt a.is_lt)

中文:
定理 coe_eq_castSucc
  条件: {a : 有限集 n}
  结论: ((a : 自然数) : 有限集 (n + 1)) = castSucc a
  证明: by
  ext
  exact val_cast_of_lt (Nat.lt_succ_of_lt a.is_lt)

Depends on / 依赖: Nat.lt_succ_of_lt, a.is_lt, is_lt, lt_succ_of_lt, val_cast_of_lt
-/
theorem coe_eq_castSucc {a : Fin n} : ((a : Nat) : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt_succ_of_lt a.is_lt)

open Fin.NatCast in
/--
theorem `coe_succ_lt_iff_lt` / 定理 `coe_succ_lt_iff_lt`

English:
theorem coe_succ_lt_iff_lt
  given: {n : Nat} {j k : Fin n}
  statement: (j : Fin (n + 1)) < k ↔ j < k
  proof: by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]

中文:
定理 coe_succ_lt_iff_lt
  条件: {n : 自然数} {j k : 有限集 n}
  结论: (j : 有限集 (n + 1)) < k ↔ j < k
  证明: by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]

Depends on / 依赖: castSucc_lt_castSucc_iff, coe_eq_castSucc
-/
theorem coe_succ_lt_iff_lt {n : Nat} {j k : Fin n} : (j : Fin (n + 1)) < k ↔ j < k := by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]
/--
theorem `range_castSucc` / 定理 `range_castSucc`

English:
theorem range_castSucc
  given: {n : Nat}
  statement: Set.range (castSucc : Fin n -> Fin n.succ) =
  proof: range_castLE (by lia)

@[simp]

中文:
定理 range_castSucc
  条件: {n : 自然数}
  结论: 集合.range (castSucc : 有限集 n -> 有限集 n.succ) =
  证明: range_castLE (by lia)

@[simp]

Depends on / 依赖: range_castLE
-/
theorem range_castSucc {n : Nat} : Set.range (castSucc : Fin n -> Fin n.succ) =
    ({ i | (i : Nat) < n } : Set (Fin n.succ)) := range_castLE (by lia)

@[simp]
/--
theorem `coe_of_injective_castSucc_symm` / 定理 `coe_of_injective_castSucc_symm`

English:
theorem coe_of_injective_castSucc_symm
  given: {n : Nat} (i : Fin n.succ) (hi)
  proof: by
  rw [← val_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

中文:
定理 coe_of_injective_castSucc_symm
  条件: {n : 自然数} (i : 有限集 n.succ) (hi)
  证明: by
  rw [← val_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

Depends on / 依赖: Equiv.apply_ofInjective_symm, apply_ofInjective_symm, congr_arg, val_castSucc
-/
theorem coe_of_injective_castSucc_symm {n : Nat} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : Nat) = i := by
  rw [← val_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

/--
theorem `castSucc_castAdd` / 定理 `castSucc_castAdd`

English:
theorem castSucc_castAdd
  given: (i : Fin n)
  statement: castSucc (castAdd m i) = castAdd (m + 1) i
  proof: rfl

中文:
定理 castSucc_castAdd
  条件: (i : 有限集 n)
  结论: castSucc (castAdd m i) = castAdd (m + 1) i
  证明: rfl
-/
theorem castSucc_castAdd (i : Fin n) : castSucc (castAdd m i) = castAdd (m + 1) i := rfl

/--
theorem `succ_castAdd` / 定理 `succ_castAdd`

English:
theorem succ_castAdd
  given: (i : Fin n)
  statement: succ (castAdd m i) =
  proof: by
  split_ifs with h
  exacts [Fin.ext (congr_arg Fin.val h :), rfl]

中文:
定理 succ_castAdd
  条件: (i : 有限集 n)
  结论: succ (castAdd m i) =
  证明: by
  split_ifs with h
  exacts [Fin.ext (congr_arg Fin.val h :), rfl]

Depends on / 依赖: Fin.ext, Fin.val, congr_arg, exacts, split_ifs
-/
theorem succ_castAdd (i : Fin n) : succ (castAdd m i) =
    if h : i.succ = last _ then natAdd n (0 : Fin (m + 1))
      else castAdd (m + 1) ⟨i.1 + 1, lt_of_le_of_ne i.2 (Fin.val_ne_iff.mpr h)⟩ := by
  split_ifs with h
  exacts [Fin.ext (congr_arg Fin.val h :), rfl]

/--
theorem `succ_natAdd` / 定理 `succ_natAdd`

English:
theorem succ_natAdd
  given: (i : Fin m)
  statement: succ (natAdd n i) = natAdd n (succ i)
  proof: rfl

中文:
定理 succ_natAdd
  条件: (i : 有限集 m)
  结论: succ (natAdd n i) = natAdd n (succ i)
  证明: rfl
-/
theorem succ_natAdd (i : Fin m) : succ (natAdd n i) = natAdd n (succ i) := rfl

/--
theorem `sub_castAdd_eq_castAdd_sub_of_le` / 定理 `sub_castAdd_eq_castAdd_sub_of_le`

English:
theorem sub_castAdd_eq_castAdd_sub_of_le
  given: {n : Nat} {a b : Fin n} (h : b <= a)
  proof: by
  grind [Fin.sub_val_of_le]

中文:
定理 sub_castAdd_eq_castAdd_sub_of_le
  条件: {n : 自然数} {a b : 有限集 n} (h : b <= a)
  证明: by
  grind [Fin.sub_val_of_le]

Depends on / 依赖: Fin.sub_val_of_le, sub_val_of_le
-/
theorem sub_castAdd_eq_castAdd_sub_of_le {n : Nat} {a b : Fin n} (h : b <= a) :
    a.castAdd m - b.castAdd m = (a - b).castAdd m := by
  grind [Fin.sub_val_of_le]

/--
theorem `sub_castSucc_eq_castSucc_sub_of_le` / 定理 `sub_castSucc_eq_castSucc_sub_of_le`

English:
theorem sub_castSucc_eq_castSucc_sub_of_le
  given: {n : Nat} {a b : Fin n} (h : b <= a)
  proof: sub_castAdd_eq_castAdd_sub_of_le h

中文:
定理 sub_castSucc_eq_castSucc_sub_of_le
  条件: {n : 自然数} {a b : 有限集 n} (h : b <= a)
  证明: sub_castAdd_eq_castAdd_sub_of_le h

Depends on / 依赖: sub_castAdd_eq_castAdd_sub_of_le
-/
theorem sub_castSucc_eq_castSucc_sub_of_le {n : Nat} {a b : Fin n} (h : b <= a) :
    a.castSucc - b.castSucc = (a - b).castSucc := sub_castAdd_eq_castAdd_sub_of_le h

end Succ

section Pred


/--
theorem `pred_one'` / 定理 `pred_one'`

English:
theorem pred_one'
  given: [NeZero n] (h := (zero_ne_one' (n := n)).symm)
  proof: by
  simp_rw [Fin.ext_iff, val_pred, val_one', val_zero, Nat.sub_eq_zero_iff_le, Nat.mod_le]

中文:
定理 pred_one'
  条件: [NeZero n] (h := (zero_ne_one' (n := n)).symm)
  证明: by
  simp_rw [Fin.ext_iff, val_pred, val_one', val_zero, Nat.sub_eq_zero_iff_le, Nat.mod_le]

Depends on / 依赖: zero_ne_one
-/
theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm) :
    Fin.pred (1 : Fin (n + 1)) h = 0 := by
  simp_rw [Fin.ext_iff, val_pred, val_one', val_zero, Nat.sub_eq_zero_iff_le, Nat.mod_le]

/--
theorem `pred_last` / 定理 `pred_last`

English:
theorem pred_last
  given: (h := Fin.ext_iff.not.2 last_pos'.ne')
  proof: by simp_rw [← succ_last, pred_succ]

中文:
定理 pred_last
  条件: (h := 有限集.ext_iff.not.2 last_pos'.ne')
  证明: by simp_rw [← succ_last, pred_succ]

Depends on / 依赖: Fin.ext_iff.not, ext_iff, last_pos
-/
theorem pred_last (h := Fin.ext_iff.not.2 last_pos'.ne') :
    pred (last (n + 1)) h = last n := by simp_rw [← succ_last, pred_succ]

/--
theorem `pred_lt_iff` / 定理 `pred_lt_iff`

English:
theorem pred_lt_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
  statement: pred i hi < j ↔ i < succ j
  proof: by
  rw [← succ_lt_succ_iff]; rw [succ_pred]

中文:
定理 pred_lt_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != 0)
  结论: pred i hi < j ↔ i < succ j
  证明: by
  rw [← succ_lt_succ_iff]; rw [succ_pred]

Depends on / 依赖: succ_lt_succ_iff, succ_pred
-/
theorem pred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : pred i hi < j ↔ i < succ j := by
  rw [← succ_lt_succ_iff]; rw [succ_pred]
/--
theorem `lt_pred_iff` / 定理 `lt_pred_iff`

English:
theorem lt_pred_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
  statement: j < pred i hi ↔ succ j < i
  proof: by
  rw [← succ_lt_succ_iff]; rw [succ_pred]

中文:
定理 lt_pred_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != 0)
  结论: j < pred i hi ↔ succ j < i
  证明: by
  rw [← succ_lt_succ_iff]; rw [succ_pred]

Depends on / 依赖: succ_lt_succ_iff, succ_pred
-/
theorem lt_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : j < pred i hi ↔ succ j < i := by
  rw [← succ_lt_succ_iff]; rw [succ_pred]
/--
theorem `pred_le_iff` / 定理 `pred_le_iff`

English:
theorem pred_le_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
  statement: pred i hi <= j ↔ i <= succ j
  proof: by
  rw [← succ_le_succ_iff]; rw [succ_pred]

中文:
定理 pred_le_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != 0)
  结论: pred i hi <= j ↔ i <= succ j
  证明: by
  rw [← succ_le_succ_iff]; rw [succ_pred]

Depends on / 依赖: succ_le_succ_iff, succ_pred
-/
theorem pred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : pred i hi <= j ↔ i <= succ j := by
  rw [← succ_le_succ_iff]; rw [succ_pred]
/--
theorem `le_pred_iff` / 定理 `le_pred_iff`

English:
theorem le_pred_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != 0)
  statement: j <= pred i hi ↔ succ j <= i
  proof: by
  rw [← succ_le_succ_iff]; rw [succ_pred]

中文:
定理 le_pred_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != 0)
  结论: j <= pred i hi ↔ succ j <= i
  证明: by
  rw [← succ_le_succ_iff]; rw [succ_pred]

Depends on / 依赖: succ_le_succ_iff, succ_pred
-/
theorem le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != 0) : j <= pred i hi ↔ succ j <= i := by
  rw [← succ_le_succ_iff]; rw [succ_pred]

/--
theorem `castSucc_pred_eq_pred_castSucc` / 定理 `castSucc_pred_eq_pred_castSucc`

English:
theorem castSucc_pred_eq_pred_castSucc
  given: {a : Fin (n + 1)} (ha : a != 0)
  proof: rfl

中文:
定理 castSucc_pred_eq_pred_castSucc
  条件: {a : 有限集 (n + 1)} (ha : a != 0)
  证明: rfl
-/
theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a != 0) :
    (a.pred ha).castSucc = (castSucc a).pred (castSucc_ne_zero_iff.mpr ha) := rfl

/--
theorem `castSucc_pred_add_one_eq` / 定理 `castSucc_pred_add_one_eq`

English:
theorem castSucc_pred_add_one_eq
  given: {a : Fin (n + 1)} (ha : a != 0)
  proof: by
  simp

中文:
定理 castSucc_pred_add_one_eq
  条件: {a : 有限集 (n + 1)} (ha : a != 0)
  证明: by
  simp
-/
theorem castSucc_pred_add_one_eq {a : Fin (n + 1)} (ha : a != 0) :
    (a.pred ha).castSucc + 1 = a := by
  simp

/--
theorem `le_pred_castSucc_iff` / 定理 `le_pred_castSucc_iff`

English:
theorem le_pred_castSucc_iff
  given: {a b : Fin (n + 1)} (ha : castSucc a != 0)
  proof: by
  rw [le_pred_iff]; rw [succ_le_castSucc_iff]

中文:
定理 le_pred_castSucc_iff
  条件: {a b : 有限集 (n + 1)} (ha : castSucc a != 0)
  证明: by
  rw [le_pred_iff]; rw [succ_le_castSucc_iff]

Depends on / 依赖: le_pred_iff, succ_le_castSucc_iff
-/
theorem le_pred_castSucc_iff {a b : Fin (n + 1)} (ha : castSucc a != 0) :
    b <= (castSucc a).pred ha ↔ b < a := by
  rw [le_pred_iff]; rw [succ_le_castSucc_iff]

/--
theorem `pred_castSucc_lt_iff` / 定理 `pred_castSucc_lt_iff`

English:
theorem pred_castSucc_lt_iff
  given: {a b : Fin (n + 1)} (ha : castSucc a != 0)
  proof: by
  rw [pred_lt_iff]; rw [castSucc_lt_succ_iff]

中文:
定理 pred_castSucc_lt_iff
  条件: {a b : 有限集 (n + 1)} (ha : castSucc a != 0)
  证明: by
  rw [pred_lt_iff]; rw [castSucc_lt_succ_iff]

Depends on / 依赖: castSucc_lt_succ_iff, pred_lt_iff
-/
theorem pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha : castSucc a != 0) :
    (castSucc a).pred ha < b ↔ a <= b := by
  rw [pred_lt_iff]; rw [castSucc_lt_succ_iff]

/--
theorem `pred_castSucc_lt` / 定理 `pred_castSucc_lt`

English:
theorem pred_castSucc_lt
  given: {a : Fin (n + 1)} (ha : castSucc a != 0)
  proof: by rw [pred_castSucc_lt_iff, le_def]

中文:
定理 pred_castSucc_lt
  条件: {a : 有限集 (n + 1)} (ha : castSucc a != 0)
  证明: by rw [pred_castSucc_lt_iff, le_def]

Depends on / 依赖: le_def, pred_castSucc_lt_iff
-/
theorem pred_castSucc_lt {a : Fin (n + 1)} (ha : castSucc a != 0) :
    (castSucc a).pred ha < a := by rw [pred_castSucc_lt_iff, le_def]

/--
theorem `le_castSucc_pred_iff` / 定理 `le_castSucc_pred_iff`

English:
theorem le_castSucc_pred_iff
  given: {a b : Fin (n + 1)} (ha : a != 0)
  proof: by
  rw [castSucc_pred_eq_pred_castSucc]; rw [le_pred_castSucc_iff]

中文:
定理 le_castSucc_pred_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != 0)
  证明: by
  rw [castSucc_pred_eq_pred_castSucc]; rw [le_pred_castSucc_iff]

Depends on / 依赖: castSucc_pred_eq_pred_castSucc, le_pred_castSucc_iff
-/
theorem le_castSucc_pred_iff {a b : Fin (n + 1)} (ha : a != 0) :
    b <= castSucc (a.pred ha) ↔ b < a := by
  rw [castSucc_pred_eq_pred_castSucc]; rw [le_pred_castSucc_iff]

/--
theorem `castSucc_pred_lt_iff` / 定理 `castSucc_pred_lt_iff`

English:
theorem castSucc_pred_lt_iff
  given: {a b : Fin (n + 1)} (ha : a != 0)
  proof: by
  rw [castSucc_pred_eq_pred_castSucc]; rw [pred_castSucc_lt_iff]

中文:
定理 castSucc_pred_lt_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != 0)
  证明: by
  rw [castSucc_pred_eq_pred_castSucc]; rw [pred_castSucc_lt_iff]

Depends on / 依赖: castSucc_pred_eq_pred_castSucc, pred_castSucc_lt_iff
-/
theorem castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha : a != 0) :
    castSucc (a.pred ha) < b ↔ a <= b := by
  rw [castSucc_pred_eq_pred_castSucc]; rw [pred_castSucc_lt_iff]

/--
theorem `castSucc_pred_lt` / 定理 `castSucc_pred_lt`

English:
theorem castSucc_pred_lt
  given: {a : Fin (n + 1)} (ha : a != 0)
  proof: by rw [castSucc_pred_lt_iff, le_def]

中文:
定理 castSucc_pred_lt
  条件: {a : 有限集 (n + 1)} (ha : a != 0)
  证明: by rw [castSucc_pred_lt_iff, le_def]

Depends on / 依赖: castSucc_pred_lt_iff, le_def
-/
theorem castSucc_pred_lt {a : Fin (n + 1)} (ha : a != 0) :
    castSucc (a.pred ha) < a := by rw [castSucc_pred_lt_iff, le_def]

end Pred

section CastPred

/--
Definition of `castPred` / `castPred` 的定义

English:
definition castPred
  signature: (i : Fin (n + 1)) (h : i != last n)
  body: castLT i (val_lt_last h)

@[simp]

中文:
定义 castPred
  签名: (i : 有限集 (n + 1)) (h : i != last n)
  定义体: castLT i (val_lt_last h)

@[simp]
-/
@[inline] def castPred (i : Fin (n + 1)) (h : i != last n) : Fin n := castLT i (val_lt_last h)

@[simp]
/--
lemma `castLT_eq_castPred` / 引理 `castLT_eq_castPred`

English:
lemma castLT_eq_castPred
  given: (i : Fin (n + 1)) (h : i < last _) (h' := Fin.ext_iff.not.2 h.ne)
  proof: rfl

@[simp]

中文:
引理 castLT_eq_castPred
  条件: (i : 有限集 (n + 1)) (h : i < last _) (h' := 有限集.ext_iff.not.2 h.ne)
  证明: rfl

@[simp]

Depends on / 依赖: Fin.ext_iff.not, ext_iff, h.ne
-/
lemma castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h' := Fin.ext_iff.not.2 h.ne) :
    castLT i h = castPred i h' := rfl

@[simp]
/--
lemma `coe_castPred` / 引理 `coe_castPred`

English:
lemma coe_castPred
  given: (i : Fin (n + 1)) (h : i != last _)
  statement: (castPred i h : Nat) = i
  proof: rfl

@[simp]

中文:
引理 coe_castPred
  条件: (i : 有限集 (n + 1)) (h : i != last _)
  结论: (castPred i h : 自然数) = i
  证明: rfl

@[simp]
-/
lemma coe_castPred (i : Fin (n + 1)) (h : i != last _) : (castPred i h : Nat) = i := rfl

@[simp]
/--
theorem `castPred_castSucc` / 定理 `castPred_castSucc`

English:
theorem castPred_castSucc
  given: {i : Fin n} (h' := Fin.ext_iff.not.2 (castSucc_lt_last i).ne)
  proof: rfl

@[simp]

中文:
定理 castPred_castSucc
  条件: {i : 有限集 n} (h' := 有限集.ext_iff.not.2 (castSucc_lt_last i).ne)
  证明: rfl

@[simp]

Depends on / 依赖: Fin.ext_iff.not, castSucc_lt_last, ext_iff
-/
theorem castPred_castSucc {i : Fin n} (h' := Fin.ext_iff.not.2 (castSucc_lt_last i).ne) :
    castPred (castSucc i) h' = i := rfl

@[simp]
/--
theorem `castSucc_castPred` / 定理 `castSucc_castPred`

English:
theorem castSucc_castPred
  given: (i : Fin (n + 1)) (h : i != last n)
  proof: by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]

中文:
定理 castSucc_castPred
  条件: (i : 有限集 (n + 1)) (h : i != last n)
  证明: by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]

Depends on / 依赖: castPred_castSucc, exists_castSucc_eq, exists_castSucc_eq.mpr
-/
theorem castSucc_castPred (i : Fin (n + 1)) (h : i != last n) :
    castSucc (i.castPred h) = i := by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]

/--
theorem `castPred_eq_iff_eq_castSucc` / 定理 `castPred_eq_iff_eq_castSucc`

English:
theorem castPred_eq_iff_eq_castSucc
  given: (i : Fin (n + 1)) (hi : i != last _) (j : Fin n)
  proof: ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]

中文:
定理 castPred_eq_iff_eq_castSucc
  条件: (i : 有限集 (n + 1)) (hi : i != last _) (j : 有限集 n)
  证明: ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]

Depends on / 依赖: castPred_castSucc, castSucc_castPred, simp_rw
-/
theorem castPred_eq_iff_eq_castSucc (i : Fin (n + 1)) (hi : i != last _) (j : Fin n) :
    castPred i hi = j ↔ i = castSucc j :=
  ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]
/--
theorem `castPred_mk` / 定理 `castPred_mk`

English:
theorem castPred_mk
  statement: (i : Nat) (h₁ : i < n) (h₂ := h₁.trans (Nat.lt_succ_self _))
  proof: rfl

@[simp]

中文:
定理 castPred_mk
  结论: (i : 自然数) (h₁ : i < n) (h₂ := h₁.trans (自然数.lt_succ_self _))
  证明: rfl

@[simp]

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self
-/
theorem castPred_mk (i : Nat) (h₁ : i < n) (h₂ := h₁.trans (Nat.lt_succ_self _))
    (h₃ : ⟨i, h₂⟩ != last _ := (ne_iff_vne _ _).mpr (val_last _ ▸ h₁.ne)) :
    castPred ⟨i, h₂⟩ h₃ = ⟨i, h₁⟩ := rfl

@[simp]
/--
theorem `castPred_le_castPred_iff` / 定理 `castPred_le_castPred_iff`

English:
theorem castPred_le_castPred_iff
  given: {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n}
  proof: Iff.rfl

中文:
定理 castPred_le_castPred_iff
  条件: {i j : 有限集 (n + 1)} {hi : i != last n} {hj : j != last n}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem castPred_le_castPred_iff {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n} :
    castPred i hi <= castPred j hj ↔ i <= j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_le_castPred_iff`
that deduces `i ≠ last n` from `i ≤ j` and `j ≠ last n`. -/
@[gcongr]
/--
theorem `castPred_le_castPred` / 定理 `castPred_le_castPred`

English:
theorem castPred_le_castPred
  given: {i j : Fin (n + 1)} (h : i <= j) (hj : j != last n)
  proof: h

@[simp]

中文:
定理 castPred_le_castPred
  条件: {i j : 有限集 (n + 1)} (h : i <= j) (hj : j != last n)
  证明: h

@[simp]
-/
theorem castPred_le_castPred {i j : Fin (n + 1)} (h : i <= j) (hj : j != last n) :
    castPred i (by rw [← lt_last_iff_ne_last] at hj ⊢; exact Fin.lt_of_le_of_lt h hj) <=
      castPred j hj :=
  h

@[simp]
/--
theorem `castPred_lt_castPred_iff` / 定理 `castPred_lt_castPred_iff`

English:
theorem castPred_lt_castPred_iff
  given: {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n}
  proof: Iff.rfl

中文:
定理 castPred_lt_castPred_iff
  条件: {i j : 有限集 (n + 1)} {hi : i != last n} {hj : j != last n}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem castPred_lt_castPred_iff {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n} :
    castPred i hi < castPred j hj ↔ i < j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_lt_castPred_iff`
that deduces `i ≠ last n` from `i < j`. -/
@[gcongr]
/--
theorem `castPred_lt_castPred` / 定理 `castPred_lt_castPred`

English:
theorem castPred_lt_castPred
  given: {i j : Fin (n + 1)} (h : i < j) (hj : j != last n)
  proof: h

中文:
定理 castPred_lt_castPred
  条件: {i j : 有限集 (n + 1)} (h : i < j) (hj : j != last n)
  证明: h
-/
theorem castPred_lt_castPred {i j : Fin (n + 1)} (h : i < j) (hj : j != last n) :
    castPred i (ne_last_of_lt h) < castPred j hj := h

/--
theorem `castPred_lt_iff` / 定理 `castPred_lt_iff`

English:
theorem castPred_lt_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != last n)
  proof: by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

中文:
定理 castPred_lt_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != last n)
  证明: by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

Depends on / 依赖: castSucc_castPred, castSucc_lt_castSucc_iff
-/
theorem castPred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) :
    castPred i hi < j ↔ i < castSucc j := by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

/--
theorem `lt_castPred_iff` / 定理 `lt_castPred_iff`

English:
theorem lt_castPred_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != last n)
  proof: by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

中文:
定理 lt_castPred_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != last n)
  证明: by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

Depends on / 依赖: castSucc_castPred, castSucc_lt_castSucc_iff
-/
theorem lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) :
    j < castPred i hi ↔ castSucc j < i := by
  rw [← castSucc_lt_castSucc_iff]; rw [castSucc_castPred]

/--
theorem `castPred_le_iff` / 定理 `castPred_le_iff`

English:
theorem castPred_le_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != last n)
  proof: by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

中文:
定理 castPred_le_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != last n)
  证明: by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

Depends on / 依赖: castSucc_castPred, castSucc_le_castSucc_iff
-/
theorem castPred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) :
    castPred i hi <= j ↔ i <= castSucc j := by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

/--
theorem `le_castPred_iff` / 定理 `le_castPred_iff`

English:
theorem le_castPred_iff
  given: {j : Fin n} {i : Fin (n + 1)} (hi : i != last n)
  proof: by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

@[simp]

中文:
定理 le_castPred_iff
  条件: {j : 有限集 n} {i : 有限集 (n + 1)} (hi : i != last n)
  证明: by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

@[simp]

Depends on / 依赖: castSucc_castPred, castSucc_le_castSucc_iff, d.filter, filter, ndinter_eq_inter
-/
theorem le_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i != last n) :
    j <= castPred i hi ↔ castSucc j <= i := by
  rw [← castSucc_le_castSucc_iff]; rw [castSucc_castPred]

@[simp]
/--
theorem `castPred_inj` / 定理 `castPred_inj`

English:
theorem castPred_inj
  given: {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n}
  proof: by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

@[simp]

中文:
定理 castPred_inj
  条件: {i j : 有限集 (n + 1)} {hi : i != last n} {hj : j != last n}
  证明: by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

@[simp]

Depends on / 依赖: Fin.ext_iff, castPred_le_castPred_iff, ext_iff, le_antisymm_iff, le_def, simp_rw
-/
theorem castPred_inj {i j : Fin (n + 1)} {hi : i != last n} {hj : j != last n} :
    castPred i hi = castPred j hj ↔ i = j := by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

@[simp]
/--
theorem `castPred_zero` / 定理 `castPred_zero`

English:
theorem castPred_zero
  given: [NeZero n]
  proof: rfl

@[simp]

中文:
定理 castPred_zero
  条件: [NeZero n]
  证明: rfl

@[simp]
-/
theorem castPred_zero [NeZero n] :
    castPred (0 : Fin (n + 1)) (Fin.ext_iff.not.2 last_pos'.ne) = 0 := rfl

@[simp]
/--
theorem `castPred_eq_zero` / 定理 `castPred_eq_zero`

English:
theorem castPred_eq_zero
  given: [NeZero n] {i : Fin (n + 1)} (h : i != last n)
  proof: by
  rw [← castPred_zero]; rw [castPred_inj]

中文:
定理 castPred_eq_zero
  条件: [NeZero n] {i : 有限集 (n + 1)} (h : i != last n)
  证明: by
  rw [← castPred_zero]; rw [castPred_inj]

Depends on / 依赖: castPred_inj, castPred_zero
-/
theorem castPred_eq_zero [NeZero n] {i : Fin (n + 1)} (h : i != last n) :
    Fin.castPred i h = 0 ↔ i = 0 := by
  rw [← castPred_zero]; rw [castPred_inj]

/--
theorem `castPred_ne_zero` / 定理 `castPred_ne_zero`

English:
theorem castPred_ne_zero
  given: [NeZero n] {i : Fin (n + 1)} (h₁ : i != last n) (h₂ : i != 0)
  proof: (castPred_eq_zero h₁).not.mpr h₂

@[simp]

中文:
定理 castPred_ne_zero
  条件: [NeZero n] {i : 有限集 (n + 1)} (h₁ : i != last n) (h₂ : i != 0)
  证明: (castPred_eq_zero h₁).not.mpr h₂

@[simp]

Depends on / 依赖: castPred_eq_zero, not.mpr
-/
theorem castPred_ne_zero [NeZero n] {i : Fin (n + 1)} (h₁ : i != last n) (h₂ : i != 0) :
    castPred i h₁ != 0 :=
  (castPred_eq_zero h₁).not.mpr h₂

@[simp]
/--
theorem `castPred_one` / 定理 `castPred_one`

English:
theorem castPred_one
  given: [NeZero n]
  proof: by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl

中文:
定理 castPred_one
  条件: [NeZero n]
  证明: by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl

Depends on / 依赖: subsingleton_one, subsingleton_one.elim
-/
theorem castPred_one [NeZero n] :
    castPred (1 : Fin (n + 2)) (Fin.ext_iff.not.2 one_lt_last.ne) = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl

/--
theorem `succ_castPred_eq_castPred_succ` / 定理 `succ_castPred_eq_castPred_succ`

English:
theorem succ_castPred_eq_castPred_succ
  statement: {a : Fin (n + 1)} (ha : a != last n)
  proof: rfl

中文:
定理 succ_castPred_eq_castPred_succ
  结论: {a : 有限集 (n + 1)} (ha : a != last n)
  证明: rfl

Depends on / 依赖: a.succ_ne_last_iff.mpr, succ_ne_last_iff
-/
theorem succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a != last n)
    (ha' := a.succ_ne_last_iff.mpr ha) :
    (a.castPred ha).succ = (succ a).castPred ha' := rfl

/--
theorem `succ_castPred_eq_add_one` / 定理 `succ_castPred_eq_add_one`

English:
theorem succ_castPred_eq_add_one
  given: {a : Fin (n + 1)} (ha : a != last n)
  proof: by
  cases a using lastCases
  · exact (ha rfl).elim
  · rw [castPred_castSucc, coeSucc_eq_succ]

中文:
定理 succ_castPred_eq_add_one
  条件: {a : 有限集 (n + 1)} (ha : a != last n)
  证明: by
  cases a using lastCases
  · exact (ha rfl).elim
  · rw [castPred_castSucc, coeSucc_eq_succ]

Depends on / 依赖: castPred_castSucc, coeSucc_eq_succ, lastCases
-/
theorem succ_castPred_eq_add_one {a : Fin (n + 1)} (ha : a != last n) :
    (a.castPred ha).succ = a + 1 := by
  cases a using lastCases
  · exact (ha rfl).elim
  · rw [castPred_castSucc, coeSucc_eq_succ]

/--
theorem `castpred_succ_le_iff` / 定理 `castpred_succ_le_iff`

English:
theorem castpred_succ_le_iff
  given: {a b : Fin (n + 1)} (ha : succ a != last (n + 1))
  proof: by
  rw [castPred_le_iff]; rw [succ_le_castSucc_iff]

中文:
定理 castpred_succ_le_iff
  条件: {a b : 有限集 (n + 1)} (ha : succ a != last (n + 1))
  证明: by
  rw [castPred_le_iff]; rw [succ_le_castSucc_iff]

Depends on / 依赖: castPred_le_iff, succ_le_castSucc_iff
-/
theorem castpred_succ_le_iff {a b : Fin (n + 1)} (ha : succ a != last (n + 1)) :
    (succ a).castPred ha <= b ↔ a < b := by
  rw [castPred_le_iff]; rw [succ_le_castSucc_iff]

/--
theorem `lt_castPred_succ_iff` / 定理 `lt_castPred_succ_iff`

English:
theorem lt_castPred_succ_iff
  given: {a b : Fin (n + 1)} (ha : succ a != last (n + 1))
  proof: by
  rw [lt_castPred_iff]; rw [castSucc_lt_succ_iff]

中文:
定理 lt_castPred_succ_iff
  条件: {a b : 有限集 (n + 1)} (ha : succ a != last (n + 1))
  证明: by
  rw [lt_castPred_iff]; rw [castSucc_lt_succ_iff]

Depends on / 依赖: castSucc_lt_succ_iff, lt_castPred_iff
-/
theorem lt_castPred_succ_iff {a b : Fin (n + 1)} (ha : succ a != last (n + 1)) :
    b < (succ a).castPred ha ↔ b <= a := by
  rw [lt_castPred_iff]; rw [castSucc_lt_succ_iff]

/--
theorem `lt_castPred_succ` / 定理 `lt_castPred_succ`

English:
theorem lt_castPred_succ
  given: {a : Fin (n + 1)} (ha : succ a != last (n + 1))
  proof: by rw [lt_castPred_succ_iff, le_def]

中文:
定理 lt_castPred_succ
  条件: {a : 有限集 (n + 1)} (ha : succ a != last (n + 1))
  证明: by rw [lt_castPred_succ_iff, le_def]

Depends on / 依赖: le_def, lt_castPred_succ_iff
-/
theorem lt_castPred_succ {a : Fin (n + 1)} (ha : succ a != last (n + 1)) :
    a < (succ a).castPred ha := by rw [lt_castPred_succ_iff, le_def]

/--
theorem `succ_castPred_le_iff` / 定理 `succ_castPred_le_iff`

English:
theorem succ_castPred_le_iff
  given: {a b : Fin (n + 1)} (ha : a != last n)
  proof: by
  rw [succ_castPred_eq_castPred_succ ha]; rw [castpred_succ_le_iff]

中文:
定理 succ_castPred_le_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != last n)
  证明: by
  rw [succ_castPred_eq_castPred_succ ha]; rw [castpred_succ_le_iff]

Depends on / 依赖: castpred_succ_le_iff, succ_castPred_eq_castPred_succ
-/
theorem succ_castPred_le_iff {a b : Fin (n + 1)} (ha : a != last n) :
    succ (a.castPred ha) <= b ↔ a < b := by
  rw [succ_castPred_eq_castPred_succ ha]; rw [castpred_succ_le_iff]

/--
theorem `lt_succ_castPred_iff` / 定理 `lt_succ_castPred_iff`

English:
theorem lt_succ_castPred_iff
  given: {a b : Fin (n + 1)} (ha : a != last n)
  proof: by
  rw [succ_castPred_eq_castPred_succ ha]; rw [lt_castPred_succ_iff]

中文:
定理 lt_succ_castPred_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != last n)
  证明: by
  rw [succ_castPred_eq_castPred_succ ha]; rw [lt_castPred_succ_iff]

Depends on / 依赖: lt_castPred_succ_iff, succ_castPred_eq_castPred_succ
-/
theorem lt_succ_castPred_iff {a b : Fin (n + 1)} (ha : a != last n) :
    b < succ (a.castPred ha) ↔ b <= a := by
  rw [succ_castPred_eq_castPred_succ ha]; rw [lt_castPred_succ_iff]

/--
theorem `lt_succ_castPred` / 定理 `lt_succ_castPred`

English:
theorem lt_succ_castPred
  given: {a : Fin (n + 1)} (ha : a != last n)
  proof: by rw [lt_succ_castPred_iff, le_def]

中文:
定理 lt_succ_castPred
  条件: {a : 有限集 (n + 1)} (ha : a != last n)
  证明: by rw [lt_succ_castPred_iff, le_def]

Depends on / 依赖: le_def, lt_succ_castPred_iff
-/
theorem lt_succ_castPred {a : Fin (n + 1)} (ha : a != last n) :
    a < succ (a.castPred ha) := by rw [lt_succ_castPred_iff, le_def]

/--
theorem `castPred_le_pred_iff` / 定理 `castPred_le_pred_iff`

English:
theorem castPred_le_pred_iff
  given: {a b : Fin (n + 1)} (ha : a != last n) (hb : b != 0)
  proof: by
  rw [le_pred_iff]; rw [succ_castPred_le_iff]

中文:
定理 castPred_le_pred_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != last n) (hb : b != 0)
  证明: by
  rw [le_pred_iff]; rw [succ_castPred_le_iff]

Depends on / 依赖: le_pred_iff, succ_castPred_le_iff
-/
theorem castPred_le_pred_iff {a b : Fin (n + 1)} (ha : a != last n) (hb : b != 0) :
    castPred a ha <= pred b hb ↔ a < b := by
  rw [le_pred_iff]; rw [succ_castPred_le_iff]

/--
theorem `pred_lt_castPred_iff` / 定理 `pred_lt_castPred_iff`

English:
theorem pred_lt_castPred_iff
  given: {a b : Fin (n + 1)} (ha : a != 0) (hb : b != last n)
  proof: by
  rw [lt_castPred_iff]; rw [castSucc_pred_lt_iff ha]

中文:
定理 pred_lt_castPred_iff
  条件: {a b : 有限集 (n + 1)} (ha : a != 0) (hb : b != last n)
  证明: by
  rw [lt_castPred_iff]; rw [castSucc_pred_lt_iff ha]

Depends on / 依赖: castSucc_pred_lt_iff, lt_castPred_iff
-/
theorem pred_lt_castPred_iff {a b : Fin (n + 1)} (ha : a != 0) (hb : b != last n) :
    pred a ha < castPred b hb ↔ a <= b := by
  rw [lt_castPred_iff]; rw [castSucc_pred_lt_iff ha]

/--
theorem `pred_lt_castPred` / 定理 `pred_lt_castPred`

English:
theorem pred_lt_castPred
  given: {a : Fin (n + 1)} (h₁ : a != 0) (h₂ : a != last n)
  proof: by
  rw [pred_lt_castPred_iff]; rw [le_def]

中文:
定理 pred_lt_castPred
  条件: {a : 有限集 (n + 1)} (h₁ : a != 0) (h₂ : a != last n)
  证明: by
  rw [pred_lt_castPred_iff]; rw [le_def]

Depends on / 依赖: le_def, pred_lt_castPred_iff
-/
theorem pred_lt_castPred {a : Fin (n + 1)} (h₁ : a != 0) (h₂ : a != last n) :
    pred a h₁ < castPred a h₂ := by
  rw [pred_lt_castPred_iff]; rw [le_def]

/--
theorem `val_sub_castLT_of_le` / 定理 `val_sub_castLT_of_le`

English:
theorem val_sub_castLT_of_le
  given: {a b : Fin m} (ha : a.val < n) (h : b <= a)
  proof: by
  have : b.castLT (lt_of_le_of_lt h ha) <= a.castLT ha := by simpa [← val_fin_le] using h
  simp [sub_val_of_le, h, this]

中文:
定理 val_sub_castLT_of_le
  条件: {a b : 有限集 m} (ha : a.val < n) (h : b <= a)
  证明: by
  have : b.castLT (lt_of_le_of_lt h ha) <= a.castLT ha := by simpa [← val_fin_le] using h
  simp [sub_val_of_le, h, this]

Depends on / 依赖: a.castLT, b.castLT, castLT, lt_of_le_of_lt, sub_val_of_le, val_fin_le
-/
theorem val_sub_castLT_of_le {a b : Fin m} (ha : a.val < n) (h : b <= a) :
    (a.castLT ha - b.castLT (lt_of_le_of_lt h ha)).val = (a - b).val := by
  have : b.castLT (lt_of_le_of_lt h ha) <= a.castLT ha := by simpa [← val_fin_le] using h
  simp [sub_val_of_le, h, this]

/--
theorem `sub_castLT_eq_castLT_sub_of_le` / 定理 `sub_castLT_eq_castLT_sub_of_le`

English:
theorem sub_castLT_eq_castLT_sub_of_le
  given: {a b : Fin m} (ha : a.val < n) (h : b <= a)
  proof: by
  rw [Fin.ext_iff]
  exact val_sub_castLT_of_le ha h

中文:
定理 sub_castLT_eq_castLT_sub_of_le
  条件: {a b : 有限集 m} (ha : a.val < n) (h : b <= a)
  证明: by
  rw [Fin.ext_iff]
  exact val_sub_castLT_of_le ha h

Depends on / 依赖: Fin.ext_iff, ext_iff, val_sub_castLT_of_le
-/
theorem sub_castLT_eq_castLT_sub_of_le {a b : Fin m} (ha : a.val < n) (h : b <= a) :
    a.castLT ha - b.castLT (lt_of_le_of_lt h ha) =
      (a - b).castLT (val_sub_lt_of_lt_of_le ha h) := by
  rw [Fin.ext_iff]
  exact val_sub_castLT_of_le ha h

/--
theorem `val_sub_castLT_of_lt` / 定理 `val_sub_castLT_of_lt`

English:
theorem val_sub_castLT_of_lt
  given: {a b : Fin m} (hb : b < n) (h : a < b)
  proof: by
  simp only [val_sub, val_castLT]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  have h' : a.val < b.val := h
  omega

中文:
定理 val_sub_castLT_of_lt
  条件: {a b : 有限集 m} (hb : b < n) (h : a < b)
  证明: by
  simp only [val_sub, val_castLT]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  have h' : a.val < b.val := h
  omega

Depends on / 依赖: Nat.mod_eq_of_lt, a.val, b.val, mod_eq_of_lt, repeat, val_castLT, val_sub
-/
theorem val_sub_castLT_of_lt {a b : Fin m} (hb : b < n) (h : a < b) :
    (a.castLT (lt_trans h hb) - b.castLT hb).val = (a - b).val + n - m := by
  simp only [val_sub, val_castLT]
  repeat rw [Nat.mod_eq_of_lt (by omega)]
  have h' : a.val < b.val := h
  omega

/--
theorem `val_sub_castPred_of_le` / 定理 `val_sub_castPred_of_le`

English:
theorem val_sub_castPred_of_le
  statement: {a b : Fin (n + 1)} (ha : a != last n)
  proof: val_sub_castLT_of_le (lt_last_iff_ne_last.mpr ha) h

中文:
定理 val_sub_castPred_of_le
  结论: {a b : 有限集 (n + 1)} (ha : a != last n)
  证明: val_sub_castLT_of_le (lt_last_iff_ne_last.mpr ha) h

Depends on / 依赖: lt_last_iff_ne_last, lt_last_iff_ne_last.mpr, val_sub_castLT_of_le
-/
theorem val_sub_castPred_of_le {a b : Fin (n + 1)} (ha : a != last n)
    (h : b <= a) :
    (a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h)).val = (a - b).val :=
  val_sub_castLT_of_le (lt_last_iff_ne_last.mpr ha) h

/--
theorem `sub_castPred_eq_castPred_sub_of_le` / 定理 `sub_castPred_eq_castPred_sub_of_le`

English:
theorem sub_castPred_eq_castPred_sub_of_le
  statement: {a b : Fin (n + 1)} (ha : a != last n)
  proof: sub_castLT_eq_castLT_sub_of_le (lt_last_iff_ne_last.mpr ha) h

中文:
定理 sub_castPred_eq_castPred_sub_of_le
  结论: {a b : 有限集 (n + 1)} (ha : a != last n)
  证明: sub_castLT_eq_castLT_sub_of_le (lt_last_iff_ne_last.mpr ha) h

Depends on / 依赖: lt_last_iff_ne_last, lt_last_iff_ne_last.mpr, sub_castLT_eq_castLT_sub_of_le
-/
theorem sub_castPred_eq_castPred_sub_of_le {a b : Fin (n + 1)} (ha : a != last n)
    (h : b <= a) :
    a.castPred ha - b.castPred (ne_last_of_ne_last_of_le ha h) =
      (a - b).castPred (sub_ne_last_of_ne_last_of_le ha h) :=
  sub_castLT_eq_castLT_sub_of_le (lt_last_iff_ne_last.mpr ha) h

/--
theorem `val_sub_castPred_of_ge` / 定理 `val_sub_castPred_of_ge`

English:
theorem val_sub_castPred_of_ge
  statement: {a b : Fin (n + 1)} (hb : b != last n)
  proof: by
  obtain (rfl | h') := Fin.eq_or_lt_of_le h
  · simp [val_sub, Nat.sub_add_cancel a.is_le]
  grind [castPred, val_sub_castLT_of_lt]

中文:
定理 val_sub_castPred_of_ge
  结论: {a b : 有限集 (n + 1)} (hb : b != last n)
  证明: by
  obtain (rfl | h') := Fin.eq_or_lt_of_le h
  · simp [val_sub, Nat.sub_add_cancel a.is_le]
  grind [castPred, val_sub_castLT_of_lt]

Depends on / 依赖: Fin.eq_or_lt_of_le, Nat.sub_add_cancel, a.is_le, castPred, eq_or_lt_of_le, is_le, sub_add_cancel, val_sub, val_sub_castLT_of_lt
-/
theorem val_sub_castPred_of_ge {a b : Fin (n + 1)} (hb : b != last n)
    (h : a <= b) :
    (a.castPred (ne_last_of_ne_last_of_le hb h) - b.castPred hb).val = (a - b).val - 1 := by
  obtain (rfl | h') := Fin.eq_or_lt_of_le h
  · simp [val_sub, Nat.sub_add_cancel a.is_le]
  grind [castPred, val_sub_castLT_of_lt]

end CastPred

section SuccAbove
variable {p : Fin (n + 1)} {i j : Fin n}

/--
Definition of `succAbove` / `succAbove` 的定义

English:
definition succAbove
  signature: (p : Fin (n + 1)) (i : Fin n)
  body: if castSucc i < p then i.castSucc else i.succ

中文:
定义 succAbove
  签名: (p : 有限集 (n + 1)) (i : 有限集 n)
  定义体: if castSucc i < p then i.castSucc else i.succ

Depends on / 依赖: castSucc, i.castSucc, i.succ
-/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

/--
lemma `succAbove_of_castSucc_lt` / 引理 `succAbove_of_castSucc_lt`

English:
lemma succAbove_of_castSucc_lt
  given: (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p)
  proof: if_pos h

中文:
引理 succAbove_of_castSucc_lt
  条件: (p : 有限集 (n + 1)) (i : 有限集 n) (h : castSucc i < p)
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h

/--
lemma `succAbove_of_succ_le` / 引理 `succAbove_of_succ_le`

English:
lemma succAbove_of_succ_le
  given: (p : Fin (n + 1)) (i : Fin n) (h : succ i <= p)
  proof: succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

中文:
引理 succAbove_of_succ_le
  条件: (p : 有限集 (n + 1)) (i : 有限集 n) (h : succ i <= p)
  证明: succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

Depends on / 依赖: castSucc_lt_iff_succ_le, castSucc_lt_iff_succ_le.mpr, succAbove_of_castSucc_lt
-/
lemma succAbove_of_succ_le (p : Fin (n + 1)) (i : Fin n) (h : succ i <= p) :
    p.succAbove i = castSucc i :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

/--
lemma `succAbove_of_le_castSucc` / 引理 `succAbove_of_le_castSucc`

English:
lemma succAbove_of_le_castSucc
  given: (p : Fin (n + 1)) (i : Fin n) (h : p <= castSucc i)
  proof: if_neg (Fin.not_lt.2 h)

中文:
引理 succAbove_of_le_castSucc
  条件: (p : 有限集 (n + 1)) (i : 有限集 n) (h : p <= castSucc i)
  证明: if_neg (Fin.not_lt.2 h)

Depends on / 依赖: Fin.not_lt, if_neg, not_lt
-/
lemma succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p <= castSucc i) :
    p.succAbove i = i.succ := if_neg (Fin.not_lt.2 h)

/--
lemma `succAbove_of_lt_succ` / 引理 `succAbove_of_lt_succ`

English:
lemma succAbove_of_lt_succ
  given: (p : Fin (n + 1)) (i : Fin n) (h : p < succ i)
  proof: succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

中文:
引理 succAbove_of_lt_succ
  条件: (p : 有限集 (n + 1)) (i : 有限集 n) (h : p < succ i)
  证明: succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

Depends on / 依赖: le_castSucc_iff, le_castSucc_iff.mpr, succAbove_of_le_castSucc
-/
lemma succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fin n) (h : p < succ i) :
    p.succAbove i = succ i := succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

/--
lemma `succAbove_succ_of_lt` / 引理 `succAbove_succ_of_lt`

English:
lemma succAbove_succ_of_lt
  given: (p i : Fin n) (h : p < i)
  statement: succAbove p.succ i = i.succ
  proof: succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)

中文:
引理 succAbove_succ_of_lt
  条件: (p i : 有限集 n) (h : p < i)
  结论: succAbove p.succ i = i.succ
  证明: succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)

Depends on / 依赖: succAbove_of_lt_succ, succ_lt_succ_iff, succ_lt_succ_iff.mpr
-/
lemma succAbove_succ_of_lt (p i : Fin n) (h : p < i) : succAbove p.succ i = i.succ :=
  succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)

/--
lemma `succAbove_succ_of_le` / 引理 `succAbove_succ_of_le`

English:
lemma succAbove_succ_of_le
  given: (p i : Fin n) (h : i <= p)
  statement: succAbove p.succ i = i.castSucc
  proof: succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)

中文:
引理 succAbove_succ_of_le
  条件: (p i : 有限集 n) (h : i <= p)
  结论: succAbove p.succ i = i.castSucc
  证明: succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)

Depends on / 依赖: succAbove_of_succ_le, succ_le_succ_iff, succ_le_succ_iff.mpr
-/
lemma succAbove_succ_of_le (p i : Fin n) (h : i <= p) : succAbove p.succ i = i.castSucc :=
  succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)

/--
lemma `succAbove_succ_self` / 引理 `succAbove_succ_self`

English:
lemma succAbove_succ_self
  given: (j : Fin n)
  statement: j.succ.succAbove j = j.castSucc
  proof: succAbove_succ_of_le _ _ Fin.le_rfl

中文:
引理 succAbove_succ_self
  条件: (j : 有限集 n)
  结论: j.succ.succAbove j = j.castSucc
  证明: succAbove_succ_of_le _ _ Fin.le_rfl
-/
@[simp] lemma succAbove_succ_self (j : Fin n) : j.succ.succAbove j = j.castSucc :=
  succAbove_succ_of_le _ _ Fin.le_rfl

/--
lemma `succAbove_castSucc_of_lt` / 引理 `succAbove_castSucc_of_lt`

English:
lemma succAbove_castSucc_of_lt
  given: (p i : Fin n) (h : i < p)
  statement: succAbove p.castSucc i = i.castSucc
  proof: succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)

中文:
引理 succAbove_castSucc_of_lt
  条件: (p i : 有限集 n) (h : i < p)
  结论: succAbove p.castSucc i = i.castSucc
  证明: succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)

Depends on / 依赖: castSucc_lt_castSucc_iff, succAbove_of_castSucc_lt
-/
lemma succAbove_castSucc_of_lt (p i : Fin n) (h : i < p) : succAbove p.castSucc i = i.castSucc :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)

/--
lemma `succAbove_castSucc_of_le` / 引理 `succAbove_castSucc_of_le`

English:
lemma succAbove_castSucc_of_le
  given: (p i : Fin n) (h : p <= i)
  statement: succAbove p.castSucc i = i.succ
  proof: succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.2 h)

中文:
引理 succAbove_castSucc_of_le
  条件: (p i : 有限集 n) (h : p <= i)
  结论: succAbove p.castSucc i = i.succ
  证明: succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.2 h)

Depends on / 依赖: castSucc_le_castSucc_iff, succAbove_of_le_castSucc
-/
lemma succAbove_castSucc_of_le (p i : Fin n) (h : p <= i) : succAbove p.castSucc i = i.succ :=
  succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.2 h)

/--
lemma `succAbove_castSucc_self` / 引理 `succAbove_castSucc_self`

English:
lemma succAbove_castSucc_self
  given: (j : Fin n)
  statement: succAbove j.castSucc j = j.succ
  proof: succAbove_castSucc_of_le _ _ Fin.le_rfl

中文:
引理 succAbove_castSucc_self
  条件: (j : 有限集 n)
  结论: succAbove j.castSucc j = j.succ
  证明: succAbove_castSucc_of_le _ _ Fin.le_rfl
-/
@[simp] lemma succAbove_castSucc_self (j : Fin n) : succAbove j.castSucc j = j.succ :=
  succAbove_castSucc_of_le _ _ Fin.le_rfl

/--
lemma `succAbove_pred_of_lt` / 引理 `succAbove_pred_of_lt`

English:
lemma succAbove_pred_of_lt
  given: (p i : Fin (n + 1)) (h : p < i)
  proof: by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]; rw [succ_pred]

中文:
引理 succAbove_pred_of_lt
  条件: (p i : 有限集 (n + 1)) (h : p < i)
  证明: by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]; rw [succ_pred]

Depends on / 依赖: succAbove_of_lt_succ, succ_pred
-/
lemma succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) = i := by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]; rw [succ_pred]

/--
lemma `succAbove_pred_of_le` / 引理 `succAbove_pred_of_le`

English:
lemma succAbove_pred_of_le
  given: (p i : Fin (n + 1)) (h : i <= p) (hi : i != 0)
  proof: succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)

中文:
引理 succAbove_pred_of_le
  条件: (p i : 有限集 (n + 1)) (h : i <= p) (hi : i != 0)
  证明: succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)

Depends on / 依赖: succAbove_of_succ_le, succ_pred
-/
lemma succAbove_pred_of_le (p i : Fin (n + 1)) (h : i <= p) (hi : i != 0) :
    succAbove p (i.pred hi) = (i.pred hi).castSucc := succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)

/--
lemma `succAbove_pred_self` / 引理 `succAbove_pred_self`

English:
lemma succAbove_pred_self
  given: (p : Fin (n + 1)) (h : p != 0)
  proof: succAbove_pred_of_le _ _ Fin.le_rfl h

中文:
引理 succAbove_pred_self
  条件: (p : 有限集 (n + 1)) (h : p != 0)
  证明: succAbove_pred_of_le _ _ Fin.le_rfl h
-/
@[simp] lemma succAbove_pred_self (p : Fin (n + 1)) (h : p != 0) :
    succAbove p (p.pred h) = (p.pred h).castSucc := succAbove_pred_of_le _ _ Fin.le_rfl h

/--
lemma `succAbove_castPred_of_lt` / 引理 `succAbove_castPred_of_lt`

English:
lemma succAbove_castPred_of_lt
  given: (p i : Fin (n + 1)) (h : i < p)
  proof: by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]; rw [castSucc_castPred]

中文:
引理 succAbove_castPred_of_lt
  条件: (p i : 有限集 (n + 1)) (h : i < p)
  证明: by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]; rw [castSucc_castPred]

Depends on / 依赖: castSucc_castPred, succAbove_of_castSucc_lt
-/
lemma succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p.le_last)) = i := by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]; rw [castSucc_castPred]

/--
lemma `succAbove_castPred_of_le` / 引理 `succAbove_castPred_of_le`

English:
lemma succAbove_castPred_of_le
  given: (p i : Fin (n + 1)) (h : p <= i) (hi : i != last n)
  proof: succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)

中文:
引理 succAbove_castPred_of_le
  条件: (p i : 有限集 (n + 1)) (h : p <= i) (hi : i != last n)
  证明: succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)

Depends on / 依赖: castSucc_castPred, succAbove_of_le_castSucc
-/
lemma succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p <= i) (hi : i != last n) :
    succAbove p (i.castPred hi) = (i.castPred hi).succ :=
  succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)

/--
lemma `succAbove_castPred_self` / 引理 `succAbove_castPred_self`

English:
lemma succAbove_castPred_self
  given: (p : Fin (n + 1)) (h : p != last n)
  proof: succAbove_castPred_of_le _ _ Fin.le_rfl h

中文:
引理 succAbove_castPred_self
  条件: (p : 有限集 (n + 1)) (h : p != last n)
  证明: succAbove_castPred_of_le _ _ Fin.le_rfl h

Depends on / 依赖: Fin.le_rfl, le_rfl, succAbove_castPred_of_le
-/
lemma succAbove_castPred_self (p : Fin (n + 1)) (h : p != last n) :
    succAbove p (p.castPred h) = (p.castPred h).succ := succAbove_castPred_of_le _ _ Fin.le_rfl h

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
@[simp]
/--
lemma `succAbove_ne` / 引理 `succAbove_ne`

English:
lemma succAbove_ne
  given: (p : Fin (n + 1)) (i : Fin n)
  statement: p.succAbove i != p
  proof: by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

@[simp]

中文:
引理 succAbove_ne
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  结论: p.succAbove i != p
  证明: by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

@[simp]

Depends on / 依赖: Fin.ne_of_gt, Fin.ne_of_lt, castSucc_lt_or_lt_succ, ne_of_gt, ne_of_lt, p.castSucc_lt_or_lt_succ, succAbove_of_castSucc_lt, succAbove_of_lt_succ
-/
lemma succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i != p := by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

@[simp]
/--
lemma `ne_succAbove` / 引理 `ne_succAbove`

English:
lemma ne_succAbove
  given: (p : Fin (n + 1)) (i : Fin n)
  statement: p != p.succAbove i
  proof: (succAbove_ne _ _).symm

中文:
引理 ne_succAbove
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  结论: p != p.succAbove i
  证明: (succAbove_ne _ _).symm

Depends on / 依赖: succAbove_ne
-/
lemma ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p != p.succAbove i := (succAbove_ne _ _).symm

/--
lemma `succAbove_right_injective` / 引理 `succAbove_right_injective`

English:
lemma succAbove_right_injective
  statement: Injective p.succAbove
  proof: by
  rintro i j hij
  unfold succAbove at hij
  split_ifs at hij with hi hj hj
  · exact castSucc_injective _ hij
  · rw [hij] at hi
cases hj Nat.lt_trans j.castSucc_lt_succ hi
  · rw [← hij] at hj
cases hi Nat.lt_trans i.castSucc_lt_succ hj
  · exact succ_injective _ hij

中文:
引理 succAbove_right_injective
  结论: 单射 p.succAbove
  证明: by
  rintro i j hij
  unfold succAbove at hij
  split_ifs at hij with hi hj hj
  · exact castSucc_injective _ hij
  · rw [hij] at hi
cases hj Nat.lt_trans j.castSucc_lt_succ hi
  · rw [← hij] at hj
cases hi Nat.lt_trans i.castSucc_lt_succ hj
  · exact succ_injective _ hij

Depends on / 依赖: Nat.lt_trans, castSucc_injective, castSucc_lt_succ, i.castSucc_lt_succ, j.castSucc_lt_succ, lt_trans, split_ifs, succAbove, succ_injective
-/
lemma succAbove_right_injective : Injective p.succAbove := by
  rintro i j hij
  unfold succAbove at hij
  split_ifs at hij with hi hj hj
  · exact castSucc_injective _ hij
  · rw [hij] at hi
cases hj Nat.lt_trans j.castSucc_lt_succ hi
  · rw [← hij] at hj
cases hi Nat.lt_trans i.castSucc_lt_succ hj
  · exact succ_injective _ hij

/--
lemma `succAbove_right_inj` / 引理 `succAbove_right_inj`

English:
lemma succAbove_right_inj
  statement: p.succAbove i = p.succAbove j ↔ i = j
  proof: succAbove_right_injective.eq_iff

@[simp]

中文:
引理 succAbove_right_inj
  结论: p.succAbove i = p.succAbove j ↔ i = j
  证明: succAbove_right_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, succAbove_right_injective, succAbove_right_injective.eq_iff
-/
lemma succAbove_right_inj : p.succAbove i = p.succAbove j ↔ i = j :=
  succAbove_right_injective.eq_iff

@[simp]
/--
lemma `succAbove_ne_zero_zero` / 引理 `succAbove_ne_zero_zero`

English:
lemma succAbove_ne_zero_zero
  given: [NeZero n] {a : Fin (n + 1)} (ha : a != 0)
  statement: a.succAbove 0 = 0
  proof: by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact Fin.pos_iff_ne_zero.2 ha

中文:
引理 succAbove_ne_zero_zero
  条件: [NeZero n] {a : 有限集 (n + 1)} (ha : a != 0)
  结论: a.succAbove 0 = 0
  证明: by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact Fin.pos_iff_ne_zero.2 ha

Depends on / 依赖: Fin.pos_iff_ne_zero, Fin.succAbove_of_castSucc_lt, castSucc_zero, pos_iff_ne_zero, succAbove_of_castSucc_lt
-/
lemma succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a != 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact Fin.pos_iff_ne_zero.2 ha

/--
lemma `succAbove_eq_zero_iff` / 引理 `succAbove_eq_zero_iff`

English:
lemma succAbove_eq_zero_iff
  given: [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 0)
  proof: by
  rw [← succAbove_ne_zero_zero ha]; rw [succAbove_right_inj]

中文:
引理 succAbove_eq_zero_iff
  条件: [NeZero n] {a : 有限集 (n + 1)} {b : 有限集 n} (ha : a != 0)
  证明: by
  rw [← succAbove_ne_zero_zero ha]; rw [succAbove_right_inj]

Depends on / 依赖: succAbove_ne_zero_zero, succAbove_right_inj
-/
lemma succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  rw [← succAbove_ne_zero_zero ha]; rw [succAbove_right_inj]

/--
lemma `succAbove_ne_zero` / 引理 `succAbove_ne_zero`

English:
lemma succAbove_ne_zero
  given: [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 0) (hb : b != 0)
  proof: mt (succAbove_eq_zero_iff ha).mp hb

中文:
引理 succAbove_ne_zero
  条件: [NeZero n] {a : 有限集 (n + 1)} {b : 有限集 n} (ha : a != 0) (hb : b != 0)
  证明: mt (succAbove_eq_zero_iff ha).mp hb

Depends on / 依赖: succAbove_eq_zero_iff
-/
lemma succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a != 0) (hb : b != 0) :
    a.succAbove b != 0 := mt (succAbove_eq_zero_iff ha).mp hb

/--
lemma `succAbove_zero` / 引理 `succAbove_zero`

English:
lemma succAbove_zero
  statement: succAbove (0 : Fin (n + 1)) = Fin.succ
  proof: rfl

中文:
引理 succAbove_zero
  结论: succAbove (0 : 有限集 (n + 1)) = 有限集.succ
  证明: rfl
-/
@[simp] lemma succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ := rfl

/--
lemma `succAbove_zero_apply` / 引理 `succAbove_zero_apply`

English:
lemma succAbove_zero_apply
  given: (i : Fin n)
  statement: succAbove 0 i = succ i
  proof: by rw [succAbove_zero]

中文:
引理 succAbove_zero_apply
  条件: (i : 有限集 n)
  结论: succAbove 0 i = succ i
  证明: by rw [succAbove_zero]

Depends on / 依赖: _right, fold_cons, hc.comm, succAbove_zero
-/
lemma succAbove_zero_apply (i : Fin n) : succAbove 0 i = succ i := by rw [succAbove_zero]

/--
lemma `succAbove_ne_last_last` / 引理 `succAbove_ne_last_last`

English:
lemma succAbove_ne_last_last
  given: {a : Fin (n + 2)} (h : a != last (n + 1))
  proof: by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_last_iff_ne_last.2 h)]; rw [succ_last]

中文:
引理 succAbove_ne_last_last
  条件: {a : 有限集 (n + 2)} (h : a != last (n + 1))
  证明: by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_last_iff_ne_last.2 h)]; rw [succ_last]
-/
@[simp] lemma succAbove_ne_last_last {a : Fin (n + 2)} (h : a != last (n + 1)) :
    a.succAbove (last n) = last (n + 1) := by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_last_iff_ne_last.2 h)]; rw [succ_last]

/--
lemma `succAbove_eq_last_iff` / 引理 `succAbove_eq_last_iff`

English:
lemma succAbove_eq_last_iff
  given: {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last _)
  proof: by
  rw [← succAbove_ne_last_last ha]; rw [succAbove_right_inj]

中文:
引理 succAbove_eq_last_iff
  条件: {a : 有限集 (n + 2)} {b : 有限集 (n + 1)} (ha : a != last _)
  证明: by
  rw [← succAbove_ne_last_last ha]; rw [succAbove_right_inj]

Depends on / 依赖: succAbove_ne_last_last, succAbove_right_inj
-/
lemma succAbove_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last _) :
    a.succAbove b = last _ ↔ b = last _ := by
  rw [← succAbove_ne_last_last ha]; rw [succAbove_right_inj]

/--
lemma `succAbove_ne_last` / 引理 `succAbove_ne_last`

English:
lemma succAbove_ne_last
  given: {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last _) (hb : b != last _)
  proof: mt (succAbove_eq_last_iff ha).mp hb

中文:
引理 succAbove_ne_last
  条件: {a : 有限集 (n + 2)} {b : 有限集 (n + 1)} (ha : a != last _) (hb : b != last _)
  证明: mt (succAbove_eq_last_iff ha).mp hb

Depends on / 依赖: succAbove_eq_last_iff
-/
lemma succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last _) (hb : b != last _) :
    a.succAbove b != last _ := mt (succAbove_eq_last_iff ha).mp hb

/--
lemma `succAbove_last` / 引理 `succAbove_last`

English:
lemma succAbove_last
  statement: succAbove (last n) = castSucc
  proof: by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]

中文:
引理 succAbove_last
  结论: succAbove (last n) = castSucc
  证明: by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]
-/
@[simp] lemma succAbove_last : succAbove (last n) = castSucc := by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]

/--
lemma `succAbove_last_apply` / 引理 `succAbove_last_apply`

English:
lemma succAbove_last_apply
  given: (i : Fin n)
  statement: succAbove (last n) i = castSucc i
  proof: by rw [succAbove_last]

中文:
引理 succAbove_last_apply
  条件: (i : 有限集 n)
  结论: succAbove (last n) i = castSucc i
  证明: by rw [succAbove_last]

Depends on / 依赖: succAbove_last
-/
lemma succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i := by rw [succAbove_last]

/--
lemma `succAbove_lt_iff_castSucc_lt` / 引理 `succAbove_lt_iff_castSucc_lt`

English:
lemma succAbove_lt_iff_castSucc_lt
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right (Fin.not_le.2 H), succAbove_of_lt_succ _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H

中文:
引理 succAbove_lt_iff_castSucc_lt
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  证明: by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right (Fin.not_le.2 H), succAbove_of_lt_succ _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H

Depends on / 依赖: Fin.le_of_lt, Fin.not_le, Fin.not_lt, castSucc_lt_iff_succ_le, castSucc_lt_or_lt_succ, iff_false_right, iff_true_right, le_of_lt, not_le, not_lt, succAbove_of_castSucc_lt, succAbove_of_lt_succ
-/
lemma succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right (Fin.not_le.2 H), succAbove_of_lt_succ _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H

/--
lemma `succAbove_lt_iff_succ_le` / 引理 `succAbove_lt_iff_succ_le`

English:
lemma succAbove_lt_iff_succ_le
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by
  rw [succAbove_lt_iff_castSucc_lt]; rw [castSucc_lt_iff_succ_le]

中文:
引理 succAbove_lt_iff_succ_le
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  证明: by
  rw [succAbove_lt_iff_castSucc_lt]; rw [castSucc_lt_iff_succ_le]

Depends on / 依赖: castSucc_lt_iff_succ_le, succAbove_lt_iff_castSucc_lt
-/
lemma succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ succ i <= p := by
  rw [succAbove_lt_iff_castSucc_lt]; rw [castSucc_lt_iff_succ_le]

/--
lemma `lt_succAbove_iff_le_castSucc` / 引理 `lt_succAbove_iff_le_castSucc`

English:
lemma lt_succAbove_iff_le_castSucc
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rw [iff_false_right (Fin.not_le.2 H), succAbove_of_castSucc_lt _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]

中文:
引理 lt_succAbove_iff_le_castSucc
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  证明: by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rw [iff_false_right (Fin.not_le.2 H), succAbove_of_castSucc_lt _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]

Depends on / 依赖: Fin.le_of_lt, Fin.not_le, Fin.not_lt, castSucc_lt_or_lt_succ, iff_false_right, iff_true_left, le_castSucc_iff, le_of_lt, not_le, not_lt, succAbove_of_castSucc_lt, succAbove_of_lt_succ
-/
lemma lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p <= castSucc i := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rw [iff_false_right (Fin.not_le.2 H), succAbove_of_castSucc_lt _ _ H]
exact Fin.not_lt.2 Fin.le_of_lt H
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]

/--
lemma `lt_succAbove_iff_lt_castSucc` / 引理 `lt_succAbove_iff_lt_castSucc`

English:
lemma lt_succAbove_iff_lt_castSucc
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: by rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

中文:
引理 lt_succAbove_iff_lt_castSucc
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  证明: by rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

Depends on / 依赖: le_castSucc_iff, lt_succAbove_iff_le_castSucc
-/
lemma lt_succAbove_iff_lt_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p < succ i := by rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

/--
lemma `succAbove_pos` / 引理 `succAbove_pos`

English:
lemma succAbove_pos
  given: [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i)
  statement: 0 < p.succAbove i
  proof: by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 H)]

中文:
引理 succAbove_pos
  条件: [NeZero n] (p : 有限集 (n + 1)) (i : 有限集 n) (h : 0 < i)
  结论: 0 < p.succAbove i
  证明: by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 H)]

Depends on / 依赖: Fin.not_lt, castSucc, castSucc_pos, not_lt, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
lemma succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 H)]

/--
lemma `castPred_succAbove` / 引理 `castPred_succAbove`

English:
lemma castPred_succAbove
  statement: (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y)
  proof: by
  rw [castPred_eq_iff_eq_castSucc]; rw [succAbove_of_castSucc_lt _ _ h]

中文:
引理 castPred_succAbove
  结论: (x : 有限集 n) (y : 有限集 (n + 1)) (h : castSucc x < y)
  证明: by
  rw [castPred_eq_iff_eq_castSucc]; rw [succAbove_of_castSucc_lt _ _ h]

Depends on / 依赖: Fin.ne_last_of_lt, ne_last_of_lt, succAbove_lt_iff_castSucc_lt
-/
lemma castPred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y)
    (h' := Fin.ne_last_of_lt <| (succAbove_lt_iff_castSucc_lt ..).2 h) :
    (y.succAbove x).castPred h' = x := by
  rw [castPred_eq_iff_eq_castSucc]; rw [succAbove_of_castSucc_lt _ _ h]

/--
lemma `pred_succAbove` / 引理 `pred_succAbove`

English:
lemma pred_succAbove
  statement: (x : Fin n) (y : Fin (n + 1)) (h : y <= castSucc x)
  proof: by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]

中文:
引理 pred_succAbove
  结论: (x : 有限集 n) (y : 有限集 (n + 1)) (h : y <= castSucc x)
  证明: by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]

Depends on / 依赖: Fin.ne_zero_of_lt, lt_succAbove_iff_le_castSucc, ne_zero_of_lt
-/
lemma pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y <= castSucc x)
    (h' := Fin.ne_zero_of_lt <| (lt_succAbove_iff_le_castSucc ..).2 h) :
    (y.succAbove x).pred h' = x := by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]

/--
lemma `exists_succAbove_eq` / 引理 `exists_succAbove_eq`

English:
lemma exists_succAbove_eq
  given: {x y : Fin (n + 1)} (h : x != y)
  statement: exists z, y.succAbove z = x
  proof: by
  obtain hxy | hyx := Fin.lt_or_lt_of_ne h
  exacts [⟨_, succAbove_castPred_of_lt _ _ hxy⟩, ⟨_, succAbove_pred_of_lt _ _ hyx⟩]

中文:
引理 存在_succAbove_eq
  条件: {x y : 有限集 (n + 1)} (h : x != y)
  结论: 存在 z, y.succAbove z = x
  证明: by
  obtain hxy | hyx := Fin.lt_or_lt_of_ne h
  exacts [⟨_, succAbove_castPred_of_lt _ _ hxy⟩, ⟨_, succAbove_pred_of_lt _ _ hyx⟩]

Depends on / 依赖: Fin.lt_or_lt_of_ne, exacts, lt_or_lt_of_ne, succAbove_castPred_of_lt, succAbove_pred_of_lt
-/
lemma exists_succAbove_eq {x y : Fin (n + 1)} (h : x != y) : exists z, y.succAbove z = x := by
  obtain hxy | hyx := Fin.lt_or_lt_of_ne h
  exacts [⟨_, succAbove_castPred_of_lt _ _ hxy⟩, ⟨_, succAbove_pred_of_lt _ _ hyx⟩]

/--
lemma `exists_succAbove_eq_iff` / 引理 `exists_succAbove_eq_iff`

English:
lemma exists_succAbove_eq_iff
  given: {x y : Fin (n + 1)}
  statement: (exists z, x.succAbove z = y) ↔ y != x
  proof: ⟨by rintro ⟨y, rfl⟩; exact succAbove_ne _ _, exists_succAbove_eq⟩

中文:
引理 存在_succAbove_eq_iff
  条件: {x y : 有限集 (n + 1)}
  结论: (存在 z, x.succAbove z = y) ↔ y != x
  证明: ⟨by rintro ⟨y, rfl⟩; exact succAbove_ne _ _, exists_succAbove_eq⟩
-/
@[simp] lemma exists_succAbove_eq_iff {x y : Fin (n + 1)} : (exists z, x.succAbove z = y) ↔ y != x :=
  ⟨by rintro ⟨y, rfl⟩; exact succAbove_ne _ _, exists_succAbove_eq⟩

/--
lemma `range_succAbove` / 引理 `range_succAbove`

English:
lemma range_succAbove
  given: (p : Fin (n + 1))
  statement: Set.range p.succAbove = {p}ᶜ
  proof: Set.ext fun _ => exists_succAbove_eq_iff

中文:
引理 range_succAbove
  条件: (p : 有限集 (n + 1))
  结论: 集合.range p.succAbove = {p}ᶜ
  证明: Set.ext fun _ => exists_succAbove_eq_iff
-/
@[simp] lemma range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff

/--
lemma `range_succ` / 引理 `range_succ`

English:
lemma range_succ
  given: (n : Nat)
  statement: Set.range (Fin.succ : Fin n -> Fin (n + 1)) = {0}ᶜ
  proof: by
  rw [← succAbove_zero]; rw [range_succAbove]

中文:
引理 range_succ
  条件: (n : 自然数)
  结论: 集合.range (有限集.succ : 有限集 n -> 有限集 (n + 1)) = {0}ᶜ
  证明: by
  rw [← succAbove_zero]; rw [range_succAbove]
-/
@[simp] lemma range_succ (n : Nat) : Set.range (Fin.succ : Fin n -> Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]; rw [range_succAbove]

/--
lemma `succAbove_left_injective` / 引理 `succAbove_left_injective`

English:
lemma succAbove_left_injective
  statement: Injective (@succAbove n)
  proof: fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n -> Fin (n + 1) => (Set.range f)ᶜ) h

中文:
引理 succAbove_left_injective
  结论: 单射 (@succAbove n)
  证明: fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n -> Fin (n + 1) => (Set.range f)ᶜ) h

Depends on / 依赖: Set.range, congr_arg, range_succAbove
-/
lemma succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n -> Fin (n + 1) => (Set.range f)ᶜ) h

/--
lemma `succAbove_left_inj` / 引理 `succAbove_left_inj`

English:
lemma succAbove_left_inj
  given: {x y : Fin (n + 1)}
  statement: x.succAbove = y.succAbove ↔ x = y
  proof: succAbove_left_injective.eq_iff

中文:
引理 succAbove_left_inj
  条件: {x y : 有限集 (n + 1)}
  结论: x.succAbove = y.succAbove ↔ x = y
  证明: succAbove_left_injective.eq_iff
-/
@[simp] lemma succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff

/--
lemma `zero_succAbove` / 引理 `zero_succAbove`

English:
lemma zero_succAbove
  given: {n : Nat} (i : Fin n)
  statement: (0 : Fin (n + 1)).succAbove i = i.succ
  proof: rfl

中文:
引理 zero_succAbove
  条件: {n : 自然数} (i : 有限集 n)
  结论: (0 : 有限集 (n + 1)).succAbove i = i.succ
  证明: rfl
-/
@[simp] lemma zero_succAbove {n : Nat} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := rfl

/--
lemma `succ_succAbove_zero` / 引理 `succ_succAbove_zero`

English:
lemma succ_succAbove_zero
  given: {n : Nat} [NeZero n] (i : Fin n)
  statement: succAbove i.succ 0 = 0
  proof: by simp

中文:
引理 succ_succAbove_zero
  条件: {n : 自然数} [NeZero n] (i : 有限集 n)
  结论: succAbove i.succ 0 = 0
  证明: by simp
-/
lemma succ_succAbove_zero {n : Nat} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 := by simp

/--
lemma `succ_succAbove_succ` / 引理 `succ_succAbove_succ`

English:
lemma succ_succAbove_succ
  given: {n : Nat} (i : Fin (n + 1)) (j : Fin n)
  proof: by
  obtain h | h := i.lt_or_ge (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]

中文:
引理 succ_succAbove_succ
  条件: {n : 自然数} (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: by
  obtain h | h := i.lt_or_ge (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]
-/
@[simp] lemma succ_succAbove_succ {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ := by
  obtain h | h := i.lt_or_ge (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
/--
lemma `castSucc_succAbove_castSucc` / 引理 `castSucc_succAbove_castSucc`

English:
lemma castSucc_succAbove_castSucc
  given: {n : Nat} {i : Fin (n + 1)} {j : Fin n}
  proof: by
  rcases i.le_or_gt (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

中文:
引理 castSucc_succAbove_castSucc
  条件: {n : 自然数} {i : 有限集 (n + 1)} {j : 有限集 n}
  证明: by
  rcases i.le_or_gt (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

Depends on / 依赖: castSucc, i.le_or_gt, le_or_gt, succAbove_castSucc_of_le, succAbove_castSucc_of_lt, succAbove_of_castSucc_lt, succAbove_of_le_castSucc, succ_castSucc
-/
lemma castSucc_succAbove_castSucc {n : Nat} {i : Fin (n + 1)} {j : Fin n} :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases i.le_or_gt (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

/--
lemma `pred_succAbove_pred` / 引理 `pred_succAbove_pred`

English:
lemma pred_succAbove_pred
  statement: {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != 0) (hb : b != 0)
  proof: by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]

中文:
引理 pred_succAbove_pred
  结论: {a : 有限集 (n + 2)} {b : 有限集 (n + 1)} (ha : a != 0) (hb : b != 0)
  证明: by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]

Depends on / 依赖: succAbove_ne_zero
-/
lemma pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != 0) (hb : b != 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]

/--
lemma `castPred_succAbove_castPred` / 引理 `castPred_succAbove_castPred`

English:
lemma castPred_succAbove_castPred
  statement: {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last (n + 1))
  proof: by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]

中文:
引理 castPred_succAbove_castPred
  结论: {a : 有限集 (n + 2)} {b : 有限集 (n + 1)} (ha : a != last (n + 1))
  证明: by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]

Depends on / 依赖: succAbove_ne_last
-/
lemma castPred_succAbove_castPred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a != last (n + 1))
    (hb : b != last n) (hk := succAbove_ne_last ha hb) :
    (a.castPred ha).succAbove (b.castPred hb) = (a.succAbove b).castPred hk := by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]

/--
lemma `one_succAbove_zero` / 引理 `one_succAbove_zero`

English:
lemma one_succAbove_zero
  given: {n : Nat}
  statement: (1 : Fin (n + 2)).succAbove 0 = 0
  proof: rfl

中文:
引理 one_succAbove_zero
  条件: {n : 自然数}
  结论: (1 : 有限集 (n + 2)).succAbove 0 = 0
  证明: rfl
-/
lemma one_succAbove_zero {n : Nat} : (1 : Fin (n + 2)).succAbove 0 = 0 := rfl

/--
lemma `succ_succAbove_one` / 引理 `succ_succAbove_one`

English:
lemma succ_succAbove_one
  given: {n : Nat} [NeZero n] (i : Fin (n + 1))
  proof: by
  rw [← succ_zero_eq_one']
  exact succ_succAbove_succ i 0

中文:
引理 succ_succAbove_one
  条件: {n : 自然数} [NeZero n] (i : 有限集 (n + 1))
  证明: by
  rw [← succ_zero_eq_one']
  exact succ_succAbove_succ i 0
-/
@[simp] lemma succ_succAbove_one {n : Nat} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one']
  exact succ_succAbove_succ i 0

/--
lemma `one_succAbove_succ` / 引理 `one_succAbove_succ`

English:
lemma one_succAbove_succ
  given: {n : Nat} (j : Fin n)
  proof: by
  have := succ_succAbove_succ 0 j; rwa [succ_zero_eq_one, zero_succAbove] at this

中文:
引理 one_succAbove_succ
  条件: {n : 自然数} (j : 有限集 n)
  证明: by
  have := succ_succAbove_succ 0 j; rwa [succ_zero_eq_one, zero_succAbove] at this
-/
@[simp] lemma one_succAbove_succ {n : Nat} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j; rwa [succ_zero_eq_one, zero_succAbove] at this

/--
lemma `one_succAbove_one` / 引理 `one_succAbove_one`

English:
lemma one_succAbove_one
  given: {n : Nat}
  statement: (1 : Fin (n + 3)).succAbove 1 = 2
  proof: by
  simpa only [succ_zero_eq_one, val_zero, zero_succAbove, succ_one_eq_two]
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 1))

中文:
引理 one_succAbove_one
  条件: {n : 自然数}
  结论: (1 : 有限集 (n + 3)).succAbove 1 = 2
  证明: by
  simpa only [succ_zero_eq_one, val_zero, zero_succAbove, succ_one_eq_two]
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 1))
-/
@[simp] lemma one_succAbove_one {n : Nat} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  simpa only [succ_zero_eq_one, val_zero, zero_succAbove, succ_one_eq_two]
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 1))

end SuccAbove

section PredAbove

/--
Definition of `predAbove` / `predAbove` 的定义

English:
definition predAbove
  signature: (p : Fin n) (i : Fin (n + 1))
  body: if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))

中文:
定义 predAbove
  签名: (p : 有限集 n) (i : 有限集 (n + 1))
  定义体: if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))

Depends on / 依赖: Fin.lt_of_le_of_lt, Fin.ne_of_lt, Fin.ne_zero_of_lt, Fin.not_lt, castPred, castSucc, castSucc_lt_last, lt_of_le_of_lt, ne_of_lt, ne_zero_of_lt, not_lt
-/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))

/--
lemma `predAbove_of_le_castSucc` / 引理 `predAbove_of_le_castSucc`

English:
lemma predAbove_of_le_castSucc
  given: (p : Fin n) (i : Fin (n + 1)) (h : i <= castSucc p)
  proof: dif_neg Fin.not_lt.2 h

中文:
引理 predAbove_of_le_castSucc
  条件: (p : 有限集 n) (i : 有限集 (n + 1)) (h : i <= castSucc p)
  证明: dif_neg Fin.not_lt.2 h

Depends on / 依赖: Fin.not_lt, dif_neg, not_lt
-/
lemma predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i <= castSucc p) :
    p.predAbove i = i.castPred (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| castSucc_lt_last _) :=
dif_neg Fin.not_lt.2 h

/--
lemma `predAbove_of_lt_succ` / 引理 `predAbove_of_lt_succ`

English:
lemma predAbove_of_lt_succ
  given: (p : Fin n) (i : Fin (n + 1)) (h : i < succ p)
  proof: predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

中文:
引理 predAbove_of_lt_succ
  条件: (p : 有限集 n) (i : 有限集 (n + 1)) (h : i < succ p)
  证明: predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

Depends on / 依赖: le_castSucc_iff, le_castSucc_iff.mpr, predAbove_of_le_castSucc
-/
lemma predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p) :
    p.predAbove i = i.castPred (Fin.ne_last_of_lt h) :=
  predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

/--
lemma `predAbove_of_castSucc_lt` / 引理 `predAbove_of_castSucc_lt`

English:
lemma predAbove_of_castSucc_lt
  given: (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i)
  proof: dif_pos h

中文:
引理 predAbove_of_castSucc_lt
  条件: (p : 有限集 n) (i : 有限集 (n + 1)) (h : castSucc p < i)
  证明: dif_pos h

Depends on / 依赖: dif_pos
-/
lemma predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred (Fin.ne_zero_of_lt h) := dif_pos h

/--
lemma `predAbove_of_succ_le` / 引理 `predAbove_of_succ_le`

English:
lemma predAbove_of_succ_le
  given: (p : Fin n) (i : Fin (n + 1)) (h : succ p <= i)
  proof: predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

中文:
引理 predAbove_of_succ_le
  条件: (p : 有限集 n) (i : 有限集 (n + 1)) (h : succ p <= i)
  证明: predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

Depends on / 依赖: castSucc_lt_iff_succ_le, castSucc_lt_iff_succ_le.mpr, predAbove_of_castSucc_lt
-/
lemma predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p <= i) :
    p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (succ_pos _) h) :=
  predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

/--
lemma `predAbove_succ_of_lt` / 引理 `predAbove_succ_of_lt`

English:
lemma predAbove_succ_of_lt
  given: (p i : Fin n) (h : i < p)
  proof: by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]

中文:
引理 predAbove_succ_of_lt
  条件: (p i : 有限集 n) (h : i < p)
  证明: by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]

Depends on / 依赖: predAbove_of_lt_succ, succ_lt_succ_iff, succ_lt_succ_iff.mpr
-/
lemma predAbove_succ_of_lt (p i : Fin n) (h : i < p) :
    p.predAbove (succ i) = (i.succ).castPred (succ_ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]

/--
lemma `predAbove_succ_of_le` / 引理 `predAbove_succ_of_le`

English:
lemma predAbove_succ_of_le
  given: (p i : Fin n) (h : p <= i)
  statement: p.predAbove (succ i) = i
  proof: by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)]; rw [pred_succ]

中文:
引理 predAbove_succ_of_le
  条件: (p i : 有限集 n) (h : p <= i)
  结论: p.predAbove (succ i) = i
  证明: by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)]; rw [pred_succ]

Depends on / 依赖: predAbove_of_succ_le, pred_succ, succ_le_succ_iff, succ_le_succ_iff.mpr
-/
lemma predAbove_succ_of_le (p i : Fin n) (h : p <= i) : p.predAbove (succ i) = i := by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)]; rw [pred_succ]

/--
lemma `predAbove_succ_self` / 引理 `predAbove_succ_self`

English:
lemma predAbove_succ_self
  given: (p : Fin n)
  statement: p.predAbove (succ p) = p
  proof: predAbove_succ_of_le _ _ Fin.le_rfl

中文:
引理 predAbove_succ_self
  条件: (p : 有限集 n)
  结论: p.predAbove (succ p) = p
  证明: predAbove_succ_of_le _ _ Fin.le_rfl
-/
@[simp] lemma predAbove_succ_self (p : Fin n) : p.predAbove (succ p) = p :=
  predAbove_succ_of_le _ _ Fin.le_rfl

/--
lemma `predAbove_castSucc_of_lt` / 引理 `predAbove_castSucc_of_lt`

English:
lemma predAbove_castSucc_of_lt
  given: (p i : Fin n) (h : p < i)
  proof: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]

中文:
引理 predAbove_castSucc_of_lt
  条件: (p i : 有限集 n) (h : p < i)
  证明: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]

Depends on / 依赖: castSucc_lt_castSucc_iff, predAbove_of_castSucc_lt
-/
lemma predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) :
    p.predAbove (castSucc i) = i.castSucc.pred (castSucc_ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]

/--
lemma `predAbove_castSucc_of_le` / 引理 `predAbove_castSucc_of_le`

English:
lemma predAbove_castSucc_of_le
  given: (p i : Fin n) (h : i <= p)
  statement: p.predAbove (castSucc i) = i
  proof: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h)]; rw [castPred_castSucc]

中文:
引理 predAbove_castSucc_of_le
  条件: (p i : 有限集 n) (h : i <= p)
  结论: p.predAbove (castSucc i) = i
  证明: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h)]; rw [castPred_castSucc]

Depends on / 依赖: castPred_castSucc, castSucc_le_castSucc_iff, castSucc_le_castSucc_iff.mpr, predAbove_of_le_castSucc
-/
lemma predAbove_castSucc_of_le (p i : Fin n) (h : i <= p) : p.predAbove (castSucc i) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h)]; rw [castPred_castSucc]

/--
lemma `predAbove_castSucc_self` / 引理 `predAbove_castSucc_self`

English:
lemma predAbove_castSucc_self
  given: (p : Fin n)
  statement: p.predAbove (castSucc p) = p
  proof: predAbove_castSucc_of_le _ _ Fin.le_rfl

中文:
引理 predAbove_castSucc_self
  条件: (p : 有限集 n)
  结论: p.predAbove (castSucc p) = p
  证明: predAbove_castSucc_of_le _ _ Fin.le_rfl
-/
@[simp] lemma predAbove_castSucc_self (p : Fin n) : p.predAbove (castSucc p) = p :=
  predAbove_castSucc_of_le _ _ Fin.le_rfl

/--
lemma `predAbove_pred_of_lt` / 引理 `predAbove_pred_of_lt`

English:
lemma predAbove_pred_of_lt
  given: (p i : Fin (n + 1)) (h : i < p)
  proof: by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]

中文:
引理 predAbove_pred_of_lt
  条件: (p i : 有限集 (n + 1)) (h : i < p)
  证明: by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]

Depends on / 依赖: predAbove_of_lt_succ, succ_pred
-/
lemma predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    (pred p (Fin.ne_zero_of_lt h)).predAbove i = castPred i (Fin.ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]

/--
lemma `predAbove_pred_of_le` / 引理 `predAbove_pred_of_le`

English:
lemma predAbove_pred_of_le
  given: (p i : Fin (n + 1)) (h : p <= i) (hp : p != 0)
  proof: by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]

中文:
引理 predAbove_pred_of_le
  条件: (p i : 有限集 (n + 1)) (h : p <= i) (hp : p != 0)
  证明: by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]

Depends on / 依赖: predAbove_of_succ_le, succ_pred
-/
lemma predAbove_pred_of_le (p i : Fin (n + 1)) (h : p <= i) (hp : p != 0) :
    (pred p hp).predAbove i =
      pred i (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (Fin.pos_iff_ne_zero.2 hp) h) := by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]

/--
lemma `predAbove_pred_self` / 引理 `predAbove_pred_self`

English:
lemma predAbove_pred_self
  given: (p : Fin (n + 1)) (hp : p != 0)
  statement: (pred p hp).predAbove p = pred p hp
  proof: predAbove_pred_of_le _ _ Fin.le_rfl hp

中文:
引理 predAbove_pred_self
  条件: (p : 有限集 (n + 1)) (hp : p != 0)
  结论: (pred p hp).predAbove p = pred p hp
  证明: predAbove_pred_of_le _ _ Fin.le_rfl hp

Depends on / 依赖: Fin.le_rfl, le_rfl, predAbove_pred_of_le
-/
lemma predAbove_pred_self (p : Fin (n + 1)) (hp : p != 0) : (pred p hp).predAbove p = pred p hp :=
  predAbove_pred_of_le _ _ Fin.le_rfl hp

/--
lemma `predAbove_castPred_of_lt` / 引理 `predAbove_castPred_of_lt`

English:
lemma predAbove_castPred_of_lt
  given: (p i : Fin (n + 1)) (h : p < i)
  proof: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]

中文:
引理 predAbove_castPred_of_lt
  条件: (p i : 有限集 (n + 1)) (h : p < i)
  证明: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]

Depends on / 依赖: castSucc_castPred, predAbove_of_castSucc_lt
-/
lemma predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    (castPred p (Fin.ne_last_of_lt h)).predAbove i = pred i (Fin.ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]

/--
lemma `predAbove_castPred_of_le` / 引理 `predAbove_castPred_of_le`

English:
lemma predAbove_castPred_of_le
  given: (p i : Fin (n + 1)) (h : i <= p) (hp : p != last n)
  proof: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]

中文:
引理 predAbove_castPred_of_le
  条件: (p i : 有限集 (n + 1)) (h : i <= p) (hp : p != last n)
  证明: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]

Depends on / 依赖: castSucc_castPred, predAbove_of_le_castSucc
-/
lemma predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i <= p) (hp : p != last n) :
    (castPred p hp).predAbove i =
      castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| Fin.lt_last_iff_ne_last.2 hp) := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]

/--
lemma `predAbove_castPred_self` / 引理 `predAbove_castPred_self`

English:
lemma predAbove_castPred_self
  given: (p : Fin (n + 1)) (hp : p != last n)
  proof: predAbove_castPred_of_le _ _ Fin.le_rfl hp

中文:
引理 predAbove_castPred_self
  条件: (p : 有限集 (n + 1)) (hp : p != last n)
  证明: predAbove_castPred_of_le _ _ Fin.le_rfl hp

Depends on / 依赖: Fin.le_rfl, le_rfl, predAbove_castPred_of_le
-/
lemma predAbove_castPred_self (p : Fin (n + 1)) (hp : p != last n) :
    (castPred p hp).predAbove p = castPred p hp := predAbove_castPred_of_le _ _ Fin.le_rfl hp

/--
lemma `predAbove_right_zero` / 引理 `predAbove_right_zero`

English:
lemma predAbove_right_zero
  given: [NeZero n] {i : Fin n}
  statement: predAbove (i : Fin n) 0 = 0
  proof: by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]

中文:
引理 predAbove_right_zero
  条件: [NeZero n] {i : 有限集 n}
  结论: predAbove (i : 有限集 n) 0 = 0
  证明: by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]
-/
@[simp] lemma predAbove_right_zero [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]

/--
lemma `predAbove_zero_succ` / 引理 `predAbove_zero_succ`

English:
lemma predAbove_zero_succ
  given: [NeZero n] {i : Fin n}
  statement: predAbove 0 i.succ = i
  proof: by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le _)]

中文:
引理 predAbove_zero_succ
  条件: [NeZero n] {i : 有限集 n}
  结论: predAbove 0 i.succ = i
  证明: by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le _)]

Depends on / 依赖: Fin.zero_le, predAbove_succ_of_le, zero_le
-/
lemma predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 i.succ = i := by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le _)]

/--
lemma `predAbove_zero_of_ne_zero` / 引理 `predAbove_zero_of_ne_zero`

English:
lemma predAbove_zero_of_ne_zero
  given: [NeZero n] {i : Fin (n + 1)} (hi : i != 0)
  proof: by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi
  exact predAbove_zero_succ

中文:
引理 predAbove_zero_of_ne_zero
  条件: [NeZero n] {i : 有限集 (n + 1)} (hi : i != 0)
  证明: by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi
  exact predAbove_zero_succ
-/
@[simp] lemma predAbove_zero_of_ne_zero [NeZero n] {i : Fin (n + 1)} (hi : i != 0) :
    predAbove 0 i = i.pred hi := by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi
  exact predAbove_zero_succ

/--
lemma `succ_predAbove_zero` / 引理 `succ_predAbove_zero`

English:
lemma succ_predAbove_zero
  given: [NeZero n] {j : Fin (n + 1)} (h : j != 0)
  statement: succ (predAbove 0 j) = j
  proof: by
  simp [h]

中文:
引理 succ_predAbove_zero
  条件: [NeZero n] {j : 有限集 (n + 1)} (h : j != 0)
  结论: succ (predAbove 0 j) = j
  证明: by
  simp [h]
-/
lemma succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j != 0) : succ (predAbove 0 j) = j := by
  simp [h]

/--
lemma `predAbove_zero` / 引理 `predAbove_zero`

English:
lemma predAbove_zero
  given: [NeZero n] {i : Fin (n + 1)}
  proof: by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

中文:
引理 predAbove_zero
  条件: [NeZero n] {i : 有限集 (n + 1)}
  证明: by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

Depends on / 依赖: predAbove_right_zero, predAbove_zero_of_ne_zero, split_ifs
-/
lemma predAbove_zero [NeZero n] {i : Fin (n + 1)} :
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

/--
lemma `predAbove_right_last` / 引理 `predAbove_right_last`

English:
lemma predAbove_right_last
  given: {i : Fin (n + 1)}
  statement: predAbove i (last (n + 1)) = last n
  proof: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _)]; rw [pred_last]

中文:
引理 predAbove_right_last
  条件: {i : 有限集 (n + 1)}
  结论: predAbove i (last (n + 1)) = last n
  证明: by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _)]; rw [pred_last]
-/
@[simp] lemma predAbove_right_last {i : Fin (n + 1)} : predAbove i (last (n + 1)) = last n := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _)]; rw [pred_last]

/--
lemma `predAbove_last_castSucc` / 引理 `predAbove_last_castSucc`

English:
lemma predAbove_last_castSucc
  given: {i : Fin (n + 1)}
  statement: predAbove (last n) (i.castSucc) = i
  proof: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr (le_last _))]; rw [castPred_castSucc]

中文:
引理 predAbove_last_castSucc
  条件: {i : 有限集 (n + 1)}
  结论: predAbove (last n) (i.castSucc) = i
  证明: by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr (le_last _))]; rw [castPred_castSucc]

Depends on / 依赖: castPred_castSucc, castSucc_le_castSucc_iff, castSucc_le_castSucc_iff.mpr, le_last, predAbove_of_le_castSucc
-/
lemma predAbove_last_castSucc {i : Fin (n + 1)} : predAbove (last n) (i.castSucc) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr (le_last _))]; rw [castPred_castSucc]

/--
lemma `predAbove_last_of_ne_last` / 引理 `predAbove_last_of_ne_last`

English:
lemma predAbove_last_of_ne_last
  given: {i : Fin (n + 2)} (hi : i != last (n + 1))
  proof: by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc

中文:
引理 predAbove_last_of_ne_last
  条件: {i : 有限集 (n + 2)} (hi : i != last (n + 1))
  证明: by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc
-/
@[simp] lemma predAbove_last_of_ne_last {i : Fin (n + 2)} (hi : i != last (n + 1)) :
    predAbove (last n) i = castPred i hi := by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc

/--
lemma `predAbove_last_apply` / 引理 `predAbove_last_apply`

English:
lemma predAbove_last_apply
  given: {i : Fin (n + 2)}
  proof: by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]

中文:
引理 predAbove_last_apply
  条件: {i : 有限集 (n + 2)}
  证明: by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]

Depends on / 依赖: predAbove_last_of_ne_last, predAbove_right_last, split_ifs
-/
lemma predAbove_last_apply {i : Fin (n + 2)} :
    predAbove (last n) i = if hi : i = last _ then last _ else i.castPred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]

/--
lemma `predAbove_surjective` / 引理 `predAbove_surjective`

English:
lemma predAbove_surjective
  given: {n : Nat} (p : Fin n)
  proof: by
  intro i
  by_cases hi : i <= p
  · exact ⟨i.castSucc, predAbove_castSucc_of_le p i hi⟩
  · rw [Fin.not_le] at hi
    exact ⟨i.succ, predAbove_succ_of_le p i (Fin.le_of_lt hi)⟩

中文:
引理 predAbove_surjective
  条件: {n : 自然数} (p : 有限集 n)
  证明: by
  intro i
  by_cases hi : i <= p
  · exact ⟨i.castSucc, predAbove_castSucc_of_le p i hi⟩
  · rw [Fin.not_le] at hi
    exact ⟨i.succ, predAbove_succ_of_le p i (Fin.le_of_lt hi)⟩

Depends on / 依赖: Fin.le_of_lt, Fin.not_le, castSucc, i.castSucc, i.succ, le_of_lt, not_le, predAbove_castSucc_of_le, predAbove_succ_of_le
-/
lemma predAbove_surjective {n : Nat} (p : Fin n) :
    Function.Surjective p.predAbove := by
  intro i
  by_cases hi : i <= p
  · exact ⟨i.castSucc, predAbove_castSucc_of_le p i hi⟩
  · rw [Fin.not_le] at hi
    exact ⟨i.succ, predAbove_succ_of_le p i (Fin.le_of_lt hi)⟩

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
/--
lemma `succAbove_predAbove` / 引理 `succAbove_predAbove`

English:
lemma succAbove_predAbove
  given: {p : Fin n} {i : Fin (n + 1)} (h : i != castSucc p)
  proof: by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

中文:
引理 succAbove_predAbove
  条件: {p : 有限集 n} {i : 有限集 (n + 1)} (h : i != castSucc p)
  证明: by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

Depends on / 依赖: Fin.le_of_lt, Fin.lt_or_lt_of_ne, le_of_lt, lt_or_lt_of_ne, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, succAbove_castPred_of_lt, succAbove_pred_of_lt
-/
lemma succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i != castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p.succ` is the identity away from `p.succ`. -/
@[simp]
/--
lemma `succ_succAbove_predAbove` / 引理 `succ_succAbove_predAbove`

English:
lemma succ_succAbove_predAbove
  given: {n : Nat} {p : Fin n} {i : Fin (n + 1)} (h : i != p.succ)
  proof: by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (le_castSucc_iff.2 h),
      succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ (Fin.lt_of_le_of_lt (p.castSucc_le_succ) h),
      succAbove_pred_of_lt _ _ h]

中文:
引理 succ_succAbove_predAbove
  条件: {n : 自然数} {p : 有限集 n} {i : 有限集 (n + 1)} (h : i != p.succ)
  证明: by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (le_castSucc_iff.2 h),
      succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ (Fin.lt_of_le_of_lt (p.castSucc_le_succ) h),
      succAbove_pred_of_lt _ _ h]

Depends on / 依赖: Fin.lt_of_le_of_lt, Fin.lt_or_lt_of_ne, castSucc_le_succ, le_castSucc_iff, lt_of_le_of_lt, lt_or_lt_of_ne, p.castSucc_le_succ, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, succAbove_castPred_of_lt, succAbove_pred_of_lt
-/
lemma succ_succAbove_predAbove {n : Nat} {p : Fin n} {i : Fin (n + 1)} (h : i != p.succ) :
    p.succ.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (le_castSucc_iff.2 h),
      succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ (Fin.lt_of_le_of_lt (p.castSucc_le_succ) h),
      succAbove_pred_of_lt _ _ h]

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
/--
lemma `predAbove_succAbove` / 引理 `predAbove_succAbove`

English:
lemma predAbove_succAbove
  given: (p : Fin n) (i : Fin n)
  statement: p.predAbove ((castSucc p).succAbove i) = i
  proof: by
  obtain h | h := p.le_or_gt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

中文:
引理 predAbove_succAbove
  条件: (p : 有限集 n) (i : 有限集 n)
  结论: p.predAbove ((castSucc p).succAbove i) = i
  证明: by
  obtain h | h := p.le_or_gt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

Depends on / 依赖: Fin.le_of_lt, le_of_lt, le_or_gt, p.le_or_gt, predAbove_castSucc_of_le, predAbove_succ_of_le, succAbove_castSucc_of_le, succAbove_castSucc_of_lt
-/
lemma predAbove_succAbove (p : Fin n) (i : Fin n) : p.predAbove ((castSucc p).succAbove i) = i := by
  obtain h | h := p.le_or_gt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

/--
lemma `succ_predAbove_succ` / 引理 `succ_predAbove_succ`

English:
lemma succ_predAbove_succ
  given: (a : Fin n) (b : Fin (n + 1))
  proof: by
  obtain h | h := Fin.le_or_gt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]

中文:
引理 succ_predAbove_succ
  条件: (a : 有限集 n) (b : 有限集 (n + 1))
  证明: by
  obtain h | h := Fin.le_or_gt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]
-/
@[simp] lemma succ_predAbove_succ (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h | h := Fin.le_or_gt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]

/--
lemma `castSucc_predAbove_castSucc` / 引理 `castSucc_predAbove_castSucc`

English:
lemma castSucc_predAbove_castSucc
  given: {n : Nat} (a : Fin n) (b : Fin (n + 1))
  proof: by
  obtain h | h := a.castSucc.lt_or_ge b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]

中文:
引理 castSucc_predAbove_castSucc
  条件: {n : 自然数} (a : 有限集 n) (b : 有限集 (n + 1))
  证明: by
  obtain h | h := a.castSucc.lt_or_ge b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]
-/
@[simp] lemma castSucc_predAbove_castSucc {n : Nat} (a : Fin n) (b : Fin (n + 1)) :
    a.castSucc.predAbove b.castSucc = (a.predAbove b).castSucc := by
  obtain h | h := a.castSucc.lt_or_ge b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]

/--
theorem `predAbove_predAbove_succAbove` / 定理 `predAbove_predAbove_succAbove`

English:
theorem predAbove_predAbove_succAbove
  given: {n : Nat} (i : Fin (n + 1)) (j : Fin n)
  proof: by
  cases j.castSucc.lt_or_le i with
  | inl h =>
    rw [predAbove_of_castSucc_lt _ _ h]; rw [succAbove_of_castSucc_lt _ _ h]; rw [predAbove_of_le_castSucc]; rw [castPred_castSucc]
    rwa [le_castSucc_iff, succ_pred]
  | inr h =>
    rw [predAbove_of_le_castSucc _ _ h]; rw [succAbove_of_le_castSucc _ _ h]; rw [predAbove_of_castSucc_lt]; rw [pred_succ]
    rwa [castSucc_castPred, ← le_castSucc_iff]

中文:
定理 predAbove_predAbove_succAbove
  条件: {n : 自然数} (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: by
  cases j.castSucc.lt_or_le i with
  | inl h =>
    rw [predAbove_of_castSucc_lt _ _ h]; rw [succAbove_of_castSucc_lt _ _ h]; rw [predAbove_of_le_castSucc]; rw [castPred_castSucc]
    rwa [le_castSucc_iff, succ_pred]
  | inr h =>
    rw [predAbove_of_le_castSucc _ _ h]; rw [succAbove_of_le_castSucc _ _ h]; rw [predAbove_of_castSucc_lt]; rw [pred_succ]
    rwa [castSucc_castPred, ← le_castSucc_iff]

Depends on / 依赖: castPred_castSucc, castSucc, castSucc_castPred, j.castSucc.lt_or_le, le_castSucc_iff, lt_or_le, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, pred_succ, succAbove_of_castSucc_lt, succAbove_of_le_castSucc, succ_pred
-/
theorem predAbove_predAbove_succAbove {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    (j.predAbove i).predAbove (i.succAbove j) = j := by
  cases j.castSucc.lt_or_le i with
  | inl h =>
    rw [predAbove_of_castSucc_lt _ _ h]; rw [succAbove_of_castSucc_lt _ _ h]; rw [predAbove_of_le_castSucc]; rw [castPred_castSucc]
    rwa [le_castSucc_iff, succ_pred]
  | inr h =>
    rw [predAbove_of_le_castSucc _ _ h]; rw [succAbove_of_le_castSucc _ _ h]; rw [predAbove_of_castSucc_lt]; rw [pred_succ]
    rwa [castSucc_castPred, ← le_castSucc_iff]

/--
theorem `succAbove_succAbove_predAbove` / 定理 `succAbove_succAbove_predAbove`

English:
theorem succAbove_succAbove_predAbove
  given: {n : Nat} (i : Fin (n + 1)) (j : Fin n)
  proof: by
  cases Fin.lt_or_le j.castSucc i with
  | inl h => rw [succAbove_of_castSucc_lt _ _ h, succAbove_predAbove (Fin.ne_of_gt h)]
  | inr h =>
    rw [succAbove_of_le_castSucc _ _ h]; rw [succ_succAbove_predAbove (Fin.ne_of_lt <| le_castSucc_iff.mp h)]

中文:
定理 succAbove_succAbove_predAbove
  条件: {n : 自然数} (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: by
  cases Fin.lt_or_le j.castSucc i with
  | inl h => rw [succAbove_of_castSucc_lt _ _ h, succAbove_predAbove (Fin.ne_of_gt h)]
  | inr h =>
    rw [succAbove_of_le_castSucc _ _ h]; rw [succ_succAbove_predAbove (Fin.ne_of_lt <| le_castSucc_iff.mp h)]

Depends on / 依赖: Fin.lt_or_le, Fin.ne_of_gt, Fin.ne_of_lt, castSucc, j.castSucc, le_castSucc_iff, le_castSucc_iff.mp, lt_or_le, ne_of_gt, ne_of_lt, succAbove_of_castSucc_lt, succAbove_of_le_castSucc, succAbove_predAbove, succ_succAbove_predAbove
-/
theorem succAbove_succAbove_predAbove {n : Nat} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).succAbove (j.predAbove i) = i := by
  cases Fin.lt_or_le j.castSucc i with
  | inl h => rw [succAbove_of_castSucc_lt _ _ h, succAbove_predAbove (Fin.ne_of_gt h)]
  | inr h =>
    rw [succAbove_of_le_castSucc _ _ h]; rw [succ_succAbove_predAbove (Fin.ne_of_lt <| le_castSucc_iff.mp h)]

/--
theorem `succAbove_succAbove_succAbove_predAbove` / 定理 `succAbove_succAbove_succAbove_predAbove`

English:
theorem succAbove_succAbove_succAbove_predAbove
  statement: {n : Nat}
  proof: by
  /- While it is possible to give a "morally correct" proof
  by saying that both functions are strictly monotone and have the same range `{i, i.succAbove j}ᶜ`,
  we give a direct proof by case analysis to avoid extra dependencies. -/
  ext
  simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val, val_pred, coe_castPred,
    dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> lia

中文:
定理 succAbove_succAbove_succAbove_predAbove
  结论: {n : 自然数}
  证明: by
  /- While it is possible to give a "morally correct" proof
  by saying that both functions are strictly monotone and have the same range `{i, i.succAbove j}ᶜ`,
  we give a direct proof by case analysis to avoid extra dependencies. -/
  ext
  simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val, val_pred, coe_castPred,
    dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> lia
-/
theorem succAbove_succAbove_succAbove_predAbove {n : Nat}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  /- While it is possible to give a "morally correct" proof
  by saying that both functions are strictly monotone and have the same range `{i, i.succAbove j}ᶜ`,
  we give a direct proof by case analysis to avoid extra dependencies. -/
  ext
  simp only [succAbove, predAbove, lt_def, val_castSucc, apply_dite Fin.val, val_pred, coe_castPred,
    dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> lia

end PredAbove

end Fin
