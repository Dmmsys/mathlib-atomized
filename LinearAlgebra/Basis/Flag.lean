/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Fin.FlagRange
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Flag of submodules defined by a basis

In this file we define `Basis.flag b k`, where `b : Basis (Fin n) R M`, `k : Fin (n + 1)`,
to be the subspace spanned by the first `k` vectors of the basis `b`.

We also prove some lemmas about this definition.
-/

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- This is why this section is `noncomputable`.
-- See https://github.com/leanprover/lean4/issues/14084.
@[expose] public noncomputable section

open Set Submodule

namespace Module.Basis

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : Nat} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

/--
Definition of `flag` / `flag` 的定义

English:
definition flag
  signature: (b : Basis (Fin n) R M) (k : Fin (n + 1))
  body: .span R b '' {i | i.castSucc < k}

@[simp]

中文:
定义 flag
  签名: (b : 基 (有限集 n) R M) (k : 有限集 (n + 1))
  定义体: .span R b '' {i | i.castSucc < k}

@[simp]

Depends on / 依赖: castSucc, i.castSucc
-/
def flag (b : Basis (Fin n) R M) (k : Fin (n + 1)) : Submodule R M :=
.span R b '' {i | i.castSucc < k}

@[simp]
/--
theorem `flag_zero` / 定理 `flag_zero`

English:
theorem flag_zero
  given: (b : Basis (Fin n) R M)
  statement: b.flag 0 = ⊥
  proof: by simp [flag]

@[simp]

中文:
定理 flag_zero
  条件: (b : 基 (有限集 n) R M)
  结论: b.flag 0 = ⊥
  证明: by simp [flag]

@[simp]
-/
theorem flag_zero (b : Basis (Fin n) R M) : b.flag 0 = ⊥ := by simp [flag]

@[simp]
/--
theorem `flag_last` / 定理 `flag_last`

English:
theorem flag_last
  given: (b : Basis (Fin n) R M)
  statement: b.flag (.last n) = ⊤
  proof: by
  simp [flag]

中文:
定理 flag_last
  条件: (b : 基 (有限集 n) R M)
  结论: b.flag (.last n) = ⊤
  证明: by
  simp [flag]
-/
theorem flag_last (b : Basis (Fin n) R M) : b.flag (.last n) = ⊤ := by
  simp [flag]

/--
theorem `flag_le_iff` / 定理 `flag_le_iff`

English:
theorem flag_le_iff
  given: (b : Basis (Fin n) R M) {k p}
  proof: span_le.trans forall_mem_image

中文:
定理 flag_le_iff
  条件: (b : 基 (有限集 n) R M) {k p}
  证明: span_le.trans forall_mem_image

Depends on / 依赖: forall_mem_image, span_le, span_le.trans
-/
theorem flag_le_iff (b : Basis (Fin n) R M) {k p} :
    b.flag k <= p ↔ forall i : Fin n, i.castSucc < k -> b i in p :=
  span_le.trans forall_mem_image

/--
theorem `flag_succ` / 定理 `flag_succ`

English:
theorem flag_succ
  given: (b : Basis (Fin n) R M) (k : Fin n)
  proof: by
  simp only [flag, Fin.castSucc_lt_castSucc_iff]
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, ofPred_or, image_insert_eq, span_insert]

中文:
定理 flag_succ
  条件: (b : 基 (有限集 n) R M) (k : 有限集 n)
  证明: by
  simp only [flag, Fin.castSucc_lt_castSucc_iff]
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, ofPred_or, image_insert_eq, span_insert]

Depends on / 依赖: Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_iff_succ_le, castSucc_lt_castSucc_iff, castSucc_lt_iff_succ_le, image_insert_eq, le_iff_eq_or_lt, ofPred_or, span_insert
-/
theorem flag_succ (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc := by
  simp only [flag, Fin.castSucc_lt_castSucc_iff]
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, ofPred_or, image_insert_eq, span_insert]

/--
theorem `self_mem_flag` / 定理 `self_mem_flag`

English:
theorem self_mem_flag
  given: (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i.castSucc < k)
  proof: subset_span mem_image_of_mem _ h

@[simp]

中文:
定理 self_mem_flag
  条件: (b : 基 (有限集 n) R M) {i : 有限集 n} {k : 有限集 (n + 1)} (h : i.castSucc < k)
  证明: subset_span mem_image_of_mem _ h

@[simp]

Depends on / 依赖: mem_image_of_mem, subset_span
-/
theorem self_mem_flag (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} (h : i.castSucc < k) :
    b i in b.flag k :=
subset_span mem_image_of_mem _ h

@[simp]
/--
theorem `self_mem_flag_iff` / 定理 `self_mem_flag_iff`

English:
theorem self_mem_flag_iff
  given: [Nontrivial R] (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)}
  proof: b.self_mem_span_image

@[gcongr, mono]

中文:
定理 self_mem_flag_iff
  条件: [非平凡 R] (b : 基 (有限集 n) R M) {i : 有限集 n} {k : 有限集 (n + 1)}
  证明: b.self_mem_span_image

@[gcongr, mono]

Depends on / 依赖: b.self_mem_span_image, self_mem_span_image
-/
theorem self_mem_flag_iff [Nontrivial R] (b : Basis (Fin n) R M) {i : Fin n} {k : Fin (n + 1)} :
    b i in b.flag k ↔ i.castSucc < k :=
  b.self_mem_span_image

@[gcongr, mono]
/--
theorem `flag_mono` / 定理 `flag_mono`

English:
theorem flag_mono
  given: (b : Basis (Fin n) R M)
  statement: Monotone b.flag
  proof: Fin.monotone_iff_le_succ.2 fun k => by rw [flag_succ]; exact le_sup_right

中文:
定理 flag_mono
  条件: (b : 基 (有限集 n) R M)
  结论: 递增 b.flag
  证明: Fin.monotone_iff_le_succ.2 fun k => by rw [flag_succ]; exact le_sup_right

Depends on / 依赖: Fin.monotone_iff_le_succ, flag_succ, le_sup_right, monotone_iff_le_succ
-/
theorem flag_mono (b : Basis (Fin n) R M) : Monotone b.flag :=
  Fin.monotone_iff_le_succ.2 fun k => by rw [flag_succ]; exact le_sup_right

/--
theorem `isChain_range_flag` / 定理 `isChain_range_flag`

English:
theorem isChain_range_flag
  given: (b : Basis (Fin n) R M)
  statement: IsChain (· <= ·) (range b.flag)
  proof: b.flag_mono.isChain_range

@[gcongr, mono]

中文:
定理 isChain_range_flag
  条件: (b : 基 (有限集 n) R M)
  结论: IsChain (· <= ·) (range b.flag)
  证明: b.flag_mono.isChain_range

@[gcongr, mono]

Depends on / 依赖: b.flag_mono.isChain_range, flag_mono, isChain_range
-/
theorem isChain_range_flag (b : Basis (Fin n) R M) : IsChain (· <= ·) (range b.flag) :=
  b.flag_mono.isChain_range

@[gcongr, mono]
/--
theorem `flag_strictMono` / 定理 `flag_strictMono`

English:
theorem flag_strictMono
  given: [Nontrivial R] (b : Basis (Fin n) R M)
  statement: StrictMono b.flag
  proof: Fin.strictMono_iff_lt_succ.2 fun _ => by simp [flag_succ]

中文:
定理 flag_strictMono
  条件: [非平凡 R] (b : 基 (有限集 n) R M)
  结论: 严格递增 b.flag
  证明: Fin.strictMono_iff_lt_succ.2 fun _ => by simp [flag_succ]

Depends on / 依赖: Fin.strictMono_iff_lt_succ, flag_succ, strictMono_iff_lt_succ
-/
theorem flag_strictMono [Nontrivial R] (b : Basis (Fin n) R M) : StrictMono b.flag :=
  Fin.strictMono_iff_lt_succ.2 fun _ => by simp [flag_succ]

end Semiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : Nat}

@[simp]
/--
theorem `flag_le_ker_coord_iff` / 定理 `flag_le_ker_coord_iff`

English:
theorem flag_le_ker_coord_iff
  given: [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
  proof: by
  simp [flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]

中文:
定理 flag_le_ker_coord_iff
  条件: [非平凡 R] (b : 基 (有限集 n) R M) {k : 有限集 (n + 1)} {l : 有限集 n}
  证明: by
  simp [flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]

Depends on / 依赖: Finsupp, Finsupp.single_apply_eq_zero, flag_le_iff, imp_false, imp_not_comm, single_apply_eq_zero
-/
theorem flag_le_ker_coord_iff [Nontrivial R] (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k <= LinearMap.ker (b.coord l) ↔ k <= l.castSucc := by
  simp [flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]

/--
theorem `flag_le_ker_coord` / 定理 `flag_le_ker_coord`

English:
theorem flag_le_ker_coord
  statement: (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
  proof: by
  nontriviality R
  exact b.flag_le_ker_coord_iff.2 h

中文:
定理 flag_le_ker_coord
  结论: (b : 基 (有限集 n) R M) {k : 有限集 (n + 1)} {l : 有限集 n}
  证明: by
  nontriviality R
  exact b.flag_le_ker_coord_iff.2 h

Depends on / 依赖: b.flag_le_ker_coord_iff, flag_le_ker_coord_iff, nontriviality
-/
theorem flag_le_ker_coord (b : Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
    (h : k <= l.castSucc) : b.flag k <= LinearMap.ker (b.coord l) := by
  nontriviality R
  exact b.flag_le_ker_coord_iff.2 h

/--
theorem `flag_le_ker_dual` / 定理 `flag_le_ker_dual`

English:
theorem flag_le_ker_dual
  given: (b : Basis (Fin n) R M) (k : Fin n)
  proof: by
  nontriviality R
  rw [coe_dualBasis]; rw [b.flag_le_ker_coord_iff]

中文:
定理 flag_le_ker_dual
  条件: (b : 基 (有限集 n) R M) (k : 有限集 n)
  证明: by
  nontriviality R
  rw [coe_dualBasis]; rw [b.flag_le_ker_coord_iff]

Depends on / 依赖: b.flag_le_ker_coord_iff, coe_dualBasis, flag_le_ker_coord_iff, nontriviality
-/
theorem flag_le_ker_dual (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.castSucc <= LinearMap.ker (b.dualBasis k) := by
  nontriviality R
  rw [coe_dualBasis]; rw [b.flag_le_ker_coord_iff]

end CommRing

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : Nat}

/--
theorem `flag_covBy` / 定理 `flag_covBy`

English:
theorem flag_covBy
  given: (b : Basis (Fin n) K V) (i : Fin n)
  proof: by
  rw [flag_succ]
  apply covBy_span_singleton_sup
  simp

中文:
定理 flag_covBy
  条件: (b : 基 (有限集 n) K V) (i : 有限集 n)
  证明: by
  rw [flag_succ]
  apply covBy_span_singleton_sup
  simp

Depends on / 依赖: covBy_span_singleton_sup, flag_succ
-/
theorem flag_covBy (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⋖ b.flag i.succ := by
  rw [flag_succ]
  apply covBy_span_singleton_sup
  simp

/--
theorem `flag_wcovBy` / 定理 `flag_wcovBy`

English:
theorem flag_wcovBy
  given: (b : Basis (Fin n) K V) (i : Fin n)
  proof: (b.flag_covBy i).wcovBy

中文:
定理 flag_wcovBy
  条件: (b : 基 (有限集 n) K V) (i : 有限集 n)
  证明: (b.flag_covBy i).wcovBy

Depends on / 依赖: b.flag_covBy, flag_covBy, wcovBy
-/
theorem flag_wcovBy (b : Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ :=
  (b.flag_covBy i).wcovBy

/-- Range of `Basis.flag` as a `Flag`. -/
@[simps!]
/--
Definition of `toFlag` / `toFlag` 的定义

English:
definition toFlag
  signature: (b : Basis (Fin n) K V)
  body: .rangeFin b.flag b.flag_zero b.flag_last b.flag_wcovBy

@[simp]

中文:
定义 toFlag
  签名: (b : 基 (有限集 n) K V)
  定义体: .rangeFin b.flag b.flag_zero b.flag_last b.flag_wcovBy

@[simp]

Depends on / 依赖: b.flag, b.flag_last, b.flag_wcovBy, b.flag_zero, flag_last, flag_wcovBy, flag_zero, rangeFin
-/
def toFlag (b : Basis (Fin n) K V) : Flag (Submodule K V) :=
  .rangeFin b.flag b.flag_zero b.flag_last b.flag_wcovBy

@[simp]
/--
theorem `mem_toFlag` / 定理 `mem_toFlag`

English:
theorem mem_toFlag
  given: (b : Basis (Fin n) K V) {p : Submodule K V}
  statement: p in b.toFlag ↔ exists k, b.flag k = p
  proof: Iff.rfl

中文:
定理 mem_toFlag
  条件: (b : 基 (有限集 n) K V) {p : 子模 K V}
  结论: p in b.toFlag ↔ 存在 k, b.flag k = p
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toFlag (b : Basis (Fin n) K V) {p : Submodule K V} : p in b.toFlag ↔ exists k, b.flag k = p :=
  Iff.rfl

/--
theorem `isMaxChain_range_flag` / 定理 `isMaxChain_range_flag`

English:
theorem isMaxChain_range_flag
  given: (b : Basis (Fin n) K V)
  statement: IsMaxChain (· <= ·) (range b.flag)
  proof: b.toFlag.maxChain

中文:
定理 isMaxChain_range_flag
  条件: (b : 基 (有限集 n) K V)
  结论: IsMaxChain (· <= ·) (range b.flag)
  证明: b.toFlag.maxChain

Depends on / 依赖: b.toFlag.maxChain, maxChain, toFlag
-/
theorem isMaxChain_range_flag (b : Basis (Fin n) K V) : IsMaxChain (· <= ·) (range b.flag) :=
  b.toFlag.maxChain

end DivisionRing

end Module.Basis
