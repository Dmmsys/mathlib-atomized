/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Lemmas about coprimality with big products.

These lemmas are kept separate from `Data.Nat.GCD.Basic` in order to minimize imports.
-/

public section


namespace Nat

variable {ι : Type*}

/--
theorem `coprime_list_prod_left_iff` / 定理 `coprime_list_prod_left_iff`

English:
theorem coprime_list_prod_left_iff
  given: {l : List Nat} {k : Nat}
  proof: by
  induction l <;> simp [Nat.coprime_mul_iff_left, *]

中文:
定理 coprime_list_prod_left_iff
  条件: {l : List 自然数} {k : 自然数}
  证明: by
  induction l <;> simp [Nat.coprime_mul_iff_left, *]

Depends on / 依赖: Nat.coprime_mul_iff_left, coprime_mul_iff_left
-/
theorem coprime_list_prod_left_iff {l : List Nat} {k : Nat} :
    Coprime l.prod k ↔ forall n in l, Coprime n k := by
  induction l <;> simp [Nat.coprime_mul_iff_left, *]

/--
theorem `coprime_list_prod_right_iff` / 定理 `coprime_list_prod_right_iff`

English:
theorem coprime_list_prod_right_iff
  given: {k : Nat} {l : List Nat}
  proof: by
  simp_rw [coprime_comm (n := k), coprime_list_prod_left_iff]

中文:
定理 coprime_list_prod_right_iff
  条件: {k : 自然数} {l : List 自然数}
  证明: by
  simp_rw [coprime_comm (n := k), coprime_list_prod_left_iff]

Depends on / 依赖: coprime_comm, coprime_list_prod_left_iff, simp_rw
-/
theorem coprime_list_prod_right_iff {k : Nat} {l : List Nat} :
    Coprime k l.prod ↔ forall n in l, Coprime k n := by
  simp_rw [coprime_comm (n := k), coprime_list_prod_left_iff]

/--
theorem `coprime_multiset_prod_left_iff` / 定理 `coprime_multiset_prod_left_iff`

English:
theorem coprime_multiset_prod_left_iff
  given: {m : Multiset Nat} {k : Nat}
  proof: by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_left_iff

中文:
定理 coprime_multiset_prod_left_iff
  条件: {m : Multiset 自然数} {k : 自然数}
  证明: by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_left_iff

Depends on / 依赖: Quotient, Quotient.inductionOn, coprime_list_prod_left_iff, inductionOn
-/
theorem coprime_multiset_prod_left_iff {m : Multiset Nat} {k : Nat} :
    Coprime m.prod k ↔ forall n in m, Coprime n k := by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_left_iff

/--
theorem `coprime_multiset_prod_right_iff` / 定理 `coprime_multiset_prod_right_iff`

English:
theorem coprime_multiset_prod_right_iff
  given: {k : Nat} {m : Multiset Nat}
  proof: by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_right_iff

中文:
定理 coprime_multiset_prod_right_iff
  条件: {k : 自然数} {m : Multiset 自然数}
  证明: by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_right_iff

Depends on / 依赖: Quotient, Quotient.inductionOn, coprime_list_prod_right_iff, inductionOn
-/
theorem coprime_multiset_prod_right_iff {k : Nat} {m : Multiset Nat} :
    Coprime k m.prod ↔ forall n in m, Coprime k n := by
  induction m using Quotient.inductionOn; simpa using coprime_list_prod_right_iff

/--
theorem `coprime_prod_left_iff` / 定理 `coprime_prod_left_iff`

English:
theorem coprime_prod_left_iff
  given: {t : Finset ι} {s : ι -> Nat} {x : Nat}
  proof: by
  simpa using coprime_multiset_prod_left_iff (m := t.val.map s)

中文:
定理 coprime_prod_left_iff
  条件: {t : Finset ι} {s : ι -> 自然数} {x : 自然数}
  证明: by
  simpa using coprime_multiset_prod_left_iff (m := t.val.map s)

Depends on / 依赖: coprime_multiset_prod_left_iff, t.val.map
-/
theorem coprime_prod_left_iff {t : Finset ι} {s : ι -> Nat} {x : Nat} :
    Coprime (∏ i in t, s i) x ↔ forall i in t, Coprime (s i) x := by
  simpa using coprime_multiset_prod_left_iff (m := t.val.map s)

/--
theorem `coprime_prod_right_iff` / 定理 `coprime_prod_right_iff`

English:
theorem coprime_prod_right_iff
  given: {x : Nat} {t : Finset ι} {s : ι -> Nat}
  proof: by
  simpa using coprime_multiset_prod_right_iff (m := t.val.map s)

中文:
定理 coprime_prod_right_iff
  条件: {x : 自然数} {t : Finset ι} {s : ι -> 自然数}
  证明: by
  simpa using coprime_multiset_prod_right_iff (m := t.val.map s)

Depends on / 依赖: coprime_multiset_prod_right_iff, t.val.map
-/
theorem coprime_prod_right_iff {x : Nat} {t : Finset ι} {s : ι -> Nat} :
    Coprime x (∏ i in t, s i) ↔ forall i in t, Coprime x (s i) := by
  simpa using coprime_multiset_prod_right_iff (m := t.val.map s)

/-- See `IsCoprime.prod_left` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_left⟩ := coprime_prod_left_iff

/-- See `IsCoprime.prod_right` for the corresponding lemma about `IsCoprime` -/
alias ⟨_, Coprime.prod_right⟩ := coprime_prod_right_iff

/--
theorem `coprime_fintype_prod_left_iff` / 定理 `coprime_fintype_prod_left_iff`

English:
theorem coprime_fintype_prod_left_iff
  given: [Fintype ι] {s : ι -> Nat} {x : Nat}
  proof: by
  simp [coprime_prod_left_iff]

中文:
定理 coprime_fintype_prod_left_iff
  条件: [Fintype ι] {s : ι -> 自然数} {x : 自然数}
  证明: by
  simp [coprime_prod_left_iff]

Depends on / 依赖: coprime_prod_left_iff
-/
theorem coprime_fintype_prod_left_iff [Fintype ι] {s : ι -> Nat} {x : Nat} :
    Coprime (∏ i, s i) x ↔ forall i, Coprime (s i) x := by
  simp [coprime_prod_left_iff]

/--
theorem `coprime_fintype_prod_right_iff` / 定理 `coprime_fintype_prod_right_iff`

English:
theorem coprime_fintype_prod_right_iff
  given: [Fintype ι] {x : Nat} {s : ι -> Nat}
  proof: by
  simp [coprime_prod_right_iff]

中文:
定理 coprime_fintype_prod_right_iff
  条件: [Fintype ι] {x : 自然数} {s : ι -> 自然数}
  证明: by
  simp [coprime_prod_right_iff]

Depends on / 依赖: coprime_prod_right_iff
-/
theorem coprime_fintype_prod_right_iff [Fintype ι] {x : Nat} {s : ι -> Nat} :
    Coprime x (∏ i, s i) ↔ forall i, Coprime x (s i) := by
  simp [coprime_prod_right_iff]

end Nat
