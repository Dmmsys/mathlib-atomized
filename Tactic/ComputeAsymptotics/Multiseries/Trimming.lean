/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs

/-!
# Trimming of multiseries

A multiseries is *trimmed* when its leading coefficient (the head of its expansion) is itself
trimmed and non-zero. For a trimmed multiseries, the leading monomial captures the main
asymptotic behavior of the approximated function.

## Main definitions

* `IsZero`: a multiseries represents the zero function — it is either the real number `0`
  (for the empty basis) or has an empty underlying sequence (`.nil`).
* `Trimmed` and `Multiseries.Trimmed`: a multiseries is trimmed in the sense above. The former
  is defined inductively for `MultiseriesExpansion`, and the latter for `Multiseries` is
  derived from it.

We also prove structural lemmas relating these predicates to `seq` and to the `cons`/`nil`
constructors.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Topology Stream'

/--
Inductive type `IsZero` / 归纳类型 `IsZero`

English:
inductive IsZero
  parameters: : {basis : Basis} -> MultiseriesExpansion basis -> Prop
  constructors (2):
    - const: {c : MultiseriesExpansion []} (hc : c.toReal = 0) : IsZero c
    - nil: {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

中文:
归纳类型 IsZero
  参数: : {basis : Basis} -> MultiseriesExpansion basis -> 命题
  构造子 (2 个):
    - const: {c : MultiseriesExpansion []} (hc : c.to实数 = 0) : IsZero c
    - nil: {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)
-/
inductive IsZero : {basis : Basis} -> MultiseriesExpansion basis -> Prop
| const {c : MultiseriesExpansion []} (hc : c.toReal = 0) : IsZero c
| nil {basis_hd} {basis_tl} (f) : @IsZero (basis_hd :: basis_tl) (mk .nil f)

namespace IsZero

@[simp]
/--
theorem `const_iff` / 定理 `const_iff`

English:
theorem const_iff
  given: {c : MultiseriesExpansion []}
  statement: IsZero c ↔ c.toReal = 0
  proof: by
  constructor <;> grind [IsZero]

@[simp]

中文:
定理 const_iff
  条件: {c : MultiseriesExpansion []}
  结论: IsZero c ↔ c.to实数 = 0
  证明: by
  constructor <;> grind [IsZero]

@[simp]

Depends on / 依赖: IsZero
-/
theorem const_iff {c : MultiseriesExpansion []} : IsZero c ↔ c.toReal = 0 := by
  constructor <;> grind [IsZero]

@[simp]
/--
theorem `iff_seq_eq_nil` / 定理 `iff_seq_eq_nil`

English:
theorem iff_seq_eq_nil
  given: {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  proof: by cases h; rw [mk_seq]
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]

中文:
定理 iff_seq_eq_nil
  条件: {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)}
  证明: by cases h; rw [mk_seq]
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]

Depends on / 依赖: IsZero, IsZero.nil, convert, mk_seq, ms.toFun
-/
theorem iff_seq_eq_nil {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    IsZero ms ↔ ms.seq = .nil where
  mp h := by cases h; rw [mk_seq]
  mpr h := by
    convert IsZero.nil ms.toFun
    simp [h]

/--
theorem `approximates_zero` / 定理 `approximates_zero`

English:
theorem approximates_zero
  statement: {basis : Basis} {ms : MultiseriesExpansion basis}
  proof: by
  cases h_zero with
  | const hc => simp [hc, Pi.zero_def]
  | nil => simpa using h_approx

中文:
定理 approximates_zero
  结论: {basis : Basis} {ms : MultiseriesExpansion basis}
  证明: by
  cases h_zero with
  | const hc => simp [hc, Pi.zero_def]
  | nil => simpa using h_approx

Depends on / 依赖: Pi.zero_def, h_approx, h_zero, zero_def
-/
theorem approximates_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_zero : IsZero ms) (h_approx : ms.Approximates) :
    ms.toFun =ᶠ[atTop] 0 := by
  cases h_zero with
  | const hc => simp [hc, Pi.zero_def]
  | nil => simpa using h_approx

/--
theorem `not_cons` / 定理 `not_cons`

English:
theorem not_cons
  statement: {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  simp

中文:
定理 not_cons
  结论: {basis_hd} {basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  simp
-/
theorem not_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : Real -> Real} :
    ¬ @IsZero (basis_hd :: basis_tl) (mk (.cons exp coef tl) f) := by
  simp

end IsZero

/--
Inductive type `Trimmed` / 归纳类型 `Trimmed`

English:
inductive Trimmed
  parameters: : {basis : Basis} -> MultiseriesExpansion basis -> Prop
  constructors (3):
    - const: {c : Real} : @Trimmed [] c
    - nil: {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
    - cons: {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : Real -> Real} (h_trimmed : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) : @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)

中文:
归纳类型 Trimmed
  参数: : {basis : Basis} -> MultiseriesExpansion basis -> 命题
  构造子 (3 个):
    - const: {c : 实数} : @Trimmed [] c
    - nil: {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
    - cons: {basis_hd} {basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : 实数 -> 实数} (h_trimmed : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) : @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)
-/
inductive Trimmed : {basis : Basis} -> MultiseriesExpansion basis -> Prop
| const {c : Real} : @Trimmed [] c
| nil {basis_hd} {basis_tl} {f} : @Trimmed (basis_hd :: basis_tl) (mk .nil f)
| cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  {tl : Multiseries basis_hd basis_tl} {f : Real -> Real} (h_trimmed : coef.Trimmed)
  (h_ne_zero : ¬ IsZero coef) :
  @Trimmed (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)

/--
Definition of `Multiseries.Trimmed` / `Multiseries.Trimmed` 的定义

English:
definition Multiseries.Trimmed
  signature: {basis_hd : Real -> Real} {basis_tl : Basis}
  body: (mk ms 0).Trimmed

中文:
定义 Multiseries.Trimmed
  签名: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  定义体: (mk ms 0).Trimmed

Depends on / 依赖: Trimmed
-/
def Multiseries.Trimmed {basis_hd : Real -> Real} {basis_tl : Basis}
    (ms : Multiseries basis_hd basis_tl) : Prop :=
  (mk ms 0).Trimmed

/--
theorem `trimmed_iff_seq_trimmed` / 定理 `trimmed_iff_seq_trimmed`

English:
theorem trimmed_iff_seq_trimmed
  statement: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | @cons _ _ exp coef tl _ h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (exp := exp) (tl := t

中文:
定理 trimmed_iff_seq_trimmed
  结论: {basis_hd : 实数 -> 实数} {basis_tl : Basis}
  证明: by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | @cons _ _ exp coef tl _ h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (exp := exp) (tl := t

Depends on / 依赖: Trimmed, Trimmed.cons, Trimmed.nil, and_true, convert, generalize, h_ne_zero, h_trimmed, ms.seq, ms.toFun, ms_eq_mk_iff
-/
theorem trimmed_iff_seq_trimmed {basis_hd : Real -> Real} {basis_tl : Basis}
    (ms : MultiseriesExpansion (basis_hd :: basis_tl)) :
    ms.Trimmed ↔ ms.seq.Trimmed where
  mp h := by
    cases h <;> constructor <;> grind
  mpr h := by
    generalize hs : ms.seq = s at h
    cases h with
    | nil =>
      convert Trimmed.nil (f := ms.toFun)
      simp [hs]
    | @cons _ _ exp coef tl _ h_trimmed h_ne_zero =>
      convert Trimmed.cons h_trimmed h_ne_zero (exp := exp) (tl := tl) (f := ms.toFun)
      simp only [ms_eq_mk_iff, hs, and_true]

namespace Multiseries.Trimmed

@[simp]
/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  given: {basis_hd} {basis_tl}
  proof: by
  constructor

中文:
定理 nil
  条件: {basis_hd} {basis_tl}
  证明: by
  constructor
-/
theorem nil {basis_hd} {basis_tl} :
    @Multiseries.Trimmed basis_hd basis_tl .nil := by
  constructor

/--
theorem `cons` / 定理 `cons`

English:
theorem cons
  statement: {basis_hd} {basis_tl} {exp : Real}
  proof: MultiseriesExpansion.Trimmed.cons h_coef h_ne_zero

中文:
定理 cons
  结论: {basis_hd} {basis_tl} {exp : 实数}
  证明: MultiseriesExpansion.Trimmed.cons h_coef h_ne_zero

Depends on / 依赖: MultiseriesExpansion, MultiseriesExpansion.Trimmed.cons, Trimmed, h_coef, h_ne_zero
-/
theorem cons {basis_hd} {basis_tl} {exp : Real}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h_coef : coef.Trimmed) (h_ne_zero : ¬ IsZero coef) :
    Multiseries.Trimmed (cons exp coef tl) :=
  MultiseriesExpansion.Trimmed.cons h_coef h_ne_zero

/--
theorem `elim_cons` / 定理 `elim_cons`

English:
theorem elim_cons
  statement: {basis_hd} {basis_tl} {exp : Real}
  proof: by
  generalize h_ms : Multiseries.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

中文:
定理 elim_cons
  结论: {basis_hd} {basis_tl} {exp : 实数}
  证明: by
  generalize h_ms : Multiseries.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

Depends on / 依赖: Multiseries, Multiseries.cons, generalize, h_ms, h_ne_zero, h_trimmed
-/
theorem elim_cons {basis_hd} {basis_tl} {exp : Real}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : Multiseries.Trimmed (.cons exp coef tl)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  generalize h_ms : Multiseries.cons exp coef tl = ms at h
  cases h with
  | nil => simp at h_ms
  | cons h_trimmed h_ne_zero =>
    simp at h_ms
    grind

end Multiseries.Trimmed

/--
theorem `elim_cons` / 定理 `elim_cons`

English:
theorem elim_cons
  statement: {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
  proof: by
  simp only [trimmed_iff_seq_trimmed, mk_seq] at h
  exact h.elim_cons

中文:
定理 elim_cons
  结论: {basis_hd} {basis_tl} {exp : 实数} {coef : MultiseriesExpansion basis_tl}
  证明: by
  simp only [trimmed_iff_seq_trimmed, mk_seq] at h
  exact h.elim_cons

Depends on / 依赖: elim_cons, h.elim_cons, mk_seq, trimmed_iff_seq_trimmed
-/
theorem elim_cons {basis_hd} {basis_tl} {exp : Real} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : Real -> Real}
    (h : Trimmed (mk (.cons exp coef tl) f)) :
    coef.Trimmed ∧ ¬ IsZero coef := by
  simp only [trimmed_iff_seq_trimmed, mk_seq] at h
  exact h.elim_cons

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
