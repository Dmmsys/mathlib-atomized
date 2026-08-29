/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis

/-!
# Basic constructions for multiseries

## Main definitions

Let `[b₁, ..., bₙ]` be our basis.

* `const c` represents a constant multiseries `c • b₁⁰ ... bₙ⁰`.
  Then we define `zero` and `one` in terms of it.
* `monomial k` represents a monomial `bₖ`.
* `monomialRpow k r` represents a monomial `bₖʳ`.

For each construction, we provide two definitions: one for `Multiseries` and one for
`MultiseriesExpansion`. We then prove structural `simp`-lemmas describing their relationships with
`MultiseriesExpansion.seq` and `MultiseriesExpansion.toFun`. Finally, we prove that all
constructions are `Sorted` and `Approximates` their attached functions.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

open Filter Stream' Topology

mutual

/--
Definition of `Multiseries.const` / `Multiseries.const` 的定义

English:
definition Multiseries.const
  signature: (basis_hd : Real -> Real) (basis_tl : Basis) (c : Real)
  body: .cons 0 (const basis_tl c) .nil

中文:
定义 Multiseries.const
  签名: (basis_hd : 实数 -> 实数) (basis_tl : 基) (c : 实数)
  定义体: .cons 0 (const basis_tl c) .nil

Depends on / 依赖: basis_tl
-/
def Multiseries.const (basis_hd : Real -> Real) (basis_tl : Basis) (c : Real) :
    Multiseries basis_hd basis_tl :=
  .cons 0 (const basis_tl c) .nil

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (basis : Basis) (c : Real)
  body: match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (Multiseries.const basis_hd basis_tl c) (fun _ => c)

中文:
定义 const
  签名: (basis : 基) (c : 实数)
  定义体: match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (Multiseries.const basis_hd basis_tl c) (fun _ => c)

Depends on / 依赖: List.cons, Multiseries, Multiseries.const, basis_hd, basis_tl, ofReal
-/
def const (basis : Basis) (c : Real) : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal c
  | List.cons basis_hd basis_tl => mk (Multiseries.const basis_hd basis_tl c) (fun _ => c)

end

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: {basis : Basis}
  body: match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ => 0)

中文:
定义 zero
  签名: {basis : 基}
  定义体: match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ => 0)

Depends on / 依赖: List.cons, ofReal
-/
def zero {basis : Basis} : MultiseriesExpansion basis :=
  match basis with
  | [] => ofReal 0
  | List.cons _ _ => mk .nil (fun _ => 0)

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis : Basis} : Zero (MultiseriesExpansion basis) where
  zero := zero

/-- This instance is needed to create an instance for `AddCommMonoid (MultiseriesExpansion basis)`,
which is necessary for using the `abel` tactic in our proofs. -/
instance {basis_hd : Real -> Real} {basis_tl : Basis} : Zero (Multiseries basis_hd basis_tl) where
  zero := .nil

/--
Definition of `Multiseries.one` / `Multiseries.one` 的定义

English:
definition Multiseries.one
  signature: {basis_hd : Real -> Real} {basis_tl : Basis}
  body: Multiseries.const _ _ 1

中文:
定义 Multiseries.one
  签名: {basis_hd : 实数 -> 实数} {basis_tl : 基}
  定义体: Multiseries.const _ _ 1

Depends on / 依赖: Multiseries, Multiseries.const
-/
def Multiseries.one {basis_hd : Real -> Real} {basis_tl : Basis} : Multiseries basis_hd basis_tl :=
  Multiseries.const _ _ 1

/--
Definition of `one` / `one` 的定义

English:
definition one
  signature: {basis : Basis}
  body: const basis 1

mutual

中文:
定义 one
  签名: {basis : 基}
  定义体: const basis 1

mutual
-/
def one {basis : Basis} : MultiseriesExpansion basis :=
  const basis 1

mutual

/--
Definition of `Multiseries.monomialRpow` / `Multiseries.monomialRpow` 的定义

English:
definition Multiseries.monomialRpow
  signature: (basis_hd : Real -> Real) (basis_tl : Basis) (n : Nat) (r : Real)
  body: match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

中文:
定义 Multiseries.monomialRpow
  签名: (basis_hd : 实数 -> 实数) (basis_tl : 基) (n : 自然数) (r : 实数)
  定义体: match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

Depends on / 依赖: monomialRpow
-/
noncomputable def Multiseries.monomialRpow (basis_hd : Real -> Real) (basis_tl : Basis) (n : Nat) (r : Real) :
    Multiseries basis_hd basis_tl :=
  match n with
  | 0 => .cons r one .nil
  | m + 1 => .cons 0 (monomialRpow _ m r) .nil

/--
Definition of `monomialRpow` / `monomialRpow` 的定义

English:
definition monomialRpow
  signature: (basis : Basis) (n : Nat) (r : Real)
  body: match basis with
  | [] => default
  | List.cons basis_hd basis_tl =>
    mk (Multiseries.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

中文:
定义 monomialRpow
  签名: (basis : 基) (n : 自然数) (r : 实数)
  定义体: match basis with
  | [] => default
  | List.cons basis_hd basis_tl =>
    mk (Multiseries.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

Depends on / 依赖: List.cons, Multiseries, Multiseries.monomialRpow, basis_hd, basis_tl, monomialRpow
-/
noncomputable def monomialRpow (basis : Basis) (n : Nat) (r : Real) : MultiseriesExpansion basis :=
  match basis with
  | [] => default
  | List.cons basis_hd basis_tl =>
    mk (Multiseries.monomialRpow _ _ n r) ((basis_hd :: basis_tl)[n]! ^ r)

end

/--
Definition of `Multiseries.monomial` / `Multiseries.monomial` 的定义

English:
definition Multiseries.monomial
  signature: (basis_hd : Real -> Real) (basis_tl : Basis) (n : Nat)
  body: Multiseries.monomialRpow _ _ n 1

中文:
定义 Multiseries.monomial
  签名: (basis_hd : 实数 -> 实数) (basis_tl : 基) (n : 自然数)
  定义体: Multiseries.monomialRpow _ _ n 1

Depends on / 依赖: Multiseries, Multiseries.monomialRpow, monomialRpow
-/
noncomputable def Multiseries.monomial (basis_hd : Real -> Real) (basis_tl : Basis) (n : Nat) :
    Multiseries basis_hd basis_tl :=
  Multiseries.monomialRpow _ _ n 1

/--
Definition of `monomial` / `monomial` 的定义

English:
definition monomial
  signature: (basis : Basis) (n : Nat)
  body: monomialRpow _ n 1

中文:
定义 monomial
  签名: (basis : 基) (n : 自然数)
  定义体: monomialRpow _ n 1

Depends on / 依赖: monomialRpow
-/
noncomputable def monomial (basis : Basis) (n : Nat) : MultiseriesExpansion basis :=
  monomialRpow _ n 1

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  given: {basis_hd basis_tl}
  proof: rfl

@[simp]

中文:
定理 zero_def
  条件: {basis_hd basis_tl}
  证明: rfl

@[simp]
-/
theorem zero_def {basis_hd basis_tl} :
    (0 : MultiseriesExpansion (basis_hd :: basis_tl)) = mk .nil (fun _ => 0) :=
  rfl

@[simp]
/--
theorem `Multiseries.zero_def` / 定理 `Multiseries.zero_def`

English:
theorem Multiseries.zero_def
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: rfl

中文:
定理 Multiseries.zero_def
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: rfl
-/
theorem Multiseries.zero_def {basis_hd : Real -> Real} {basis_tl : Basis} :
    (0 : Multiseries basis_hd basis_tl) = .nil := rfl

/--
theorem `Multiseries.const_def` / 定理 `Multiseries.const_def`

English:
theorem Multiseries.const_def
  given: {basis_hd basis_tl} (c : Real)
  proof: by
  simp [Multiseries.const]

中文:
定理 Multiseries.const_def
  条件: {basis_hd basis_tl} (c : 实数)
  证明: by
  simp [Multiseries.const]

Depends on / 依赖: Multiseries, Multiseries.const
-/
theorem Multiseries.const_def {basis_hd basis_tl} (c : Real) :
    Multiseries.const basis_hd basis_tl c =
    Multiseries.cons 0 (MultiseriesExpansion.const basis_tl c) .nil := by
  simp [Multiseries.const]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `const_toFun'` / 定理 `const_toFun'`

English:
theorem const_toFun'
  given: {basis : Basis} {c : Real}
  statement: (const basis c).toFun = fun _ => c
  proof: by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]

中文:
定理 const_toFun'
  条件: {basis : 基} {c : 实数}
  结论: (const basis c).toFun = fun _ => c
  证明: by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]

Depends on / 依赖: List.cons, ofReal, toReal
-/
theorem const_toFun' {basis : Basis} {c : Real} : (const basis c).toFun = fun _ => c := by
  match basis with
  | [] => simp [const, ofReal, toReal]
  | List.cons _ _ => simp [const]

@[simp]
/--
theorem `const_seq` / 定理 `const_seq`

English:
theorem const_seq
  given: {basis_hd basis_tl} {c : Real}
  proof: by
  simp [const, Multiseries.const]

@[simp]

中文:
定理 const_seq
  条件: {basis_hd basis_tl} {c : 实数}
  证明: by
  simp [const, Multiseries.const]

@[simp]

Depends on / 依赖: Multiseries, Multiseries.const
-/
theorem const_seq {basis_hd basis_tl} {c : Real} :
    (const (basis_hd :: basis_tl) c).seq = Multiseries.const basis_hd basis_tl c := by
  simp [const, Multiseries.const]

@[simp]
/--
theorem `zero_toFun` / 定理 `zero_toFun`

English:
theorem zero_toFun
  given: {basis : Basis}
  statement: (@zero basis).toFun = 0
  proof: by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

中文:
定理 zero_toFun
  条件: {basis : 基}
  结论: (@zero basis).toFun = 0
  证明: by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

Depends on / 依赖: List.cons
-/
theorem zero_toFun {basis : Basis} : (@zero basis).toFun = 0 := by
  match basis with
  | [] => rfl
  | List.cons _ _ => rfl

/--
theorem `Multiseries.one_def` / 定理 `Multiseries.one_def`

English:
theorem Multiseries.one_def
  given: {basis_hd basis_tl}
  proof: by
  simp [Multiseries.one, Multiseries.const_def, MultiseriesExpansion.one]

@[simp]

中文:
定理 Multiseries.one_def
  条件: {basis_hd basis_tl}
  证明: by
  simp [Multiseries.one, Multiseries.const_def, MultiseriesExpansion.one]

@[simp]

Depends on / 依赖: Multiseries, Multiseries.const_def, Multiseries.one, MultiseriesExpansion, MultiseriesExpansion.one, const_def
-/
theorem Multiseries.one_def {basis_hd basis_tl} :
    @Multiseries.one basis_hd basis_tl = Multiseries.cons 0 MultiseriesExpansion.one .nil := by
  simp [Multiseries.one, Multiseries.const_def, MultiseriesExpansion.one]

@[simp]
/--
theorem `one_toFun` / 定理 `one_toFun`

English:
theorem one_toFun
  given: {basis : Basis}
  statement: (@one basis).toFun = 1
  proof: by
  simp [one]
  rfl

@[simp]

中文:
定理 one_toFun
  条件: {basis : 基}
  结论: (@one basis).toFun = 1
  证明: by
  simp [one]
  rfl

@[simp]
-/
theorem one_toFun {basis : Basis} : (@one basis).toFun = 1 := by
  simp [one]
  rfl

@[simp]
/--
theorem `one_seq` / 定理 `one_seq`

English:
theorem one_seq
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: by
  simp [one, Multiseries.one, const]

mutual

中文:
定理 one_seq
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: by
  simp [one, Multiseries.one, const]

mutual

Depends on / 依赖: Multiseries, Multiseries.one
-/
theorem one_seq {basis_hd : Real -> Real} {basis_tl : Basis} :
    (@one (basis_hd :: basis_tl)).seq = Multiseries.one := by
  simp [one, Multiseries.one, const]

mutual

/--
theorem `Multiseries.const_sorted` / 定理 `Multiseries.const_sorted`

English:
theorem Multiseries.const_sorted
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {c : Real}
  proof: by
  simp only [Multiseries.const]
  exact const_sorted.cons_nil

中文:
定理 Multiseries.const_sorted
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基} {c : 实数}
  证明: by
  simp only [Multiseries.const]
  exact const_sorted.cons_nil

Depends on / 依赖: Multiseries, Multiseries.const, cons_nil, const_sorted, const_sorted.cons_nil
-/
theorem Multiseries.const_sorted {basis_hd : Real -> Real} {basis_tl : Basis} {c : Real} :
    (Multiseries.const basis_hd basis_tl c).Sorted := by
  simp only [Multiseries.const]
  exact const_sorted.cons_nil

/--
theorem `const_sorted` / 定理 `const_sorted`

English:
theorem const_sorted
  given: {basis : Basis} {c : Real}
  proof: by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [const, sorted_iff_seq_sorted, mk_seq] using Multiseries.const_sorted

中文:
定理 const_sorted
  条件: {basis : 基} {c : 实数}
  证明: by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [const, sorted_iff_seq_sorted, mk_seq] using Multiseries.const_sorted

Depends on / 依赖: Multiseries, Multiseries.const_sorted, basis_hd, basis_tl, const_sorted, mk_seq, sorted_iff_seq_sorted
-/
theorem const_sorted {basis : Basis} {c : Real} :
    (const basis c).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [const, sorted_iff_seq_sorted, mk_seq] using Multiseries.const_sorted

end

/--
theorem `zero_sorted` / 定理 `zero_sorted`

English:
theorem zero_sorted
  given: {basis : Basis}
  statement: (0 : MultiseriesExpansion basis).Sorted
  proof: by
  cases basis with
  | nil => constructor
  | cons => apply Sorted.nil

中文:
定理 zero_sorted
  条件: {basis : 基}
  结论: (0 : MultiseriesExpansion basis).Sorted
  证明: by
  cases basis with
  | nil => constructor
  | cons => apply Sorted.nil

Depends on / 依赖: Sorted, Sorted.nil
-/
theorem zero_sorted {basis : Basis} : (0 : MultiseriesExpansion basis).Sorted := by
  cases basis with
  | nil => constructor
  | cons => apply Sorted.nil

/--
theorem `Multiseries.one_sorted` / 定理 `Multiseries.one_sorted`

English:
theorem Multiseries.one_sorted
  given: {basis_hd : Real -> Real} {basis_tl : Basis}
  proof: Multiseries.const_sorted

中文:
定理 Multiseries.one_sorted
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基}
  证明: Multiseries.const_sorted

Depends on / 依赖: Multiseries, Multiseries.const_sorted, const_sorted
-/
theorem Multiseries.one_sorted {basis_hd : Real -> Real} {basis_tl : Basis} :
    (Multiseries.one : Multiseries basis_hd basis_tl).Sorted :=
  Multiseries.const_sorted

/--
theorem `one_sorted` / 定理 `one_sorted`

English:
theorem one_sorted
  given: {basis : Basis}
  statement: one.Sorted (basis := basis)
  proof: const_sorted

中文:
定理 one_sorted
  条件: {basis : 基}
  结论: one.Sorted (basis := basis)
  证明: const_sorted
-/
theorem one_sorted {basis : Basis} : one.Sorted (basis := basis) :=
  const_sorted

/--
theorem `const_approximates` / 定理 `const_approximates`

English:
theorem const_approximates
  given: {c : Real} {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const, Multiseries.const]
    apply (const_approximates h_basis.tail).cons _ (by simp)
exact Majorized.const h_basis.tendsto_atTop (by simp)

中文:
定理 const_approximates
  条件: {c : 实数} {basis : 基} (h_basis : WellFormedBasis basis)
  证明: by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const, Multiseries.const]
    apply (const_approximates h_basis.tail).cons _ (by simp)
exact Majorized.const h_basis.tendsto_atTop (by simp)

Depends on / 依赖: Majorized, Majorized.const, Multiseries, Multiseries.const, basis_hd, basis_tl, const_approximates, h_basis, h_basis.tail, h_basis.tendsto_atTop, tendsto_atTop
-/
theorem const_approximates {c : Real} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [const, Multiseries.const]
    apply (const_approximates h_basis.tail).cons _ (by simp)
exact Majorized.const h_basis.tendsto_atTop (by simp)

/--
theorem `zero_approximates` / 定理 `zero_approximates`

English:
theorem zero_approximates
  given: {basis : Basis}
  proof: by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

中文:
定理 zero_approximates
  条件: {basis : 基}
  证明: by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

Depends on / 依赖: Approximates, Approximates.nil
-/
theorem zero_approximates {basis : Basis} :
    (@zero basis).Approximates := by
  cases basis with
  | nil => simp [zero]
  | cons => exact Approximates.nil (by rfl)

/--
theorem `one_approximates` / 定理 `one_approximates`

English:
theorem one_approximates
  given: {basis : Basis} (h_basis : WellFormedBasis basis)
  proof: const_approximates h_basis

@[simp]

中文:
定理 one_approximates
  条件: {basis : 基} (h_basis : WellFormedBasis basis)
  证明: const_approximates h_basis

@[simp]

Depends on / 依赖: const_approximates, h_basis
-/
theorem one_approximates {basis : Basis} (h_basis : WellFormedBasis basis) :
    (@one basis).Approximates :=
  const_approximates h_basis

@[simp]
/--
theorem `monomialRpow_toFun` / 定理 `monomialRpow_toFun`

English:
theorem monomialRpow_toFun
  given: {basis : Basis} {n : Fin (List.length basis)} {r : Real}
  proof: by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]

中文:
定理 monomialRpow_toFun
  条件: {basis : 基} {n : 有限集 (列表.length basis)} {r : 实数}
  证明: by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]

Depends on / 依赖: Fin.cases, basis_hd, basis_tl, monomialRpow
-/
theorem monomialRpow_toFun {basis : Basis} {n : Fin (List.length basis)} {r : Real} :
    (monomialRpow basis n r).toFun = basis[n] ^ r := by
  cases basis with
  | nil => grind
  | cons basis_hd basis_tl => cases n using Fin.cases <;> simp [monomialRpow]

@[simp]
/--
theorem `monomialRpow_seq` / 定理 `monomialRpow_seq`

English:
theorem monomialRpow_seq
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} {r : Real}
  proof: by
  simp [monomialRpow]

mutual

中文:
定理 monomialRpow_seq
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基} {n : 自然数} {r : 实数}
  证明: by
  simp [monomialRpow]

mutual

Depends on / 依赖: monomialRpow
-/
theorem monomialRpow_seq {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} {r : Real} :
    (monomialRpow (basis_hd :: basis_tl) n r).seq = Multiseries.monomialRpow _ _ n r := by
  simp [monomialRpow]

mutual

/--
theorem `Multiseries.monomialRpow_sorted` / 定理 `Multiseries.monomialRpow_sorted`

English:
theorem Multiseries.monomialRpow_sorted
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} {r : Real}
  proof: by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil const_sorted
  | succ m =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil monomialRpow_sorted

中文:
定理 Multiseries.monomialRpow_sorted
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基} {n : 自然数} {r : 实数}
  证明: by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil const_sorted
  | succ m =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil monomialRpow_sorted

Depends on / 依赖: Multiseries, Multiseries.monomialRpow, Sorted, Sorted.cons_nil, cons_nil, const_sorted, monomialRpow, monomialRpow_sorted
-/
theorem Multiseries.monomialRpow_sorted {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} {r : Real} :
    (@Multiseries.monomialRpow basis_hd basis_tl n r).Sorted := by
  cases n with
  | zero =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil const_sorted
  | succ m =>
    simp only [Multiseries.monomialRpow]
    exact Sorted.cons_nil monomialRpow_sorted

/--
theorem `monomialRpow_sorted` / 定理 `monomialRpow_sorted`

English:
theorem monomialRpow_sorted
  given: {basis : Basis} {n : Nat} {r : Real}
  proof: by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [sorted_iff_seq_sorted, monomialRpow_seq] using Multiseries.monomialRpow_sorted

中文:
定理 monomialRpow_sorted
  条件: {basis : 基} {n : 自然数} {r : 实数}
  证明: by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [sorted_iff_seq_sorted, monomialRpow_seq] using Multiseries.monomialRpow_sorted

Depends on / 依赖: Multiseries, Multiseries.monomialRpow_sorted, basis_hd, basis_tl, monomialRpow_seq, monomialRpow_sorted, sorted_iff_seq_sorted
-/
theorem monomialRpow_sorted {basis : Basis} {n : Nat} {r : Real} :
    (monomialRpow basis n r).Sorted := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simpa only [sorted_iff_seq_sorted, monomialRpow_seq] using Multiseries.monomialRpow_sorted

end

/--
theorem `monomialRpow_approximates` / 定理 `monomialRpow_approximates`

English:
theorem monomialRpow_approximates
  statement: {basis : Basis} {n : Fin (List.length basis)} {r : Real}
  proof: by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [List.length_cons, monomialRpow, Fin.is_lt, getElem!_pos]
    cases n using Fin.cases with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Multiseries.monomialRpow,
        List.getElem_cons_zero]
  

中文:
定理 monomialRpow_approximates
  结论: {basis : 基} {n : 有限集 (列表.length basis)} {r : 实数}
  证明: by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [List.length_cons, monomialRpow, Fin.is_lt, getElem!_pos]
    cases n using Fin.cases with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Multiseries.monomialRpow,
        List.getElem_cons_zero]
  

Depends on / 依赖: Fin.cases, Fin.coe_ofNat_eq_mod, Fin.is_lt, Fin.val_succ, List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons, Majorized, Majorized.self, Multiseries, Multiseries.monomialRpow, Nat.zero_mod, _pos, basis_hd, basis_tl, coe_ofNat_eq_mod, getElem, getElem_cons_succ, getElem_cons_zero, h_basi
-/
theorem monomialRpow_approximates {basis : Basis} {n : Fin (List.length basis)} {r : Real}
    (h_basis : WellFormedBasis basis) :
    (monomialRpow basis n r).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [List.length_cons, monomialRpow, Fin.is_lt, getElem!_pos]
    cases n using Fin.cases with
    | zero =>
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Multiseries.monomialRpow,
        List.getElem_cons_zero]
      apply (one_approximates h_basis.tail).cons _ (by simp)
exact Majorized.self h_basis.tendsto_atTop (by simp)
    | succ m =>
      simp only [Fin.val_succ, Multiseries.monomialRpow, List.getElem_cons_succ]
      apply (monomialRpow_approximates h_basis.tail).cons _ (by simp)
      apply h_basis.tail_pow_majorized_head (by simp)

@[simp]
/--
theorem `monomial_toFun` / 定理 `monomial_toFun`

English:
theorem monomial_toFun
  given: {basis : Basis} {n : Nat} (h : n < basis.length)
  proof: by
  let n' : Fin basis.length := ⟨n, h⟩
  conv_lhs => rw [show n = n'.val by simp [n']]
  convert! monomialRpow_toFun
  simp
  grind

中文:
定理 monomial_toFun
  条件: {basis : 基} {n : 自然数} (h : n < basis.length)
  证明: by
  let n' : Fin basis.length := ⟨n, h⟩
  conv_lhs => rw [show n = n'.val by simp [n']]
  convert! monomialRpow_toFun
  simp
  grind

Depends on / 依赖: basis.length, conv_lhs, convert, length, monomialRpow_toFun
-/
theorem monomial_toFun {basis : Basis} {n : Nat} (h : n < basis.length) :
    (monomial basis n).toFun = basis[n] := by
  let n' : Fin basis.length := ⟨n, h⟩
  conv_lhs => rw [show n = n'.val by simp [n']]
  convert! monomialRpow_toFun
  simp
  grind

/--
theorem `monomial_toFun'` / 定理 `monomial_toFun'`

English:
theorem monomial_toFun'
  given: {basis : Basis} {n : Fin basis.length}
  proof: by
  simp

@[simp]

中文:
定理 monomial_toFun'
  条件: {basis : 基} {n : 有限集 basis.length}
  证明: by
  simp

@[simp]
-/
theorem monomial_toFun' {basis : Basis} {n : Fin basis.length} :
    (monomial basis n).toFun = basis[n] := by
  simp

@[simp]
/--
theorem `monomial_seq` / 定理 `monomial_seq`

English:
theorem monomial_seq
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat}
  proof: monomialRpow_seq

中文:
定理 monomial_seq
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基} {n : 自然数}
  证明: monomialRpow_seq

Depends on / 依赖: monomialRpow_seq
-/
theorem monomial_seq {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} :
    (monomial (basis_hd :: basis_tl) n).seq = Multiseries.monomial _ _ n :=
  monomialRpow_seq

/--
theorem `Multiseries.monomial_sorted` / 定理 `Multiseries.monomial_sorted`

English:
theorem Multiseries.monomial_sorted
  given: {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat}
  proof: Multiseries.monomialRpow_sorted

中文:
定理 Multiseries.monomial_sorted
  条件: {basis_hd : 实数 -> 实数} {basis_tl : 基} {n : 自然数}
  证明: Multiseries.monomialRpow_sorted

Depends on / 依赖: Multiseries, Multiseries.monomialRpow_sorted, monomialRpow_sorted
-/
theorem Multiseries.monomial_sorted {basis_hd : Real -> Real} {basis_tl : Basis} {n : Nat} :
    (@Multiseries.monomial basis_hd basis_tl n).Sorted :=
  Multiseries.monomialRpow_sorted

/--
theorem `monomial_sorted` / 定理 `monomial_sorted`

English:
theorem monomial_sorted
  given: {basis : Basis} {n : Nat}
  statement: (monomial basis n).Sorted
  proof: monomialRpow_sorted

中文:
定理 monomial_sorted
  条件: {basis : 基} {n : 自然数}
  结论: (monomial basis n).Sorted
  证明: monomialRpow_sorted

Depends on / 依赖: monomialRpow_sorted
-/
theorem monomial_sorted {basis : Basis} {n : Nat} : (monomial basis n).Sorted :=
  monomialRpow_sorted

/--
theorem `monomial_approximates` / 定理 `monomial_approximates`

English:
theorem monomial_approximates
  statement: {basis : Basis} {n : Fin (List.length basis)}
  proof: monomialRpow_approximates h_basis

中文:
定理 monomial_approximates
  结论: {basis : 基} {n : 有限集 (列表.length basis)}
  证明: monomialRpow_approximates h_basis

Depends on / 依赖: h_basis, monomialRpow_approximates
-/
theorem monomial_approximates {basis : Basis} {n : Fin (List.length basis)}
    (h_basis : WellFormedBasis basis) : (monomial basis n).Approximates :=
  monomialRpow_approximates h_basis

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
