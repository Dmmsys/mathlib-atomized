/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Order.CompleteLattice.Basic

/-! # Complete lattices and groups -/

public section

variable {α : Type*} {ι : Sort*} {κ : ι -> Sort*}
  [CompleteLattice α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
/--
lemma `iSup_mul_le` / 引理 `iSup_mul_le`

English:
lemma iSup_mul_le
  given: (u v : ι -> α)
  proof: iSup_le fun _ => mul_le_mul' (le_iSup ..) (le_iSup ..)

@[to_additive]

中文:
引理 iSup_mul_le
  条件: (u v : ι -> α)
  证明: iSup_le fun _ => mul_le_mul' (le_iSup ..) (le_iSup ..)

@[to_additive]

Depends on / 依赖: iSup_le, le_iSup, mul_le_mul
-/
lemma iSup_mul_le (u v : ι -> α) :
    ⨆ i, u i * v i <= (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun _ => mul_le_mul' (le_iSup ..) (le_iSup ..)

@[to_additive]
/--
lemma `le_iInf_mul` / 引理 `le_iInf_mul`

English:
lemma le_iInf_mul
  given: (u v : ι -> α)
  proof: iSup_mul_le (α := αᵒᵈ) ..

@[to_additive]

中文:
引理 le_iInf_mul
  条件: (u v : ι -> α)
  证明: iSup_mul_le (α := αᵒᵈ) ..

@[to_additive]

Depends on / 依赖: iSup_mul_le
-/
lemma le_iInf_mul (u v : ι -> α) :
    (⨅ i, u i) * ⨅ i, v i <= ⨅ i, u i * v i :=
  iSup_mul_le (α := αᵒᵈ) ..

@[to_additive]
/--
lemma `iSup₂_mul_le` / 引理 `iSup₂_mul_le`

English:
lemma iSup₂_mul_le
  given: (u v : (i : ι) -> κ i -> α)
  proof: by
  refine le_trans ?_ (iSup_mul_le ..)
  gcongr
  exact iSup_mul_le ..

@[to_additive]

中文:
引理 iSup₂_mul_le
  条件: (u v : (i : ι) -> κ i -> α)
  证明: by
  refine le_trans ?_ (iSup_mul_le ..)
  gcongr
  exact iSup_mul_le ..

@[to_additive]

Depends on / 依赖: iSup_mul_le, le_trans
-/
lemma iSup₂_mul_le (u v : (i : ι) -> κ i -> α) :
    ⨆ (i) (j), u i j * v i j <= (⨆ (i) (j), u i j) * ⨆ (i) (j), v i j := by
  refine le_trans ?_ (iSup_mul_le ..)
  gcongr
  exact iSup_mul_le ..

@[to_additive]
/--
lemma `le_iInf₂_mul` / 引理 `le_iInf₂_mul`

English:
lemma le_iInf₂_mul
  given: (u v : (i : ι) -> κ i -> α)
  proof: iSup₂_mul_le (α := αᵒᵈ) ..

中文:
引理 le_iInf₂_mul
  条件: (u v : (i : ι) -> κ i -> α)
  证明: iSup₂_mul_le (α := αᵒᵈ) ..
-/
lemma le_iInf₂_mul (u v : (i : ι) -> κ i -> α) :
    (⨅ (i) (j), u i j) * ⨅ (i) (j), v i j <= ⨅ (i) (j), u i j * v i j :=
  iSup₂_mul_le (α := αᵒᵈ) ..
