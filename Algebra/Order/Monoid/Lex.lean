/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Prod.Lex.Hom

/-!
# Order homomorphisms for products of ordered monoids

This file defines order homomorphisms for products of ordered monoids, for both the plain product
and the lexicographic product.

The product of ordered monoids `α × β` is an ordered monoid itself with both natural inclusions
and projections, making it the coproduct as well.

## TODO

Create the "OrdCommMon" category.

-/

@[expose] public section

namespace MonoidHom

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

@[to_additive]
/--
lemma `inl_mono` / 引理 `inl_mono`

English:
lemma inl_mono
  statement: Monotone (MonoidHom.inl α β)
  proof: fun _ _ => by simp

@[to_additive]

中文:
引理 inl_mono
  结论: Monotone (MonoidHom.inl α β)
  证明: fun _ _ => by simp

@[to_additive]
-/
lemma inl_mono : Monotone (MonoidHom.inl α β) :=
  fun _ _ => by simp

@[to_additive]
/--
lemma `inl_strictMono` / 引理 `inl_strictMono`

English:
lemma inl_strictMono
  statement: StrictMono (MonoidHom.inl α β)
  proof: fun _ _ => by simp

@[to_additive]

中文:
引理 inl_strictMono
  结论: StrictMono (MonoidHom.inl α β)
  证明: fun _ _ => by simp

@[to_additive]
-/
lemma inl_strictMono : StrictMono (MonoidHom.inl α β) :=
  fun _ _ => by simp

@[to_additive]
/--
lemma `inr_mono` / 引理 `inr_mono`

English:
lemma inr_mono
  statement: Monotone (MonoidHom.inr α β)
  proof: fun _ _ => by simp

@[to_additive]

中文:
引理 inr_mono
  结论: Monotone (MonoidHom.inr α β)
  证明: fun _ _ => by simp

@[to_additive]
-/
lemma inr_mono : Monotone (MonoidHom.inr α β) :=
  fun _ _ => by simp

@[to_additive]
/--
lemma `inr_strictMono` / 引理 `inr_strictMono`

English:
lemma inr_strictMono
  statement: StrictMono (MonoidHom.inr α β)
  proof: fun _ _ => by simp

@[to_additive]

中文:
引理 inr_strictMono
  结论: StrictMono (MonoidHom.inr α β)
  证明: fun _ _ => by simp

@[to_additive]
-/
lemma inr_strictMono : StrictMono (MonoidHom.inr α β) :=
  fun _ _ => by simp

@[to_additive]
/--
lemma `fst_mono` / 引理 `fst_mono`

English:
lemma fst_mono
  statement: Monotone (MonoidHom.fst α β)
  proof: fun _ _ => by simp +contextual [Prod.le_def]

@[to_additive]

中文:
引理 fst_mono
  结论: Monotone (MonoidHom.fst α β)
  证明: fun _ _ => by simp +contextual [Prod.le_def]

@[to_additive]

Depends on / 依赖: Prod.le_def, contextual, le_def
-/
lemma fst_mono : Monotone (MonoidHom.fst α β) :=
  fun _ _ => by simp +contextual [Prod.le_def]

@[to_additive]
/--
lemma `snd_mono` / 引理 `snd_mono`

English:
lemma snd_mono
  statement: Monotone (MonoidHom.snd α β)
  proof: fun _ _ => by simp +contextual [Prod.le_def]

中文:
引理 snd_mono
  结论: Monotone (MonoidHom.snd α β)
  证明: fun _ _ => by simp +contextual [Prod.le_def]

Depends on / 依赖: Prod.le_def, contextual, le_def
-/
lemma snd_mono : Monotone (MonoidHom.snd α β) :=
  fun _ _ => by simp +contextual [Prod.le_def]

end MonoidHom

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to M × N. -/]
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : α ->*o α × β where
  body: MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

中文:
定义 inl
  签名: : α ->*o α × β where
  定义体: MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

Depends on / 依赖: MonoidHom, MonoidHom.inl
-/
def inl : α ->*o α × β where
  __ := MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to M × N. -/]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : β ->*o α × β where
  body: MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

中文:
定义 inr
  签名: : β ->*o α × β where
  定义体: MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

Depends on / 依赖: MonoidHom, MonoidHom.inr
-/
def inr : β ->*o α × β where
  __ := MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to M. -/]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : α × β ->*o α where
  body: MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

中文:
定义 fst
  签名: : α × β ->*o α where
  定义体: MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

Depends on / 依赖: MonoidHom, MonoidHom.fst
-/
def fst : α × β ->*o α where
  __ := MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to N. -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : α × β ->*o β where
  body: MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

中文:
定义 snd
  签名: : α × β ->*o β where
  定义体: MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

Depends on / 依赖: MonoidHom, MonoidHom.snd
-/
def snd : α × β ->*o β where
  __ := MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to the lexicographic M ×ₗ N. -/]
/--
Definition of `inlₗ` / `inlₗ` 的定义

English:
definition inlₗ
  signature: : α ->*o α ×ₗ β where
  body: (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

中文:
定义 inlₗ
  签名: : α ->*o α ×ₗ β where
  定义体: (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

Depends on / 依赖: Prod.Lex.toLexOrderHom, toLexOrderHom
-/
def inlₗ : α ->*o α ×ₗ β where
  __ := (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to the lexicographic M ×ₗ N. -/]
/--
Definition of `inrₗ` / `inrₗ` 的定义

English:
definition inrₗ
  signature: : β ->*o (α ×ₗ β) where
  body: Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

中文:
定义 inrₗ
  签名: : β ->*o (α ×ₗ β) where
  定义体: Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

Depends on / 依赖: Prod.Lex.toLexOrderHom.comp, toLexOrderHom
-/
def inrₗ : β ->*o (α ×ₗ β) where
  __ := Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from the
lexicographic M ×ₗ N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from the lexicographic M ×ₗ N to M. -/]
/--
Definition of `fstₗ` / `fstₗ` 的定义

English:
definition fstₗ
  signature: : (α ×ₗ β) ->*o α where
  body: (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

@[to_additive (attr := simp)]

中文:
定义 fstₗ
  签名: : (α ×ₗ β) ->*o α where
  定义体: (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

@[to_additive (attr := simp)]
-/
def fstₗ : (α ×ₗ β) ->*o α where
  toFun p := (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

@[to_additive (attr := simp)]
/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: (fst α β).comp (inl α β) = .id α
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_comp_inl
  结论: (fst α β).comp (inl α β) = .id α
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_comp_inl : (fst α β).comp (inl α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `fstₗ_comp_inlₗ` / 定理 `fstₗ_comp_inlₗ`

English:
theorem fstₗ_comp_inlₗ
  statement: (fstₗ α β).comp (inlₗ α β) = .id α
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fstₗ_comp_inlₗ
  结论: (fstₗ α β).comp (inlₗ α β) = .id α
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fstₗ_comp_inlₗ : (fstₗ α β).comp (inlₗ α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: (snd α β).comp (inl α β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_comp_inl
  结论: (snd α β).comp (inl α β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_comp_inl : (snd α β).comp (inl α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: (fst α β).comp (inr α β) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_comp_inr
  结论: (fst α β).comp (inr α β) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_comp_inr : (fst α β).comp (inr α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: (snd α β).comp (inr α β) = .id β
  proof: rfl

@[to_additive]

中文:
定理 snd_comp_inr
  结论: (snd α β).comp (inr α β) = .id β
  证明: rfl

@[to_additive]
-/
theorem snd_comp_inr : (snd α β).comp (inr α β) = .id β :=
  rfl

@[to_additive]
/--
theorem `inl_mul_inr_eq_mk` / 定理 `inl_mul_inr_eq_mk`

English:
theorem inl_mul_inr_eq_mk
  given: (m : α) (n : β)
  statement: inl α β m * inr α β n = (m, n)
  proof: by
  simp

@[to_additive]

中文:
定理 inl_mul_inr_eq_mk
  条件: (m : α) (n : β)
  结论: inl α β m * inr α β n = (m, n)
  证明: by
  simp

@[to_additive]
-/
theorem inl_mul_inr_eq_mk (m : α) (n : β) : inl α β m * inr α β n = (m, n) := by
  simp

@[to_additive]
/--
theorem `inlₗ_mul_inrₗ_eq_toLex` / 定理 `inlₗ_mul_inrₗ_eq_toLex`

English:
theorem inlₗ_mul_inrₗ_eq_toLex
  given: (m : α) (n : β)
  statement: inlₗ α β m * inrₗ α β n = toLex (m, n)
  proof: by
  simp [← toLex_mul]

中文:
定理 inlₗ_mul_inrₗ_eq_toLex
  条件: (m : α) (n : β)
  结论: inlₗ α β m * inrₗ α β n = toLex (m, n)
  证明: by
  simp [← toLex_mul]

Depends on / 依赖: toLex_mul
-/
theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : inlₗ α β m * inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

variable {α β}

@[to_additive]
/--
theorem `commute_inl_inr` / 定理 `commute_inl_inr`

English:
theorem commute_inl_inr
  given: (m : α) (n : β)
  statement: Commute (inl α β m) (inr α β n)
  proof: Commute.prod (.one_right m) (.one_left n)

@[to_additive]

中文:
定理 commute_inl_inr
  条件: (m : α) (n : β)
  结论: Commute (inl α β m) (inr α β n)
  证明: Commute.prod (.one_right m) (.one_left n)

@[to_additive]

Depends on / 依赖: Commute, Commute.prod, one_left, one_right
-/
theorem commute_inl_inr (m : α) (n : β) : Commute (inl α β m) (inr α β n) :=
  Commute.prod (.one_right m) (.one_left n)

@[to_additive]
/--
theorem `commute_inlₗ_inrₗ` / 定理 `commute_inlₗ_inrₗ`

English:
theorem commute_inlₗ_inrₗ
  given: (m : α) (n : β)
  statement: Commute (inlₗ α β m) (inrₗ α β n)
  proof: Commute.prod (.one_right m) (.one_left n)

中文:
定理 commute_inlₗ_inrₗ
  条件: (m : α) (n : β)
  结论: Commute (inlₗ α β m) (inrₗ α β n)
  证明: Commute.prod (.one_right m) (.one_left n)

Depends on / 依赖: Commute, Commute.prod, one_left, one_right
-/
theorem commute_inlₗ_inrₗ (m : α) (n : β) : Commute (inlₗ α β m) (inrₗ α β n) :=
  Commute.prod (.one_right m) (.one_left n)

end OrderMonoidHom
