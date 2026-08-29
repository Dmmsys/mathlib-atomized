/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Type synonyms

This file provides two type synonyms for order theory:

* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: Type synonym of `α` to equip it with its colexicographic order. The precise meaning
  depends on the type we take the colex of. Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:

* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.
* `Colex`: `toColex : α → Colex α` and `ofColex : Colex α → α`.

## See also

This file is similar to `Mathlib.Algebra.Group.TypeTags.Basic`.
-/

@[expose] public section

assert_not_exists OrderDual

variable {α : Type*}

/-! ### Lexicographic order -/


/--
Definition of `Lex` / `Lex` 的定义

English:
definition Lex
  signature: (α : Type*)
  body: α

中文:
定义 Lex
  签名: (α : 类型)
  定义体: α
-/
def Lex (α : Type*) :=
  α

/-- `toLex` is the identity function to the `Lex` of a type. -/
@[match_pattern]
/--
Definition of `toLex` / `toLex` 的定义

English:
definition toLex
  signature: : α ≃ Lex α
  body: Equiv.refl _

中文:
定义 toLex
  签名: : α ≃ Lex α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toLex : α ≃ Lex α :=
  Equiv.refl _

/-- `ofLex` is the identity function from the `Lex` of a type. -/
@[match_pattern]
/--
Definition of `ofLex` / `ofLex` 的定义

English:
definition ofLex
  signature: : Lex α ≃ α
  body: Equiv.refl _

@[simp]

中文:
定义 ofLex
  签名: : Lex α ≃ α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofLex : Lex α ≃ α :=
  Equiv.refl _

@[simp]
/--
theorem `toLex_symm_eq` / 定理 `toLex_symm_eq`

English:
theorem toLex_symm_eq
  statement: (@toLex α).symm = ofLex
  proof: rfl

@[simp]

中文:
定理 toLex_symm_eq
  结论: (@toLex α).symm = ofLex
  证明: rfl

@[simp]
-/
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl

@[simp]
/--
theorem `ofLex_symm_eq` / 定理 `ofLex_symm_eq`

English:
theorem ofLex_symm_eq
  statement: (@ofLex α).symm = toLex
  proof: rfl

@[simp]

中文:
定理 ofLex_symm_eq
  结论: (@ofLex α).symm = toLex
  证明: rfl

@[simp]
-/
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl

@[simp]
/--
theorem `toLex_ofLex` / 定理 `toLex_ofLex`

English:
theorem toLex_ofLex
  given: (a : Lex α)
  statement: toLex (ofLex a) = a
  proof: rfl

@[simp]

中文:
定理 toLex_ofLex
  条件: (a : Lex α)
  结论: toLex (ofLex a) = a
  证明: rfl

@[simp]
-/
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl

@[simp]
/--
theorem `ofLex_toLex` / 定理 `ofLex_toLex`

English:
theorem ofLex_toLex
  given: (a : α)
  statement: ofLex (toLex a) = a
  proof: rfl

中文:
定理 ofLex_toLex
  条件: (a : α)
  结论: ofLex (toLex a) = a
  证明: rfl
-/
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl

/--
theorem `toLex_inj` / 定理 `toLex_inj`

English:
theorem toLex_inj
  given: {a b : α}
  statement: toLex a = toLex b ↔ a = b
  proof: by simp

中文:
定理 toLex_inj
  条件: {a b : α}
  结论: toLex a = toLex b ↔ a = b
  证明: by simp
-/
theorem toLex_inj {a b : α} : toLex a = toLex b ↔ a = b := by simp

/--
theorem `ofLex_inj` / 定理 `ofLex_inj`

English:
theorem ofLex_inj
  given: {a b : Lex α}
  statement: ofLex a = ofLex b ↔ a = b
  proof: by simp

中文:
定理 ofLex_inj
  条件: {a b : Lex α}
  结论: ofLex a = ofLex b ↔ a = b
  证明: by simp
-/
theorem ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b := by simp

instance (α : Type*) [BEq α] : BEq (Lex α) where
  beq a b := ofLex a == ofLex b

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Lex α) := inferInstanceAs LawfulBEq α
instance (α : Type*) [DecidableEq α] : DecidableEq (Lex α) := inferInstanceAs DecidableEq α

instance (α : Type*) [Inhabited α] : Inhabited (Lex α) := inferInstanceAs Inhabited α
instance (α : Type*) [Nonempty α] : Nonempty (Lex α) := inferInstanceAs Nonempty α
instance (α : Type*) [Nontrivial α] : Nontrivial (Lex α) := inferInstanceAs Nontrivial α
instance (α : Type*) [Unique α] : Unique (Lex α) := inferInstanceAs Unique α

instance {α γ} [H : CoeFun α γ] : CoeFun (Lex α) γ where
  coe f := H.coe (ofLex f)

/-- A recursor for `Lex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `Lex.rec` / `Lex.rec` 的定义

English:
definition Lex.rec
  signature: {β : Lex α -> Sort*} (h : forall a, β (toLex a))
  body: fun a => h (ofLex a)

中文:
定义 Lex.rec
  签名: {β : Lex α -> 类型层*} (h : 对任意 a, β (toLex a))
  定义体: fun a => h (ofLex a)
-/
protected def Lex.rec {β : Lex α -> Sort*} (h : forall a, β (toLex a)) : forall a, β a := fun a => h (ofLex a)

/--
lemma `Lex.forall` / 引理 `Lex.forall`

English:
lemma Lex.forall
  given: {p : Lex α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (toLex a)
  proof: Iff.rfl

中文:
引理 Lex.对任意
  条件: {p : Lex α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (toLex a)
  证明: Iff.rfl
-/
@[simp] lemma Lex.forall {p : Lex α -> Prop} : (forall a, p a) ↔ forall a, p (toLex a) := Iff.rfl
/--
lemma `Lex.exists` / 引理 `Lex.exists`

English:
lemma Lex.exists
  given: {p : Lex α -> Prop}
  statement: (exists a, p a) ↔ exists a, p (toLex a)
  proof: Iff.rfl

中文:
引理 Lex.存在
  条件: {p : Lex α -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (toLex a)
  证明: Iff.rfl
-/
@[simp] lemma Lex.exists {p : Lex α -> Prop} : (exists a, p a) ↔ exists a, p (toLex a) := Iff.rfl

/-! ### Colexicographic order -/


/--
Definition of `Colex` / `Colex` 的定义

English:
definition Colex
  signature: (α : Type*)
  body: α

中文:
定义 Colex
  签名: (α : 类型)
  定义体: α
-/
def Colex (α : Type*) :=
  α

/-- `toColex` is the identity function to the `Colex` of a type. -/
@[match_pattern]
/--
Definition of `toColex` / `toColex` 的定义

English:
definition toColex
  signature: : α ≃ Colex α
  body: Equiv.refl _

中文:
定义 toColex
  签名: : α ≃ Colex α
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toColex : α ≃ Colex α :=
  Equiv.refl _

/-- `ofColex` is the identity function from the `Colex` of a type. -/
@[match_pattern]
/--
Definition of `ofColex` / `ofColex` 的定义

English:
definition ofColex
  signature: : Colex α ≃ α
  body: Equiv.refl _

@[simp]

中文:
定义 ofColex
  签名: : Colex α ≃ α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofColex : Colex α ≃ α :=
  Equiv.refl _

@[simp]
/--
theorem `toColex_symm_eq` / 定理 `toColex_symm_eq`

English:
theorem toColex_symm_eq
  statement: (@toColex α).symm = ofColex
  proof: rfl

@[simp]

中文:
定理 toColex_symm_eq
  结论: (@toColex α).symm = ofColex
  证明: rfl

@[simp]
-/
theorem toColex_symm_eq : (@toColex α).symm = ofColex :=
  rfl

@[simp]
/--
theorem `ofColex_symm_eq` / 定理 `ofColex_symm_eq`

English:
theorem ofColex_symm_eq
  statement: (@ofColex α).symm = toColex
  proof: rfl

@[simp]

中文:
定理 ofColex_symm_eq
  结论: (@ofColex α).symm = toColex
  证明: rfl

@[simp]
-/
theorem ofColex_symm_eq : (@ofColex α).symm = toColex :=
  rfl

@[simp]
/--
theorem `toColex_ofColex` / 定理 `toColex_ofColex`

English:
theorem toColex_ofColex
  given: (a : Colex α)
  statement: toColex (ofColex a) = a
  proof: rfl

@[simp]

中文:
定理 toColex_ofColex
  条件: (a : Colex α)
  结论: toColex (ofColex a) = a
  证明: rfl

@[simp]
-/
theorem toColex_ofColex (a : Colex α) : toColex (ofColex a) = a :=
  rfl

@[simp]
/--
theorem `ofColex_toColex` / 定理 `ofColex_toColex`

English:
theorem ofColex_toColex
  given: (a : α)
  statement: ofColex (toColex a) = a
  proof: rfl

中文:
定理 ofColex_toColex
  条件: (a : α)
  结论: ofColex (toColex a) = a
  证明: rfl
-/
theorem ofColex_toColex (a : α) : ofColex (toColex a) = a :=
  rfl

/--
theorem `toColex_inj` / 定理 `toColex_inj`

English:
theorem toColex_inj
  given: {a b : α}
  statement: toColex a = toColex b ↔ a = b
  proof: by simp

中文:
定理 toColex_inj
  条件: {a b : α}
  结论: toColex a = toColex b ↔ a = b
  证明: by simp
-/
theorem toColex_inj {a b : α} : toColex a = toColex b ↔ a = b := by simp

/--
theorem `ofColex_inj` / 定理 `ofColex_inj`

English:
theorem ofColex_inj
  given: {a b : Colex α}
  statement: ofColex a = ofColex b ↔ a = b
  proof: by simp

中文:
定理 ofColex_inj
  条件: {a b : Colex α}
  结论: ofColex a = ofColex b ↔ a = b
  证明: by simp
-/
theorem ofColex_inj {a b : Colex α} : ofColex a = ofColex b ↔ a = b := by simp

instance (α : Type*) [BEq α] : BEq (Colex α) where
  beq a b := ofColex a == ofColex b

instance (α : Type*) [BEq α] [LawfulBEq α] : LawfulBEq (Colex α) := inferInstanceAs LawfulBEq α
instance (α : Type*) [DecidableEq α] : DecidableEq (Colex α) := inferInstanceAs DecidableEq α

instance (α : Type*) [Inhabited α] : Inhabited (Colex α) := inferInstanceAs Inhabited α
instance (α : Type*) [Nonempty α] : Nonempty (Colex α) := inferInstanceAs Nonempty α
instance (α : Type*) [Nontrivial α] : Nontrivial (Colex α) := inferInstanceAs Nontrivial α
instance (α : Type*) [Unique α] : Unique (Colex α) := inferInstanceAs Unique α

instance {α γ} [H : CoeFun α γ] : CoeFun (Colex α) γ where
  coe f := H.coe (ofColex f)

/-- A recursor for `Colex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `Colex.rec` / `Colex.rec` 的定义

English:
definition Colex.rec
  signature: {β : Colex α -> Sort*} (h : forall a, β (toColex a))
  body: fun a => h (ofColex a)

中文:
定义 Colex.rec
  签名: {β : Colex α -> 类型层*} (h : 对任意 a, β (toColex a))
  定义体: fun a => h (ofColex a)
-/
protected def Colex.rec {β : Colex α -> Sort*} (h : forall a, β (toColex a)) : forall a, β a :=
  fun a => h (ofColex a)

/--
lemma `Colex.forall` / 引理 `Colex.forall`

English:
lemma Colex.forall
  given: {p : Colex α -> Prop}
  statement: (forall a, p a) ↔ forall a, p (toColex a)
  proof: Iff.rfl

中文:
引理 Colex.对任意
  条件: {p : Colex α -> 命题}
  结论: (对任意 a, p a) ↔ 对任意 a, p (toColex a)
  证明: Iff.rfl
-/
@[simp] lemma Colex.forall {p : Colex α -> Prop} : (forall a, p a) ↔ forall a, p (toColex a) := Iff.rfl
/--
lemma `Colex.exists` / 引理 `Colex.exists`

English:
lemma Colex.exists
  given: {p : Colex α -> Prop}
  statement: (exists a, p a) ↔ exists a, p (toColex a)
  proof: Iff.rfl

中文:
引理 Colex.存在
  条件: {p : Colex α -> 命题}
  结论: (存在 a, p a) ↔ 存在 a, p (toColex a)
  证明: Iff.rfl
-/
@[simp] lemma Colex.exists {p : Colex α -> Prop} : (exists a, p a) ↔ exists a, p (toColex a) := Iff.rfl
