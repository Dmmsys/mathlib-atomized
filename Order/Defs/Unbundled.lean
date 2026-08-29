/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Defs
public import Batteries.Tactic.Alias
public import Mathlib.Tactic.ExtendDoc

import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

@[expose] public section

/-! ### Unbundled classes -/

/-- `IsIrrefl X r` means the binary relation `r` on `X` is irreflexive (that is, `r x x` never
holds). -/
@[deprecated Std.Irrefl (since := "2026-01-07")]
/--
Definition of `IsIrrefl` / `IsIrrefl` 的定义

English:
abbreviation IsIrrefl
  signature: (α : Sort*) (r : α -> α -> Prop)
  body: Std.Irrefl r

中文:
缩写 IsIrrefl
  签名: (α : Sort*) (r : α -> α -> 命题)
  定义体: Std.Irrefl r

Depends on / 依赖: Irrefl, Std.Irrefl
-/
abbrev IsIrrefl (α : Sort*) (r : α -> α -> Prop) : Prop := Std.Irrefl r

/-- `IsRefl X r` means the binary relation `r` on `X` is reflexive. -/
@[deprecated Std.Refl (since := "2026-01-08")]
/--
Definition of `IsRefl` / `IsRefl` 的定义

English:
abbreviation IsRefl
  signature: (α : Sort*) (r : α -> α -> Prop)
  body: Std.Refl r

中文:
缩写 IsRefl
  签名: (α : Sort*) (r : α -> α -> 命题)
  定义体: Std.Refl r

Depends on / 依赖: Std.Refl
-/
abbrev IsRefl (α : Sort*) (r : α -> α -> Prop) : Prop := Std.Refl r

/-- `IsAsymm X r` means that the binary relation `r` on `X` is asymmetric, that is,
`r a b → ¬ r b a`. -/
@[deprecated Std.Asymm (since := "2026-01-03")]
/--
Definition of `IsAsymm` / `IsAsymm` 的定义

English:
abbreviation IsAsymm
  signature: (α : Sort*) (r : α -> α -> Prop)
  body: Std.Asymm r

中文:
缩写 IsAsymm
  签名: (α : Sort*) (r : α -> α -> 命题)
  定义体: Std.Asymm r

Depends on / 依赖: Std.Asymm
-/
abbrev IsAsymm (α : Sort*) (r : α -> α -> Prop) : Prop := Std.Asymm r

/-- `IsAntisymm X r` means the binary relation `r` on `X` is antisymmetric. -/
@[deprecated Std.Antisymm (since := "2026-01-06")]
/--
Definition of `IsAntisymm` / `IsAntisymm` 的定义

English:
abbreviation IsAntisymm
  signature: (α : Sort*) (r : α -> α -> Prop)
  body: Std.Antisymm r

中文:
缩写 IsAntisymm
  签名: (α : Sort*) (r : α -> α -> 命题)
  定义体: Std.Antisymm r

Depends on / 依赖: Antisymm, Std.Antisymm
-/
abbrev IsAntisymm (α : Sort*) (r : α -> α -> Prop) : Prop := Std.Antisymm r

/--
Definition of `IsTrans` / `IsTrans` 的定义

English:
class IsTrans
  parameters: (α : Sort*) (r : α -> α -> Prop)
  axioms and operations (1):
    - trans : forall a b c, r a b -> r b c -> r a c

中文:
类 IsTrans
  参数: (α : Sort*) (r : α -> α -> 命题)
  公理与运算 (1 个):
    - trans : 对任意 a b c, r a b -> r b c -> r a c
-/
class IsTrans (α : Sort*) (r : α -> α -> Prop) : Prop where
  trans : forall a b c, r a b -> r b c -> r a c

instance {α : Sort*} {r : α -> α -> Prop} [IsTrans α r] : Trans r r r :=
  ⟨IsTrans.trans _ _ _⟩

instance (priority := 100) {α : Sort*} {r : α -> α -> Prop} [Trans r r r] : IsTrans α r :=
  ⟨fun _ _ _ => Trans.trans⟩

/-- `IsTotal X r` means that the binary relation `r` on `X` is total, that is, that for any
`x y : X` we have `r x y` or `r y x`. -/
@[deprecated Std.Total (since := "2026-01-09")]
/--
Definition of `IsTotal` / `IsTotal` 的定义

English:
abbreviation IsTotal
  signature: (α : Sort*) (r : α -> α -> Prop)
  body: Std.Total r

中文:
缩写 IsTotal
  签名: (α : Sort*) (r : α -> α -> 命题)
  定义体: Std.Total r

Depends on / 依赖: Std.Total
-/
abbrev IsTotal (α : Sort*) (r : α -> α -> Prop) : Prop := Std.Total r

/--
Definition of `IsPreorder` / `IsPreorder` 的定义

English:
class IsPreorder
  parameters: (α : Sort*) (r : α -> α -> Prop)
  extends: Std.Refl r, IsTrans α r
  (no additional axioms)

中文:
类 IsPreorder
  参数: (α : Sort*) (r : α -> α -> 命题)
  继承: Std.Refl r, IsTrans α r
  (无附加公理)
-/
class IsPreorder (α : Sort*) (r : α -> α -> Prop) : Prop extends Std.Refl r, IsTrans α r

/--
Definition of `IsPartialOrder` / `IsPartialOrder` 的定义

English:
class IsPartialOrder
  parameters: (α : Sort*) (r : α -> α -> Prop)
  extends: IsPreorder α r, Std.Antisymm r
  (no additional axioms)

中文:
类 IsPartialOrder
  参数: (α : Sort*) (r : α -> α -> 命题)
  继承: IsPreorder α r, Std.Antisymm r
  (无附加公理)
-/
class IsPartialOrder (α : Sort*) (r : α -> α -> Prop) : Prop extends IsPreorder α r, Std.Antisymm r

/--
Definition of `IsLinearOrder` / `IsLinearOrder` 的定义

English:
class IsLinearOrder
  parameters: (α : Sort*) (r : α -> α -> Prop)
  extends: IsPartialOrder α r, Std.Total r
  (no additional axioms)

中文:
类 IsLinearOrder
  参数: (α : Sort*) (r : α -> α -> 命题)
  继承: IsPartialOrder α r, Std.Total r
  (无附加公理)
-/
class IsLinearOrder (α : Sort*) (r : α -> α -> Prop) : Prop extends IsPartialOrder α r, Std.Total r

/--
Definition of `IsEquiv` / `IsEquiv` 的定义

English:
class IsEquiv
  parameters: (α : Sort*) (r : α -> α -> Prop)
  extends: IsPreorder α r, Std.Symm r
  (no additional axioms)

中文:
类 IsEquiv
  参数: (α : Sort*) (r : α -> α -> 命题)
  继承: IsPreorder α r, Std.Symm r
  (无附加公理)
-/
class IsEquiv (α : Sort*) (r : α -> α -> Prop) : Prop extends IsPreorder α r, Std.Symm r

/--
Definition of `IsStrictOrder` / `IsStrictOrder` 的定义

English:
class IsStrictOrder
  parameters: (α : Sort*) (r : α -> α -> Prop)
  extends: Std.Irrefl r, IsTrans α r
  (no additional axioms)

中文:
类 IsStrictOrder
  参数: (α : Sort*) (r : α -> α -> 命题)
  继承: Std.Irrefl r, IsTrans α r
  (无附加公理)
-/
class IsStrictOrder (α : Sort*) (r : α -> α -> Prop) : Prop extends Std.Irrefl r, IsTrans α r

/--
Definition of `IsStrictWeakOrder` / `IsStrictWeakOrder` 的定义

English:
class IsStrictWeakOrder
  parameters: (α : Sort*) (lt : α -> α -> Prop)
  extends: IsStrictOrder α lt
  axioms and operations (1):
    - incomp_trans : forall a b c, ¬lt a b ∧ ¬lt b a -> ¬lt b c ∧ ¬lt c b -> ¬lt a c ∧ ¬lt c a

中文:
类 IsStrictWeakOrder
  参数: (α : Sort*) (lt : α -> α -> 命题)
  继承: IsStrictOrder α lt
  公理与运算 (1 个):
    - incomp_trans : 对任意 a b c, ¬lt a b ∧ ¬lt b a -> ¬lt b c ∧ ¬lt c b -> ¬lt a c ∧ ¬lt c a
-/
class IsStrictWeakOrder (α : Sort*) (lt : α -> α -> Prop) : Prop extends IsStrictOrder α lt where
  incomp_trans : forall a b c, ¬lt a b ∧ ¬lt b a -> ¬lt b c ∧ ¬lt c b -> ¬lt a c ∧ ¬lt c a

/-- `IsTrichotomous X lt` means that the binary relation `lt` on `X` is trichotomous, that is,
either `lt a b` or `a = b` or `lt b a` for any `a` and `b`. -/
@[deprecated Std.Trichotomous (since := "2026-01-24")]
/--
Definition of `IsTrichotomous` / `IsTrichotomous` 的定义

English:
abbreviation IsTrichotomous
  signature: (α : Sort*) (lt : α -> α -> Prop)
  body: Std.Trichotomous lt

中文:
缩写 IsTrichotomous
  签名: (α : Sort*) (lt : α -> α -> 命题)
  定义体: Std.Trichotomous lt

Depends on / 依赖: Std.Trichotomous, Trichotomous
-/
abbrev IsTrichotomous (α : Sort*) (lt : α -> α -> Prop) : Prop := Std.Trichotomous lt

/--
Definition of `IsStrictTotalOrder` / `IsStrictTotalOrder` 的定义

English:
class IsStrictTotalOrder
  parameters: (α : Sort*) (lt : α -> α -> Prop)
  extends: Std.Trichotomous lt, IsStrictOrder α lt
  (no additional axioms)

中文:
类 IsStrictTotalOrder
  参数: (α : Sort*) (lt : α -> α -> 命题)
  继承: Std.Trichotomous lt, IsStrictOrder α lt
  (无附加公理)
-/
class IsStrictTotalOrder (α : Sort*) (lt : α -> α -> Prop) : Prop
    extends Std.Trichotomous lt, IsStrictOrder α lt

/--
theorem `Equivalence.of_isEquiv` / 定理 `Equivalence.of_isEquiv`

English:
theorem Equivalence.of_isEquiv
  given: {α : Sort*} (lt : α -> α -> Prop) [IsEquiv α lt]
  statement: Equivalence lt where
  proof: Std.Refl.refl; symm := Std.Symm.symm _ _; trans := IsTrans.trans _ _ _

中文:
定理 Equivalence.of_isEquiv
  条件: {α : Sort*} (lt : α -> α -> 命题) [IsEquiv α lt]
  结论: Equivalence lt where
  证明: Std.Refl.refl; symm := Std.Symm.symm _ _; trans := IsTrans.trans _ _ _

Depends on / 依赖: IsTrans, IsTrans.trans, Std.Refl.refl, Std.Symm.symm
-/
theorem Equivalence.of_isEquiv {α : Sort*} (lt : α -> α -> Prop) [IsEquiv α lt] : Equivalence lt where
  refl := Std.Refl.refl; symm := Std.Symm.symm _ _; trans := IsTrans.trans _ _ _

/--
theorem `IsEquiv.of_equivalence` / 定理 `IsEquiv.of_equivalence`

English:
theorem IsEquiv.of_equivalence
  given: {α : Sort*} {lt : α -> α -> Prop} (h : Equivalence lt)
  proof: h.refl; symm _ _ := h.symm; trans _ _ _ := h.trans

中文:
定理 IsEquiv.of_equivalence
  条件: {α : Sort*} {lt : α -> α -> 命题} (h : Equivalence lt)
  证明: h.refl; symm _ _ := h.symm; trans _ _ _ := h.trans

Depends on / 依赖: h.refl, h.symm, h.trans
-/
theorem IsEquiv.of_equivalence {α : Sort*} {lt : α -> α -> Prop} (h : Equivalence lt) :
    IsEquiv α lt where
  refl := h.refl; symm _ _ := h.symm; trans _ _ _ := h.trans

/--
theorem `equivalence_iff_isEquiv` / 定理 `equivalence_iff_isEquiv`

English:
theorem equivalence_iff_isEquiv
  given: {α : Sort*} (lt : α -> α -> Prop)
  statement: Equivalence lt ↔ IsEquiv α lt
  proof: ⟨.of_equivalence, fun _ => .of_isEquiv lt⟩

中文:
定理 equivalence_iff_isEquiv
  条件: {α : Sort*} (lt : α -> α -> 命题)
  结论: Equivalence lt ↔ IsEquiv α lt
  证明: ⟨.of_equivalence, fun _ => .of_isEquiv lt⟩

Depends on / 依赖: of_equivalence, of_isEquiv
-/
theorem equivalence_iff_isEquiv {α : Sort*} (lt : α -> α -> Prop) : Equivalence lt ↔ IsEquiv α lt :=
  ⟨.of_equivalence, fun _ => .of_isEquiv lt⟩

/--
Instance `eq_isEquiv` / 实例 `eq_isEquiv`

English:
instance eq_isEquiv
  signature: (α : Sort*)
  body: @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

中文:
实例 eq_isEquiv
  签名: (α : Sort*)
  定义体: @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

Depends on / 依赖: Eq.symm
-/
instance eq_isEquiv (α : Sort*) : IsEquiv α (· = ·) where
  symm := @Eq.symm _
  trans := @Eq.trans _
  refl := Eq.refl

instance (α : Sort*) : Std.Symm (α := α) Ne where
  symm _ _ := Ne.symm

/--
Instance `iff_isEquiv` / 实例 `iff_isEquiv`

English:
instance iff_isEquiv
  signature: : IsEquiv Prop Iff where
  body: @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl

中文:
实例 iff_isEquiv
  签名: : IsEquiv 命题 Iff where
  定义体: @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl

Depends on / 依赖: Iff.symm
-/
instance iff_isEquiv : IsEquiv Prop Iff where
  symm := @Iff.symm
  trans := @Iff.trans
  refl := @Iff.refl

section

variable {α : Sort*} {r : α -> α -> Prop} {a b c : α}

/-- Local notation for an arbitrary binary relation `r`. -/
local infixl:50 " ≺ " => r

/--
lemma `irrefl` / 引理 `irrefl`

English:
lemma irrefl
  given: [Std.Irrefl r] (a : α)
  statement: ¬a ≺ a
  proof: Std.Irrefl.irrefl a

中文:
引理 irrefl
  条件: [Std.Irrefl r] (a : α)
  结论: ¬a ≺ a
  证明: Std.Irrefl.irrefl a

Depends on / 依赖: Irrefl, Std.Irrefl.irrefl, irrefl
-/
lemma irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a := Std.Irrefl.irrefl a
/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: [Std.Refl r] (a : α)
  statement: a ≺ a
  proof: Std.Refl.refl a

中文:
引理 refl
  条件: [Std.Refl r] (a : α)
  结论: a ≺ a
  证明: Std.Refl.refl a

Depends on / 依赖: Std.Refl.refl
-/
lemma refl [Std.Refl r] (a : α) : a ≺ a := Std.Refl.refl a
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: [IsTrans α r]
  statement: a ≺ b -> b ≺ c -> a ≺ c
  proof: IsTrans.trans _ _ _

中文:
引理 trans
  条件: [IsTrans α r]
  结论: a ≺ b -> b ≺ c -> a ≺ c
  证明: IsTrans.trans _ _ _

Depends on / 依赖: IsTrans, IsTrans.trans
-/
lemma trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c := IsTrans.trans _ _ _
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: [Std.Symm r]
  statement: a ≺ b -> b ≺ a
  proof: Std.Symm.symm _ _

中文:
引理 symm
  条件: [Std.Symm r]
  结论: a ≺ b -> b ≺ a
  证明: Std.Symm.symm _ _

Depends on / 依赖: Std.Symm.symm
-/
lemma symm [Std.Symm r] : a ≺ b -> b ≺ a := Std.Symm.symm _ _
/--
lemma `antisymm` / 引理 `antisymm`

English:
lemma antisymm
  given: [Std.Antisymm r]
  statement: a ≺ b -> b ≺ a -> a = b
  proof: Std.Antisymm.antisymm _ _

中文:
引理 antisymm
  条件: [Std.Antisymm r]
  结论: a ≺ b -> b ≺ a -> a = b
  证明: Std.Antisymm.antisymm _ _

Depends on / 依赖: Antisymm, Std.Antisymm.antisymm, antisymm
-/
lemma antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b := Std.Antisymm.antisymm _ _
/--
lemma `asymm` / 引理 `asymm`

English:
lemma asymm
  given: [Std.Asymm r]
  statement: a ≺ b -> ¬b ≺ a
  proof: Std.Asymm.asymm _ _

中文:
引理 asymm
  条件: [Std.Asymm r]
  结论: a ≺ b -> ¬b ≺ a
  证明: Std.Asymm.asymm _ _

Depends on / 依赖: Std.Asymm.asymm
-/
lemma asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a := Std.Asymm.asymm _ _

/--
lemma `trichotomous` / 引理 `trichotomous`

English:
lemma trichotomous
  given: [Std.Trichotomous r]
  statement: forall a b : α, a ≺ b ∨ a = b ∨ b ≺ a
  proof: fun _ _ => Std.Trichotomous.rel_or_eq_or_rel_swap

中文:
引理 trichotomous
  条件: [Std.Trichotomous r]
  结论: 对任意 a b : α, a ≺ b ∨ a = b ∨ b ≺ a
  证明: fun _ _ => Std.Trichotomous.rel_or_eq_or_rel_swap

Depends on / 依赖: Std.Trichotomous.rel_or_eq_or_rel_swap, Trichotomous, rel_or_eq_or_rel_swap
-/
lemma trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b ∨ a = b ∨ b ≺ a :=
  fun _ _ => Std.Trichotomous.rel_or_eq_or_rel_swap

/--
lemma `irrefl_def` / 引理 `irrefl_def`

English:
lemma irrefl_def
  statement: Std.Irrefl r ↔ forall ⦃a⦄, ¬r a a
  proof: ⟨(·.irrefl), .mk⟩

中文:
引理 irrefl_def
  结论: Std.Irrefl r ↔ 对任意 ⦃a⦄, ¬r a a
  证明: ⟨(·.irrefl), .mk⟩

Depends on / 依赖: irrefl
-/
lemma irrefl_def : Std.Irrefl r ↔ forall ⦃a⦄, ¬r a a :=
  ⟨(·.irrefl), .mk⟩

/--
lemma `refl_def` / 引理 `refl_def`

English:
lemma refl_def
  statement: Std.Refl r ↔ forall ⦃a⦄, r a a
  proof: ⟨(·.refl), .mk⟩

中文:
引理 refl_def
  结论: Std.Refl r ↔ 对任意 ⦃a⦄, r a a
  证明: ⟨(·.refl), .mk⟩
-/
lemma refl_def : Std.Refl r ↔ forall ⦃a⦄, r a a :=
  ⟨(·.refl), .mk⟩

/--
lemma `isTrans_def` / 引理 `isTrans_def`

English:
lemma isTrans_def
  given: {α : Sort*} {r : α -> α -> Prop}
  statement: IsTrans α r ↔ forall ⦃a b c⦄, r a b -> r b c -> r a c
  proof: ⟨(·.trans), .mk⟩

中文:
引理 isTrans_def
  条件: {α : Sort*} {r : α -> α -> 命题}
  结论: IsTrans α r ↔ 对任意 ⦃a b c⦄, r a b -> r b c -> r a c
  证明: ⟨(·.trans), .mk⟩
-/
lemma isTrans_def {α : Sort*} {r : α -> α -> Prop} : IsTrans α r ↔ forall ⦃a b c⦄, r a b -> r b c -> r a c :=
  ⟨(·.trans), .mk⟩

/--
lemma `symm_def` / 引理 `symm_def`

English:
lemma symm_def
  statement: Std.Symm r ↔ forall ⦃a b⦄, r a b -> r b a
  proof: ⟨(·.symm), .mk⟩

中文:
引理 symm_def
  结论: Std.Symm r ↔ 对任意 ⦃a b⦄, r a b -> r b a
  证明: ⟨(·.symm), .mk⟩
-/
lemma symm_def : Std.Symm r ↔ forall ⦃a b⦄, r a b -> r b a :=
  ⟨(·.symm), .mk⟩

/--
lemma `antisymm_def` / 引理 `antisymm_def`

English:
lemma antisymm_def
  statement: Std.Antisymm r ↔ forall ⦃a b⦄, r a b -> r b a -> a = b
  proof: ⟨(·.antisymm), .mk⟩

中文:
引理 antisymm_def
  结论: Std.Antisymm r ↔ 对任意 ⦃a b⦄, r a b -> r b a -> a = b
  证明: ⟨(·.antisymm), .mk⟩

Depends on / 依赖: antisymm
-/
lemma antisymm_def : Std.Antisymm r ↔ forall ⦃a b⦄, r a b -> r b a -> a = b :=
  ⟨(·.antisymm), .mk⟩

/--
lemma `asymm_def` / 引理 `asymm_def`

English:
lemma asymm_def
  statement: Std.Asymm r ↔ forall ⦃a b⦄, r a b -> ¬r b a
  proof: ⟨(·.asymm), .mk⟩

中文:
引理 asymm_def
  结论: Std.Asymm r ↔ 对任意 ⦃a b⦄, r a b -> ¬r b a
  证明: ⟨(·.asymm), .mk⟩
-/
lemma asymm_def : Std.Asymm r ↔ forall ⦃a b⦄, r a b -> ¬r b a :=
  ⟨(·.asymm), .mk⟩

/--
lemma `total_def` / 引理 `total_def`

English:
lemma total_def
  statement: Std.Total r ↔ forall ⦃a b⦄, r a b ∨ r b a
  proof: ⟨(·.total), .mk⟩

中文:
引理 total_def
  结论: Std.Total r ↔ 对任意 ⦃a b⦄, r a b ∨ r b a
  证明: ⟨(·.total), .mk⟩
-/
lemma total_def : Std.Total r ↔ forall ⦃a b⦄, r a b ∨ r b a :=
  ⟨(·.total), .mk⟩

/--
lemma `trichotomous_def` / 引理 `trichotomous_def`

English:
lemma trichotomous_def
  statement: Std.Trichotomous r ↔ forall ⦃a b⦄, ¬r a b -> ¬r b a -> a = b
  proof: ⟨(·.trichotomous), .mk⟩

中文:
引理 trichotomous_def
  结论: Std.Trichotomous r ↔ 对任意 ⦃a b⦄, ¬r a b -> ¬r b a -> a = b
  证明: ⟨(·.trichotomous), .mk⟩

Depends on / 依赖: trichotomous
-/
lemma trichotomous_def : Std.Trichotomous r ↔ forall ⦃a b⦄, ¬r a b -> ¬r b a -> a = b :=
  ⟨(·.trichotomous), .mk⟩

instance (priority := 90) asymm_of_isTrans_of_irrefl [IsTrans α r] [Std.Irrefl r] : Std.Asymm r :=
  ⟨fun a _b h₁ h₂ => absurd (_root_.trans h₁ h₂) (irrefl a)⟩

/--
Instance `Std.Irrefl.decide` / 实例 `Std.Irrefl.decide`

English:
instance Std.Irrefl.decide
  signature: [DecidableRel r] [Std.Irrefl r]
  body: fun a => by simpa using irrefl a

中文:
实例 Std.Irrefl.decide
  签名: [DecidableRel r] [Std.Irrefl r]
  定义体: fun a => by simpa using irrefl a

Depends on / 依赖: irrefl
-/
instance Std.Irrefl.decide [DecidableRel r] [Std.Irrefl r] :
    Std.Irrefl (fun a b => decide (r a b) = true) where
  irrefl := fun a => by simpa using irrefl a

/--
Instance `Std.Refl.decide` / 实例 `Std.Refl.decide`

English:
instance Std.Refl.decide
  signature: [DecidableRel r] [Std.Refl r]
  body: fun a => by simpa using refl a

中文:
实例 Std.Refl.decide
  签名: [DecidableRel r] [Std.Refl r]
  定义体: fun a => by simpa using refl a
-/
instance Std.Refl.decide [DecidableRel r] [Std.Refl r] :
    Std.Refl (fun a b => decide (r a b) = true) where
  refl := fun a => by simpa using refl a

/--
Instance `IsTrans.decide` / 实例 `IsTrans.decide`

English:
instance IsTrans.decide
  signature: [DecidableRel r] [IsTrans α r]
  body: fun a b c => by simpa using trans a b c

中文:
实例 IsTrans.decide
  签名: [DecidableRel r] [IsTrans α r]
  定义体: fun a b c => by simpa using trans a b c
-/
instance IsTrans.decide [DecidableRel r] [IsTrans α r] :
    IsTrans α (fun a b => decide (r a b) = true) where
  trans := fun a b c => by simpa using trans a b c

/--
Instance `Std.Symm.decide` / 实例 `Std.Symm.decide`

English:
instance Std.Symm.decide
  signature: [DecidableRel r] [Std.Symm r]
  body: fun a b => by simpa using symm a b

中文:
实例 Std.Symm.decide
  签名: [DecidableRel r] [Std.Symm r]
  定义体: fun a b => by simpa using symm a b
-/
instance Std.Symm.decide [DecidableRel r] [Std.Symm r] :
    Std.Symm (fun a b => decide (r a b) = true) where
  symm := fun a b => by simpa using symm a b

/--
Instance `Std.Antisymm.decide` / 实例 `Std.Antisymm.decide`

English:
instance Std.Antisymm.decide
  signature: [DecidableRel r] [Std.Antisymm r]
  body: antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)

中文:
实例 Std.Antisymm.decide
  签名: [DecidableRel r] [Std.Antisymm r]
  定义体: antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)

Depends on / 依赖: antisymm
-/
instance Std.Antisymm.decide [DecidableRel r] [Std.Antisymm r] :
    Std.Antisymm (fun a b => decide (r a b) = true) where
  antisymm a b h₁ h₂ := antisymm (r := r) _ _ (by simpa using h₁) (by simpa using h₂)

/--
Instance `Std.Asymm.decide` / 实例 `Std.Asymm.decide`

English:
instance Std.Asymm.decide
  signature: [DecidableRel r] [Std.Asymm r]
  body: fun a b => by simpa using asymm a b

中文:
实例 Std.Asymm.decide
  签名: [DecidableRel r] [Std.Asymm r]
  定义体: fun a b => by simpa using asymm a b
-/
instance Std.Asymm.decide [DecidableRel r] [Std.Asymm r] :
    Std.Asymm (fun a b => decide (r a b) = true) where
  asymm := fun a b => by simpa using asymm a b

/--
Instance `Std.Total.decide` / 实例 `Std.Total.decide`

English:
instance Std.Total.decide
  signature: [DecidableRel r] [Std.Total r]
  body: fun a b => by simpa using total a b

中文:
实例 Std.Total.decide
  签名: [DecidableRel r] [Std.Total r]
  定义体: fun a b => by simpa using total a b
-/
instance Std.Total.decide [DecidableRel r] [Std.Total r] :
    Std.Total (fun a b => decide (r a b) = true) where
  total := fun a b => by simpa using total a b

/--
Instance `Std.Trichotomous.decide` / 实例 `Std.Trichotomous.decide`

English:
instance Std.Trichotomous.decide
  signature: [DecidableRel r] [Std.Trichotomous r]
  body: by simpa using trichotomous a b

中文:
实例 Std.Trichotomous.decide
  签名: [DecidableRel r] [Std.Trichotomous r]
  定义体: by simpa using trichotomous a b

Depends on / 依赖: trichotomous
-/
instance Std.Trichotomous.decide [DecidableRel r] [Std.Trichotomous r] :
    Std.Trichotomous (fun a b => decide (r a b) = true) where
  trichotomous a b := by simpa using trichotomous a b

variable (r)

/--
lemma `irrefl_of` / 引理 `irrefl_of`

English:
lemma irrefl_of
  given: [Std.Irrefl r] (a : α)
  statement: ¬a ≺ a
  proof: irrefl a

中文:
引理 irrefl_of
  条件: [Std.Irrefl r] (a : α)
  结论: ¬a ≺ a
  证明: irrefl a
-/
@[elab_without_expected_type] lemma irrefl_of [Std.Irrefl r] (a : α) : ¬a ≺ a := irrefl a
/--
lemma `refl_of` / 引理 `refl_of`

English:
lemma refl_of
  given: [Std.Refl r] (a : α)
  statement: a ≺ a
  proof: refl a

中文:
引理 refl_of
  条件: [Std.Refl r] (a : α)
  结论: a ≺ a
  证明: refl a
-/
@[elab_without_expected_type] lemma refl_of [Std.Refl r] (a : α) : a ≺ a := refl a
/--
lemma `trans_of` / 引理 `trans_of`

English:
lemma trans_of
  given: [IsTrans α r]
  statement: a ≺ b -> b ≺ c -> a ≺ c
  proof: _root_.trans

中文:
引理 trans_of
  条件: [IsTrans α r]
  结论: a ≺ b -> b ≺ c -> a ≺ c
  证明: _root_.trans
-/
@[elab_without_expected_type] lemma trans_of [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c := _root_.trans
/--
lemma `symm_of` / 引理 `symm_of`

English:
lemma symm_of
  given: [Std.Symm r]
  statement: a ≺ b -> b ≺ a
  proof: symm

中文:
引理 symm_of
  条件: [Std.Symm r]
  结论: a ≺ b -> b ≺ a
  证明: symm
-/
@[elab_without_expected_type] lemma symm_of [Std.Symm r] : a ≺ b -> b ≺ a := symm
/--
lemma `asymm_of` / 引理 `asymm_of`

English:
lemma asymm_of
  given: [Std.Asymm r]
  statement: a ≺ b -> ¬b ≺ a
  proof: asymm

@[elab_without_expected_type]

中文:
引理 asymm_of
  条件: [Std.Asymm r]
  结论: a ≺ b -> ¬b ≺ a
  证明: asymm

@[elab_without_expected_type]
-/
@[elab_without_expected_type] lemma asymm_of [Std.Asymm r] : a ≺ b -> ¬b ≺ a := asymm

@[elab_without_expected_type]
/--
lemma `total_of` / 引理 `total_of`

English:
lemma total_of
  given: [Std.Total r] (a b : α)
  statement: a ≺ b ∨ b ≺ a
  proof: Std.Total.total _ _

@[elab_without_expected_type]

中文:
引理 total_of
  条件: [Std.Total r] (a b : α)
  结论: a ≺ b ∨ b ≺ a
  证明: Std.Total.total _ _

@[elab_without_expected_type]

Depends on / 依赖: Std.Total.total
-/
lemma total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a := Std.Total.total _ _

@[elab_without_expected_type]
/--
lemma `trichotomous_of` / 引理 `trichotomous_of`

English:
lemma trichotomous_of
  given: [Std.Trichotomous r]
  statement: forall a b : α, a ≺ b ∨ a = b ∨ b ≺ a
  proof: trichotomous

中文:
引理 trichotomous_of
  条件: [Std.Trichotomous r]
  结论: 对任意 a b : α, a ≺ b ∨ a = b ∨ b ≺ a
  证明: trichotomous

Depends on / 依赖: trichotomous
-/
lemma trichotomous_of [Std.Trichotomous r] : forall a b : α, a ≺ b ∨ a = b ∨ b ≺ a := trichotomous

section

/-- `Std.Refl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Refl (since := "2026-03-27")]
/--
Definition of `Reflexive` / `Reflexive` 的定义

English:
definition Reflexive
  body: forall x, x ≺ x

中文:
定义 Reflexive
  定义体: forall x, x ≺ x
-/
def Reflexive := forall x, x ≺ x

/-- `Std.Symm` as a definition, suitable for use in proofs. -/
@[deprecated Std.Symm (since := "2026-06-10")]
/--
Definition of `Symmetric` / `Symmetric` 的定义

English:
definition Symmetric
  body: forall ⦃x y⦄, x ≺ y -> y ≺ x

中文:
定义 Symmetric
  定义体: forall ⦃x y⦄, x ≺ y -> y ≺ x
-/
def Symmetric := forall ⦃x y⦄, x ≺ y -> y ≺ x

/-- `IsTrans` as a definition, suitable for use in proofs. -/
@[deprecated IsTrans (since := "2026-02-20")]
/--
Definition of `Transitive` / `Transitive` 的定义

English:
definition Transitive
  body: forall ⦃x y z⦄, x ≺ y -> y ≺ z -> x ≺ z

中文:
定义 Transitive
  定义体: forall ⦃x y z⦄, x ≺ y -> y ≺ z -> x ≺ z
-/
def Transitive := forall ⦃x y z⦄, x ≺ y -> y ≺ z -> x ≺ z

/-- `Std.Irrefl` as a definition, suitable for use in proofs. -/
@[deprecated Std.Irrefl (since := "2026-02-12")]
/--
Definition of `Irreflexive` / `Irreflexive` 的定义

English:
definition Irreflexive
  body: forall x, ¬x ≺ x

中文:
定义 Irreflexive
  定义体: forall x, ¬x ≺ x
-/
def Irreflexive := forall x, ¬x ≺ x

/-- `Std.Antisymm` as a definition, suitable for use in proofs. -/
@[deprecated Std.Antisymm (since := "2026-02-09")]
/--
Definition of `AntiSymmetric` / `AntiSymmetric` 的定义

English:
definition AntiSymmetric
  body: forall ⦃x y⦄, x ≺ y -> y ≺ x -> x = y

中文:
定义 AntiSymmetric
  定义体: forall ⦃x y⦄, x ≺ y -> y ≺ x -> x = y
-/
def AntiSymmetric := forall ⦃x y⦄, x ≺ y -> y ≺ x -> x = y

/-- `Std.Total` as a definition, suitable for use in proofs. -/
@[deprecated Std.Total (since := "2026-02-10")]
/--
Definition of `Total` / `Total` 的定义

English:
definition Total
  body: forall x y, x ≺ y ∨ y ≺ x

中文:
定义 Total
  定义体: forall x y, x ≺ y ∨ y ≺ x
-/
def Total := forall x y, x ≺ y ∨ y ≺ x

/--
theorem `Equivalence.stdRefl` / 定理 `Equivalence.stdRefl`

English:
theorem Equivalence.stdRefl
  given: (h : Equivalence r)
  statement: Std.Refl r where
  proof: h.refl

@[deprecated (since := "2026-03-27")] alias Equivalence.reflexive := Equivalence.stdRefl

中文:
定理 Equivalence.stdRefl
  条件: (h : Equivalence r)
  结论: Std.Refl r where
  证明: h.refl

@[deprecated (since := "2026-03-27")] alias Equivalence.reflexive := Equivalence.stdRefl

Depends on / 依赖: h.refl
-/
theorem Equivalence.stdRefl (h : Equivalence r) : Std.Refl r where
  refl := h.refl

@[deprecated (since := "2026-03-27")] alias Equivalence.reflexive := Equivalence.stdRefl

/--
theorem `Equivalence.stdSymm` / 定理 `Equivalence.stdSymm`

English:
theorem Equivalence.stdSymm
  given: (h : Equivalence r)
  statement: Std.Symm r where
  proof: h.symm

@[deprecated (since := "2026-06-10")] alias Equivalence.symmetric := Equivalence.stdSymm

中文:
定理 Equivalence.stdSymm
  条件: (h : Equivalence r)
  结论: Std.Symm r where
  证明: h.symm

@[deprecated (since := "2026-06-10")] alias Equivalence.symmetric := Equivalence.stdSymm

Depends on / 依赖: h.symm
-/
theorem Equivalence.stdSymm (h : Equivalence r) : Std.Symm r where
  symm _ _ := h.symm

@[deprecated (since := "2026-06-10")] alias Equivalence.symmetric := Equivalence.stdSymm

/--
theorem `Equivalence.isTrans` / 定理 `Equivalence.isTrans`

English:
theorem Equivalence.isTrans
  given: (h : Equivalence r)
  statement: IsTrans α r
  proof: ⟨fun _ _ _ => h.trans⟩

@[deprecated (since := "2026-02-20")] alias Equivalence.transitive := Equivalence.isTrans

中文:
定理 Equivalence.isTrans
  条件: (h : Equivalence r)
  结论: IsTrans α r
  证明: ⟨fun _ _ _ => h.trans⟩

@[deprecated (since := "2026-02-20")] alias Equivalence.transitive := Equivalence.isTrans

Depends on / 依赖: h.trans
-/
theorem Equivalence.isTrans (h : Equivalence r) : IsTrans α r :=
  ⟨fun _ _ _ => h.trans⟩

@[deprecated (since := "2026-02-20")] alias Equivalence.transitive := Equivalence.isTrans

/--
theorem `Equivalence.isEquiv` / 定理 `Equivalence.isEquiv`

English:
theorem Equivalence.isEquiv
  given: (h : Equivalence r)
  statement: IsEquiv α r
  proof: have := h.stdRefl
  have := h.stdSymm
  have := h.isTrans
  {}

中文:
定理 Equivalence.isEquiv
  条件: (h : Equivalence r)
  结论: IsEquiv α r
  证明: have := h.stdRefl
  have := h.stdSymm
  have := h.isTrans
  {}

Depends on / 依赖: h.isTrans, h.stdRefl, h.stdSymm, isTrans, stdRefl, stdSymm
-/
theorem Equivalence.isEquiv (h : Equivalence r) : IsEquiv α r :=
  have := h.stdRefl
  have := h.stdSymm
  have := h.isTrans
  {}

variable {β : Sort*} (r : β -> β -> Prop) (f : α -> β)

/--
Instance `InvImage.isTrans` / 实例 `InvImage.isTrans`

English:
instance InvImage.isTrans
  signature: [IsTrans β r]
  body: ⟨fun _ _ _ => trans_of r⟩

@[deprecated (since := "2026-02-20")] alias InvImage.trans := InvImage.isTrans

中文:
实例 InvImage.isTrans
  签名: [IsTrans β r]
  定义体: ⟨fun _ _ _ => trans_of r⟩

@[deprecated (since := "2026-02-20")] alias InvImage.trans := InvImage.isTrans

Depends on / 依赖: trans_of
-/
instance InvImage.isTrans [IsTrans β r] : IsTrans α (InvImage r f) :=
  ⟨fun _ _ _ => trans_of r⟩

@[deprecated (since := "2026-02-20")] alias InvImage.trans := InvImage.isTrans

/--
Instance `InvImage.irrefl` / 实例 `InvImage.irrefl`

English:
instance InvImage.irrefl
  signature: [Std.Irrefl r]
  body: ⟨fun (a : α) (h₁ : InvImage r f a a) => irrefl_of r (f a) h₁⟩

@[deprecated (since := "2026-02-12")] alias InvImage.irreflexive := InvImage.irrefl

中文:
实例 InvImage.irrefl
  签名: [Std.Irrefl r]
  定义体: ⟨fun (a : α) (h₁ : InvImage r f a a) => irrefl_of r (f a) h₁⟩

@[deprecated (since := "2026-02-12")] alias InvImage.irreflexive := InvImage.irrefl

Depends on / 依赖: InvImage, irrefl_of
-/
instance InvImage.irrefl [Std.Irrefl r] : Std.Irrefl (InvImage r f) :=
  ⟨fun (a : α) (h₁ : InvImage r f a a) => irrefl_of r (f a) h₁⟩

@[deprecated (since := "2026-02-12")] alias InvImage.irreflexive := InvImage.irrefl

end

end

/-! ### Minimal and maximal -/

section LE

variable {α : Type*} [LE α] {P : α -> Prop} {x y : α}

/-- `Minimal P x` means that `x` is a minimal element satisfying `P`. -/
@[to_dual /-- `Maximal P x` means that `x` is a maximal element satisfying `P`. -/]
/--
Definition of `Minimal` / `Minimal` 的定义

English:
definition Minimal
  signature: (P : α -> Prop) (x : α)
  body: P x ∧ forall ⦃y⦄, P y -> y <= x -> x <= y

@[to_dual]

中文:
定义 Minimal
  签名: (P : α -> 命题) (x : α)
  定义体: P x ∧ forall ⦃y⦄, P y -> y <= x -> x <= y

@[to_dual]
-/
def Minimal (P : α -> Prop) (x : α) : Prop := P x ∧ forall ⦃y⦄, P y -> y <= x -> x <= y

@[to_dual]
/--
lemma `Minimal.prop` / 引理 `Minimal.prop`

English:
lemma Minimal.prop
  given: (h : Minimal P x)
  statement: P x
  proof: h.1

@[to_dual le_of_ge] -- TODO: improve this naming

中文:
引理 Minimal.prop
  条件: (h : Minimal P x)
  结论: P x
  证明: h.1

@[to_dual le_of_ge] -- TODO: improve this naming
-/
lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1

@[to_dual le_of_ge] -- TODO: improve this naming
/--
lemma `Minimal.le_of_le` / 引理 `Minimal.le_of_le`

English:
lemma Minimal.le_of_le
  given: (h : Minimal P x) (hy : P y) (hle : y <= x)
  statement: x <= y
  proof: h.2 hy hle

中文:
引理 Minimal.le_of_le
  条件: (h : Minimal P x) (hy : P y) (hle : y <= x)
  结论: x <= y
  证明: h.2 hy hle
-/
lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y <= x) : x <= y :=
  h.2 hy hle

end LE

section LE
variable {ι : Sort*} {α : Type*} [LE α] {P : ι -> Prop} {f : ι -> α} {i j : ι}

/-- `MinimalFor P f i` means that `f i` is minimal over all `i` satisfying `P`. -/
@[to_dual /-- `MaximalFor P f i` means that `f i` is maximal over all `i` satisfying `P`. -/]
/--
Definition of `MinimalFor` / `MinimalFor` 的定义

English:
definition MinimalFor
  signature: (P : ι -> Prop) (f : ι -> α) (i : ι)
  body: P i ∧ forall ⦃j⦄, P j -> f j <= f i -> f i <= f j

@[to_dual]

中文:
定义 MinimalFor
  签名: (P : ι -> 命题) (f : ι -> α) (i : ι)
  定义体: P i ∧ forall ⦃j⦄, P j -> f j <= f i -> f i <= f j

@[to_dual]
-/
def MinimalFor (P : ι -> Prop) (f : ι -> α) (i : ι) : Prop := P i ∧ forall ⦃j⦄, P j -> f j <= f i -> f i <= f j

@[to_dual]
/--
lemma `MinimalFor.prop` / 引理 `MinimalFor.prop`

English:
lemma MinimalFor.prop
  given: (h : MinimalFor P f i)
  statement: P i
  proof: h.1

@[to_dual]

中文:
引理 MinimalFor.prop
  条件: (h : MinimalFor P f i)
  结论: P i
  证明: h.1

@[to_dual]
-/
lemma MinimalFor.prop (h : MinimalFor P f i) : P i := h.1

@[to_dual]
/--
lemma `MinimalFor.le_of_le` / 引理 `MinimalFor.le_of_le`

English:
lemma MinimalFor.le_of_le
  given: (h : MinimalFor P f i) (hj : P j) (hji : f j <= f i)
  statement: f i <= f j
  proof: h.2 hj hji

中文:
引理 MinimalFor.le_of_le
  条件: (h : MinimalFor P f i) (hj : P j) (hji : f j <= f i)
  结论: f i <= f j
  证明: h.2 hj hji
-/
lemma MinimalFor.le_of_le (h : MinimalFor P f i) (hj : P j) (hji : f j <= f i) : f i <= f j :=
  h.2 hj hji

end LE

/-! ### Upper and lower sets -/

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
@[to_dual /-- A lower set in an order `α` is a set such that any element less than one of its
members is also a member. Also called down-set, downward-closed set. -/]
/--
Definition of `IsUpperSet` / `IsUpperSet` 的定义

English:
definition IsUpperSet
  signature: {α : Type*} [LE α] (s : Set α)
  body: forall ⦃a b : α⦄, a <= b -> a in s -> b in s

@[inherit_doc IsUpperSet]

中文:
定义 IsUpperSet
  签名: {α : 类型} [LE α] (s : Set α)
  定义体: forall ⦃a b : α⦄, a <= b -> a in s -> b in s

@[inherit_doc IsUpperSet]
-/
def IsUpperSet {α : Type*} [LE α] (s : Set α) : Prop :=
  forall ⦃a b : α⦄, a <= b -> a in s -> b in s

@[inherit_doc IsUpperSet]
/--
Definition of `UpperSet` / `UpperSet` 的定义

English:
structure UpperSet
  parameters: (α : Type*) [LE α]
  axioms and operations (2):
    - carrier : Set α
    - upper' : IsUpperSet carrier

中文:
结构 UpperSet
  参数: (α : 类型) [LE α]
  公理与运算 (2 个):
    - carrier : Set α
    - upper' : IsUpperSet carrier
-/
structure UpperSet (α : Type*) [LE α] where
  /-- The carrier of an `UpperSet`. -/
  carrier : Set α
  /-- The carrier of an `UpperSet` is an upper set. -/
  upper' : IsUpperSet carrier

extend_docs UpperSet before "The type of upper sets of an order."

@[inherit_doc IsLowerSet, to_dual]
/--
Definition of `LowerSet` / `LowerSet` 的定义

English:
structure LowerSet
  parameters: (α : Type*) [LE α]
  axioms and operations (2):
    - carrier : Set α
    - lower' : IsLowerSet carrier

中文:
结构 LowerSet
  参数: (α : 类型) [LE α]
  公理与运算 (2 个):
    - carrier : Set α
    - lower' : IsLowerSet carrier
-/
structure LowerSet (α : Type*) [LE α] where
  /-- The carrier of a `LowerSet`. -/
  carrier : Set α
  /-- The carrier of a `LowerSet` is a lower set. -/
  lower' : IsLowerSet carrier

extend_docs LowerSet before "The type of lower sets of an order."

/-- An upper set relative to a predicate `P` is a set such that all elements satisfy `P` and
any element greater than one of its members and satisfying `P` is also a member. -/
@[to_dual /-- A lower set relative to a predicate `P` is a set such that all elements satisfy `P`
and any element less than one of its members and satisfying `P` is also a member. -/]
/--
Definition of `IsRelUpperSet` / `IsRelUpperSet` 的定义

English:
definition IsRelUpperSet
  signature: {α : Type*} [LE α] (s : Set α) (P : α -> Prop)
  body: forall ⦃a : α⦄, a in s -> P a ∧ forall ⦃b : α⦄, a <= b -> P b -> b in s

@[inherit_doc IsRelUpperSet]

中文:
定义 IsRelUpperSet
  签名: {α : 类型} [LE α] (s : Set α) (P : α -> 命题)
  定义体: forall ⦃a : α⦄, a in s -> P a ∧ forall ⦃b : α⦄, a <= b -> P b -> b in s

@[inherit_doc IsRelUpperSet]
-/
def IsRelUpperSet {α : Type*} [LE α] (s : Set α) (P : α -> Prop) : Prop :=
  forall ⦃a : α⦄, a in s -> P a ∧ forall ⦃b : α⦄, a <= b -> P b -> b in s

@[inherit_doc IsRelUpperSet]
/--
Definition of `RelUpperSet` / `RelUpperSet` 的定义

English:
structure RelUpperSet
  parameters: {α : Type*} [LE α] (P : α -> Prop)
  axioms and operations (2):
    - carrier : Set α
    - isRelUpperSet' : IsRelUpperSet carrier P

中文:
结构 RelUpperSet
  参数: {α : 类型} [LE α] (P : α -> 命题)
  公理与运算 (2 个):
    - carrier : Set α
    - isRelUpperSet' : IsRelUpperSet carrier P
-/
structure RelUpperSet {α : Type*} [LE α] (P : α -> Prop) where
  /-- The carrier of a `RelUpperSet`. -/
  carrier : Set α
  /-- The carrier of a `RelUpperSet` is an upper set relative to `P`.

  Do NOT use directly. Please use `RelUpperSet.isRelUpperSet` instead. -/
  isRelUpperSet' : IsRelUpperSet carrier P

extend_docs RelUpperSet before "The type of upper sets of an order relative to `P`."

@[inherit_doc IsRelLowerSet, to_dual]
/--
Definition of `RelLowerSet` / `RelLowerSet` 的定义

English:
structure RelLowerSet
  parameters: {α : Type*} [LE α] (P : α -> Prop)
  axioms and operations (2):
    - carrier : Set α
    - isRelLowerSet' : IsRelLowerSet carrier P

中文:
结构 RelLowerSet
  参数: {α : 类型} [LE α] (P : α -> 命题)
  公理与运算 (2 个):
    - carrier : Set α
    - isRelLowerSet' : IsRelLowerSet carrier P
-/
structure RelLowerSet {α : Type*} [LE α] (P : α -> Prop) where
  /-- The carrier of a `RelLowerSet`. -/
  carrier : Set α
  /-- The carrier of a `RelLowerSet` is a lower set relative to `P`.

  Do NOT use directly. Please use `RelLowerSet.isRelLowerSet` instead. -/
  isRelLowerSet' : IsRelLowerSet carrier P

extend_docs RelLowerSet before "The type of lower sets of an order relative to `P`."

variable {α β : Sort*} {r : α -> α -> Prop} {s : β -> β -> Prop}

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: [Std.Refl r]
  statement: forall {a b}, a = b -> r a b

中文:
定理 of_eq
  条件: [Std.Refl r]
  结论: 对任意 {a b}, a = b -> r a b
-/
theorem of_eq [Std.Refl r] : forall {a b}, a = b -> r a b
  | _, _, .refl _ => refl _

/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: [Std.Symm r] {a b : α}
  statement: r a b ↔ r b a
  proof: ⟨symm, symm⟩

中文:
定理 comm
  条件: [Std.Symm r] {a b : α}
  结论: r a b ↔ r b a
  证明: ⟨symm, symm⟩
-/
theorem comm [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  ⟨symm, symm⟩

/--
theorem `antisymm'` / 定理 `antisymm'`

English:
theorem antisymm'
  given: [Std.Antisymm r] {a b : α}
  statement: r a b -> r b a -> b = a
  proof: fun h h' => antisymm h' h

中文:
定理 antisymm'
  条件: [Std.Antisymm r] {a b : α}
  结论: r a b -> r b a -> b = a
  证明: fun h h' => antisymm h' h

Depends on / 依赖: antisymm
-/
theorem antisymm' [Std.Antisymm r] {a b : α} : r a b -> r b a -> b = a := fun h h' => antisymm h' h

/--
theorem `antisymm_iff` / 定理 `antisymm_iff`

English:
theorem antisymm_iff
  given: [Std.Refl r] [Std.Antisymm r] {a b : α}
  statement: r a b ∧ r b a ↔ a = b
  proof: ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

中文:
定理 antisymm_iff
  条件: [Std.Refl r] [Std.Antisymm r] {a b : α}
  结论: r a b ∧ r b a ↔ a = b
  证明: ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

Depends on / 依赖: antisymm
-/
theorem antisymm_iff [Std.Refl r] [Std.Antisymm r] {a b : α} : r a b ∧ r b a ↔ a = b :=
  ⟨fun h => antisymm h.1 h.2, by
    rintro rfl
    exact ⟨refl _, refl _⟩⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
/--
theorem `antisymm_of` / 定理 `antisymm_of`

English:
theorem antisymm_of
  given: (r : α -> α -> Prop) [Std.Antisymm r] {a b : α}
  statement: r a b -> r b a -> a = b
  proof: antisymm

中文:
定理 antisymm_of
  条件: (r : α -> α -> 命题) [Std.Antisymm r] {a b : α}
  结论: r a b -> r b a -> a = b
  证明: antisymm

Depends on / 依赖: antisymm
-/
theorem antisymm_of (r : α -> α -> Prop) [Std.Antisymm r] {a b : α} : r a b -> r b a -> a = b :=
  antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `Init.Algebra.Classes`, but is missing there. -/
@[elab_without_expected_type]
/--
theorem `antisymm_of'` / 定理 `antisymm_of'`

English:
theorem antisymm_of'
  given: (r : α -> α -> Prop) [Std.Antisymm r] {a b : α}
  statement: r a b -> r b a -> b = a
  proof: antisymm'

中文:
定理 antisymm_of'
  条件: (r : α -> α -> 命题) [Std.Antisymm r] {a b : α}
  结论: r a b -> r b a -> b = a
  证明: antisymm'

Depends on / 依赖: antisymm
-/
theorem antisymm_of' (r : α -> α -> Prop) [Std.Antisymm r] {a b : α} : r a b -> r b a -> b = a :=
  antisymm'

/--
theorem `comm_of` / 定理 `comm_of`

English:
theorem comm_of
  given: (r : α -> α -> Prop) [Std.Symm r] {a b : α}
  statement: r a b ↔ r b a
  proof: comm

中文:
定理 comm_of
  条件: (r : α -> α -> 命题) [Std.Symm r] {a b : α}
  结论: r a b ↔ r b a
  证明: comm
-/
theorem comm_of (r : α -> α -> Prop) [Std.Symm r] {a b : α} : r a b ↔ r b a :=
  comm

/--
theorem `Std.Asymm.antisymm` / 定理 `Std.Asymm.antisymm`

English:
theorem Std.Asymm.antisymm
  given: (r : α -> α -> Prop) [Std.Asymm r]
  statement: Std.Antisymm r
  proof: inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isAntisymm := Std.Asymm.antisymm
@[deprecated (since := "2026-01-06")] protected alias Std.Asymm.isAntisymm := Std.Asymm.antisymm

中文:
定理 Std.Asymm.antisymm
  条件: (r : α -> α -> 命题) [Std.Asymm r]
  结论: Std.Antisymm r
  证明: inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isAntisymm := Std.Asymm.antisymm
@[deprecated (since := "2026-01-06")] protected alias Std.Asymm.isAntisymm := Std.Asymm.antisymm
-/
protected theorem Std.Asymm.antisymm (r : α -> α -> Prop) [Std.Asymm r] : Std.Antisymm r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isAntisymm := Std.Asymm.antisymm
@[deprecated (since := "2026-01-06")] protected alias Std.Asymm.isAntisymm := Std.Asymm.antisymm

/--
theorem `Std.Asymm.irrefl` / 定理 `Std.Asymm.irrefl`

English:
theorem Std.Asymm.irrefl
  given: [Std.Asymm r]
  statement: Std.Irrefl r
  proof: inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isIrrefl := Std.Asymm.irrefl
@[deprecated (since := "2026-01-07")] protected alias Std.Asymm.isIrrefl := Std.Asymm.irrefl

中文:
定理 Std.Asymm.irrefl
  条件: [Std.Asymm r]
  结论: Std.Irrefl r
  证明: inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isIrrefl := Std.Asymm.irrefl
@[deprecated (since := "2026-01-07")] protected alias Std.Asymm.isIrrefl := Std.Asymm.irrefl
-/
protected theorem Std.Asymm.irrefl [Std.Asymm r] : Std.Irrefl r :=
  inferInstance

@[deprecated (since := "2026-01-05")] protected alias IsAsymm.isIrrefl := Std.Asymm.irrefl
@[deprecated (since := "2026-01-07")] protected alias Std.Asymm.isIrrefl := Std.Asymm.irrefl

/--
theorem `Std.Total.trichotomous` / 定理 `Std.Total.trichotomous`

English:
theorem Std.Total.trichotomous
  given: (r : α -> α -> Prop) [Std.Total r]
  statement: Std.Trichotomous r
  proof: inferInstance

@[deprecated (since := "2026-01-24")] alias Std.Total.isTrichotomous := Std.Total.trichotomous

中文:
定理 Std.Total.trichotomous
  条件: (r : α -> α -> 命题) [Std.Total r]
  结论: Std.Trichotomous r
  证明: inferInstance

@[deprecated (since := "2026-01-24")] alias Std.Total.isTrichotomous := Std.Total.trichotomous
-/
protected theorem Std.Total.trichotomous (r : α -> α -> Prop) [Std.Total r] : Std.Trichotomous r :=
  inferInstance

@[deprecated (since := "2026-01-24")] alias Std.Total.isTrichotomous := Std.Total.trichotomous

-- see Note [lower instance priority]
instance (priority := 100) Std.Total.to_refl (r : α -> α -> Prop) [Std.Total r] : Std.Refl r :=
  inferInstance

/--
theorem `ne_of_irrefl` / 定理 `ne_of_irrefl`

English:
theorem ne_of_irrefl
  given: {r} [Std.Irrefl r]
  statement: forall {x y : α}, r x y -> x != y

中文:
定理 ne_of_irrefl
  条件: {r} [Std.Irrefl r]
  结论: 对任意 {x y : α}, r x y -> x != y
-/
theorem ne_of_irrefl {r} [Std.Irrefl r] : forall {x y : α}, r x y -> x != y
  | _, _, h, rfl => irrefl _ h

/--
theorem `ne_of_irrefl'` / 定理 `ne_of_irrefl'`

English:
theorem ne_of_irrefl'
  given: {r} [Std.Irrefl r]
  statement: forall {x y : α}, r x y -> y != x

中文:
定理 ne_of_irrefl'
  条件: {r} [Std.Irrefl r]
  结论: 对任意 {x y : α}, r x y -> y != x
-/
theorem ne_of_irrefl' {r} [Std.Irrefl r] : forall {x y : α}, r x y -> y != x
  | _, _, h, rfl => irrefl _ h

/--
theorem `not_rel_of_subsingleton` / 定理 `not_rel_of_subsingleton`

English:
theorem not_rel_of_subsingleton
  given: (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton α] (x y)
  statement: ¬r x y
  proof: Subsingleton.elim x y ▸ irrefl x

中文:
定理 not_rel_of_subsingleton
  条件: (r : α -> α -> 命题) [Std.Irrefl r] [Subsingleton α] (x y)
  结论: ¬r x y
  证明: Subsingleton.elim x y ▸ irrefl x

Depends on / 依赖: Field.henselian, HenselianLocalRing, Subsingleton, Subsingleton.elim, henselian, irrefl
-/
theorem not_rel_of_subsingleton (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton α] (x y) : ¬r x y :=
  Subsingleton.elim x y ▸ irrefl x

/--
theorem `rel_of_subsingleton` / 定理 `rel_of_subsingleton`

English:
theorem rel_of_subsingleton
  given: (r : α -> α -> Prop) [Std.Refl r] [Subsingleton α] (x y)
  statement: r x y
  proof: Subsingleton.elim x y ▸ refl x

@[simp]

中文:
定理 rel_of_subsingleton
  条件: (r : α -> α -> 命题) [Std.Refl r] [Subsingleton α] (x y)
  结论: r x y
  证明: Subsingleton.elim x y ▸ refl x

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem rel_of_subsingleton (r : α -> α -> Prop) [Std.Refl r] [Subsingleton α] (x y) : r x y :=
  Subsingleton.elim x y ▸ refl x

@[simp]
/--
theorem `empty_relation_apply` / 定理 `empty_relation_apply`

English:
theorem empty_relation_apply
  given: (a b : α)
  statement: emptyRelation a b ↔ False
  proof: Iff.rfl

中文:
定理 empty_relation_apply
  条件: (a b : α)
  结论: emptyRelation a b ↔ False
  证明: Iff.rfl

Depends on / 依赖: HenselianLocalRing, HenselianLocalRing.is_henselian, Ideal.Quotient.eq_zero_iff_mem, Ideal.jacobson, Iff.rfl, IsLocalRing, IsLocalRing.mem_maximalIdeal, Quotient, contrapose, eq_maximalIdeal, eq_zero_iff_mem, is_henselian, jacobson, le_sInf_iff, mem_maximalIdeal, mem_nonunits_iff, not_isUnit_zero
-/
theorem empty_relation_apply (a b : α) : emptyRelation a b ↔ False :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Irrefl α emptyRelation
  body: ⟨fun _ => id⟩

中文:
实例 :
  签名: @Std.Irrefl α emptyRelation
  定义体: ⟨fun _ => id⟩

Depends on / 依赖: CommRing, IsAdicComplete, IsAdicComplete.henselianRing, henselianRing
-/
instance : @Std.Irrefl α emptyRelation :=
  ⟨fun _ => id⟩

/--
theorem `rel_congr_left` / 定理 `rel_congr_left`

English:
theorem rel_congr_left
  given: [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b)
  statement: r a c ↔ r b c
  proof: ⟨trans_of r (symm_of r h), trans_of r h⟩

中文:
定理 rel_congr_left
  条件: [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b)
  结论: r a c ↔ r b c
  证明: ⟨trans_of r (symm_of r h), trans_of r h⟩

Depends on / 依赖: symm_of, trans_of
-/
theorem rel_congr_left [Std.Symm r] [IsTrans α r] {a b c : α} (h : r a b) : r a c ↔ r b c :=
  ⟨trans_of r (symm_of r h), trans_of r h⟩

/--
theorem `rel_congr_right` / 定理 `rel_congr_right`

English:
theorem rel_congr_right
  given: [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c)
  statement: r a b ↔ r a c
  proof: ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩

中文:
定理 rel_congr_right
  条件: [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c)
  结论: r a b ↔ r a c
  证明: ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩

Depends on / 依赖: symm_of, trans_of
-/
theorem rel_congr_right [Std.Symm r] [IsTrans α r] {a b c : α} (h : r b c) : r a b ↔ r a c :=
  ⟨(trans_of r · h), (trans_of r · (symm_of r h))⟩

/--
theorem `rel_congr` / 定理 `rel_congr`

English:
theorem rel_congr
  given: [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d)
  proof: by
  rw [rel_congr_left h₁]; rw [rel_congr_right h₂]

中文:
定理 rel_congr
  条件: [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d)
  证明: by
  rw [rel_congr_left h₁]; rw [rel_congr_right h₂]

Depends on / 依赖: rel_congr_left, rel_congr_right
-/
theorem rel_congr [Std.Symm r] [IsTrans α r] {a b c d : α} (h₁ : r a b) (h₂ : r c d) :
    r a c ↔ r b d := by
  rw [rel_congr_left h₁]; rw [rel_congr_right h₂]

/--
theorem `trans_trichotomous_left` / 定理 `trans_trichotomous_left`

English:
theorem trans_trichotomous_left
  statement: [IsTrans α r] [Std.Trichotomous r] {a b c : α}
  proof: by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁

中文:
定理 trans_trichotomous_left
  结论: [IsTrans α r] [Std.Trichotomous r] {a b c : α}
  证明: by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁

Depends on / 依赖: _root_, _root_.trans, absurd, trichotomous_of
-/
theorem trans_trichotomous_left [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : ¬r b a) (h₂ : r b c) : r a c := by
  rcases trichotomous_of r a b with (h₃ | rfl | h₃)
  · exact _root_.trans h₃ h₂
  · exact h₂
  · exact absurd h₃ h₁

/--
theorem `trans_trichotomous_right` / 定理 `trans_trichotomous_right`

English:
theorem trans_trichotomous_right
  statement: [IsTrans α r] [Std.Trichotomous r] {a b c : α}
  proof: by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

@[deprecated IsTrans.trans (since := "2026-02-20")]

中文:
定理 trans_trichotomous_right
  结论: [IsTrans α r] [Std.Trichotomous r] {a b c : α}
  证明: by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

@[deprecated IsTrans.trans (since := "2026-02-20")]

Depends on / 依赖: _root_, _root_.trans, absurd, trichotomous_of
-/
theorem trans_trichotomous_right [IsTrans α r] [Std.Trichotomous r] {a b c : α}
    (h₁ : r a b) (h₂ : ¬r c b) : r a c := by
  rcases trichotomous_of r b c with (h₃ | rfl | h₃)
  · exact _root_.trans h₁ h₃
  · exact h₁
  · exact absurd h₃ h₂

@[deprecated IsTrans.trans (since := "2026-02-20")]
/--
theorem `transitive_of_trans` / 定理 `transitive_of_trans`

English:
theorem transitive_of_trans
  given: (r : α -> α -> Prop) [IsTrans α r]
  statement: Transitive r
  proof: IsTrans.trans

中文:
定理 transitive_of_trans
  条件: (r : α -> α -> 命题) [IsTrans α r]
  结论: Transitive r
  证明: IsTrans.trans

Depends on / 依赖: IsTrans, IsTrans.trans
-/
theorem transitive_of_trans (r : α -> α -> Prop) [IsTrans α r] : Transitive r := IsTrans.trans

/--
theorem `extensional_of_trichotomous_of_irrefl` / 定理 `extensional_of_trichotomous_of_irrefl`

English:
theorem extensional_of_trichotomous_of_irrefl
  statement: (r : α -> α -> Prop) [Std.Trichotomous r] [Std.Irrefl r]
  proof: ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right mt (H _).1
 irrefl b

中文:
定理 extensional_of_trichotomous_of_irrefl
  结论: (r : α -> α -> 命题) [Std.Trichotomous r] [Std.Irrefl r]
  证明: ((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right mt (H _).1
 irrefl b

Depends on / 依赖: irrefl, resolve_left, resolve_right, trichotomous
-/
theorem extensional_of_trichotomous_of_irrefl (r : α -> α -> Prop) [Std.Trichotomous r] [Std.Irrefl r]
    {a b : α} (H : forall x, r x a ↔ r x b) : a = b :=
((@trichotomous _ r _ a b).resolve_left <| mt (H _).2 <| irrefl a).resolve_right mt (H _).1
 irrefl b
