/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.RelIso.Set

/-!
# Lexicographic order and order isomorphisms

## Main declarations

* `OrderIso.sumLexIioIci` and `OrderIso.sumLexIicIoi`: if `α` is a linear order and `x : α`,
  then `α` is order isomorphic to both `Iio x ⊕ₗ Ici x` and `Iic x ⊕ₗ Ioi x`.
* `Prod.Lex.prodUnique` and `Prod.Lex.uniqueProd`: `α ×ₗ β` is order isomorphic to one side if the
  other side is `Unique`.
-/

@[expose] public section

open Set

variable {α : Type*}

/-! ### Relation isomorphism -/

namespace RelIso

variable {r : α -> α -> Prop} {x y : α} [IsTrans α r] [Std.Trichotomous r] [DecidableRel r]

variable (r x) in
/--
Definition of `sumLexComplLeft` / `sumLexComplLeft` 的定义

English:
definition sumLexComplLeft
  signature: : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  body: .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
· simpa using fun h => ha trans h hb
    · simp

@[simp]

中文:
定义 sumLexComplLeft
  签名: : 和.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  定义体: .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
· simpa using fun h => ha trans h hb
    · simp

@[simp]

Depends on / 依赖: sumCompl
-/
def sumLexComplLeft : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  toEquiv := .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
· simpa using fun h => ha trans h hb
    · simp

@[simp]
/--
theorem `sumLexComplLeft_apply` / 定理 `sumLexComplLeft_apply`

English:
theorem sumLexComplLeft_apply
  given: (a)
  statement: sumLexComplLeft r x a = Equiv.sumCompl (r · x) a
  proof: rfl

@[simp]

中文:
定理 sumLexComplLeft_apply
  条件: (a)
  结论: sumLexComplLeft r x a = 等价.sumCompl (r · x) a
  证明: rfl

@[simp]
-/
theorem sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

@[simp]
/--
theorem `sumLexComplLeft_symm_apply` / 定理 `sumLexComplLeft_symm_apply`

English:
theorem sumLexComplLeft_symm_apply
  given: (a)
  statement: sumLexComplLeft r x a = Equiv.sumCompl (r · x) a
  proof: rfl

中文:
定理 sumLexComplLeft_symm_apply
  条件: (a)
  结论: sumLexComplLeft r x a = 等价.sumCompl (r · x) a
  证明: rfl
-/
theorem sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

variable (r x) in
/--
Definition of `sumLexComplRight` / `sumLexComplRight` 的定义

English:
definition sumLexComplRight
  signature: : Sum.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r where
  body: (Equiv.sumComm _ _).trans .sumCompl (r x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
· simpa using fun h => hb trans ha h
    · simp

@[simp]

中文:
定义 sumLexComplRight
  签名: : 和.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r where
  定义体: (Equiv.sumComm _ _).trans .sumCompl (r x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
· simpa using fun h => hb trans ha h
    · simp

@[simp]

Depends on / 依赖: Equiv.sumComm, sumComm, sumCompl
-/
def sumLexComplRight : Sum.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r where
toEquiv := (Equiv.sumComm _ _).trans .sumCompl (r x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
· simpa using fun h => hb trans ha h
    · simp

@[simp]
/--
theorem `sumLexComplRight_apply` / 定理 `sumLexComplRight_apply`

English:
theorem sumLexComplRight_apply
  given: (a)
  statement: sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap
  proof: rfl

@[simp]

中文:
定理 sumLexComplRight_apply
  条件: (a)
  结论: sumLexComplRight r x a = 等价.sumCompl (r x) a.swap
  证明: rfl

@[simp]
-/
theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

@[simp]
/--
theorem `sumLexComplRight_symm_apply` / 定理 `sumLexComplRight_symm_apply`

English:
theorem sumLexComplRight_symm_apply
  given: (a)
  statement: sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap
  proof: rfl

中文:
定理 sumLexComplRight_symm_apply
  条件: (a)
  结论: sumLexComplRight r x a = 等价.sumCompl (r x) a.swap
  证明: rfl
-/
theorem sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

end RelIso

/-! ### Order isomorphism -/

namespace OrderIso

variable [LinearOrder α] {x y : α}

variable (x) in
/--
Definition of `sumLexIioIci` / `sumLexIioIci` 的定义

English:
definition sumLexIioIci
  signature: : Iio x oplusₗ Ici x ≃o α
  body: (sumLexCongr (refl _) (setCongr (Ici x) {y | ¬ y < x} (by ext; simp))).trans
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

@[simp]

中文:
定义 sumLexIioIci
  签名: : 左无界右开区间 x oplusₗ 左闭右无界区间 x ≃o α
  定义体: (sumLexCongr (refl _) (setCongr (Ici x) {y | ¬ y < x} (by ext; simp))).trans
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

@[simp]

Depends on / 依赖: RelIso, RelIso.sumLexComplLeft, ofRelIsoLT, setCongr, sumLexComplLeft, sumLexCongr
-/
def sumLexIioIci : Iio x oplusₗ Ici x ≃o α :=
(sumLexCongr (refl _) (setCongr (Ici x) {y | ¬ y < x} (by ext; simp))).trans
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

@[simp]
/--
theorem `sumLexIioIci_apply_inl` / 定理 `sumLexIioIci_apply_inl`

English:
theorem sumLexIioIci_apply_inl
  given: (a : Iio x)
  statement: sumLexIioIci x (toLex <| Sum.inl a) = a
  proof: rfl

@[simp]

中文:
定理 sumLexIioIci_apply_inl
  条件: (a : 左无界右开区间 x)
  结论: sumLexIioIci x (toLex <| 和.inl a) = a
  证明: rfl

@[simp]
-/
theorem sumLexIioIci_apply_inl (a : Iio x) : sumLexIioIci x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
/--
theorem `sumLexIioIci_apply_inr` / 定理 `sumLexIioIci_apply_inr`

English:
theorem sumLexIioIci_apply_inr
  given: (a : Ici x)
  statement: sumLexIioIci x (toLex <| Sum.inr a) = a
  proof: rfl

中文:
定理 sumLexIioIci_apply_inr
  条件: (a : 左闭右无界区间 x)
  结论: sumLexIioIci x (toLex <| 和.inr a) = a
  证明: rfl

Depends on / 依赖: f.toRingHom.comp, g.toRingHom, toRingHom
-/
theorem sumLexIioIci_apply_inr (a : Ici x) : sumLexIioIci x (toLex <| Sum.inr a) = a :=
  rfl

/--
theorem `sumLexIioIci_symm_apply_of_lt` / 定理 `sumLexIioIci_symm_apply_of_lt`

English:
theorem sumLexIioIci_symm_apply_of_lt
  given: (h : y < x)
  proof: by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inl]

中文:
定理 sumLexIioIci_symm_apply_of_lt
  条件: (h : y < x)
  证明: by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inl]

Depends on / 依赖: sumLexIioIci_apply_inl, symm_apply_eq
-/
theorem sumLexIioIci_symm_apply_of_lt (h : y < x) :
    (sumLexIioIci x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inl]

/--
theorem `sumLexIioIci_symm_apply_of_ge` / 定理 `sumLexIioIci_symm_apply_of_ge`

English:
theorem sumLexIioIci_symm_apply_of_ge
  given: {y : α} (h : x <= y)
  proof: by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inr]

@[simp]

中文:
定理 sumLexIioIci_symm_apply_of_ge
  条件: {y : α} (h : x <= y)
  证明: by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inr]

@[simp]

Depends on / 依赖: sumLexIioIci_apply_inr, symm_apply_eq
-/
theorem sumLexIioIci_symm_apply_of_ge {y : α} (h : x <= y) :
    (sumLexIioIci x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq]; rw [sumLexIioIci_apply_inr]

@[simp]
/--
theorem `sumLexIioIci_symm_apply_Iio` / 定理 `sumLexIioIci_symm_apply_Iio`

English:
theorem sumLexIioIci_symm_apply_Iio
  given: (a : Iio x)
  statement: (sumLexIioIci x).symm a = toLex (Sum.inl a)
  proof: sumLexIioIci_symm_apply_of_lt a.2

@[simp]

中文:
定理 sumLexIioIci_symm_apply_Iio
  条件: (a : 左无界右开区间 x)
  结论: (sumLexIioIci x).symm a = toLex (和.inl a)
  证明: sumLexIioIci_symm_apply_of_lt a.2

@[simp]

Depends on / 依赖: sumLexIioIci_symm_apply_of_lt
-/
theorem sumLexIioIci_symm_apply_Iio (a : Iio x) : (sumLexIioIci x).symm a = toLex (Sum.inl a) :=
  sumLexIioIci_symm_apply_of_lt a.2

@[simp]
/--
theorem `sumLexIioIci_symm_apply_Ici` / 定理 `sumLexIioIci_symm_apply_Ici`

English:
theorem sumLexIioIci_symm_apply_Ici
  given: (a : Ici x)
  statement: (sumLexIioIci x).symm a = toLex (Sum.inr a)
  proof: sumLexIioIci_symm_apply_of_ge a.2

中文:
定理 sumLexIioIci_symm_apply_Ici
  条件: (a : 左闭右无界区间 x)
  结论: (sumLexIioIci x).symm a = toLex (和.inr a)
  证明: sumLexIioIci_symm_apply_of_ge a.2

Depends on / 依赖: sumLexIioIci_symm_apply_of_ge
-/
theorem sumLexIioIci_symm_apply_Ici (a : Ici x) : (sumLexIioIci x).symm a = toLex (Sum.inr a) :=
  sumLexIioIci_symm_apply_of_ge a.2

variable (x) in
/--
Definition of `sumLexIicIoi` / `sumLexIicIoi` 的定义

English:
definition sumLexIicIoi
  signature: : Iic x oplusₗ Ioi x ≃o α
  body: (sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]

中文:
定义 sumLexIicIoi
  签名: : 左无界右闭区间 x oplusₗ 左开右无界区间 x ≃o α
  定义体: (sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]

Depends on / 依赖: RelIso, RelIso.sumLexComplRight, f.toRingHom, ofRelIsoLT, setCongr, sumLexComplRight, sumLexCongr, toRingHom
-/
def sumLexIicIoi : Iic x oplusₗ Ioi x ≃o α :=
(sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]
/--
theorem `sumLexIicIoi_apply_inl` / 定理 `sumLexIicIoi_apply_inl`

English:
theorem sumLexIicIoi_apply_inl
  given: (a : Iic x)
  statement: sumLexIicIoi x (toLex <| Sum.inl a) = a
  proof: rfl

@[simp]

中文:
定理 sumLexIicIoi_apply_inl
  条件: (a : 左无界右闭区间 x)
  结论: sumLexIicIoi x (toLex <| 和.inl a) = a
  证明: rfl

@[simp]
-/
theorem sumLexIicIoi_apply_inl (a : Iic x) : sumLexIicIoi x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
/--
theorem `sumLexIicIoi_apply_inr` / 定理 `sumLexIicIoi_apply_inr`

English:
theorem sumLexIicIoi_apply_inr
  given: (a : Ioi x)
  statement: sumLexIicIoi x (toLex <| Sum.inr a) = a
  proof: rfl

中文:
定理 sumLexIicIoi_apply_inr
  条件: (a : 左开右无界区间 x)
  结论: sumLexIicIoi x (toLex <| 和.inr a) = a
  证明: rfl
-/
theorem sumLexIicIoi_apply_inr (a : Ioi x) : sumLexIicIoi x (toLex <| Sum.inr a) = a :=
  rfl

/--
theorem `sumLexIicIoi_symm_apply_of_le` / 定理 `sumLexIicIoi_symm_apply_of_le`

English:
theorem sumLexIicIoi_symm_apply_of_le
  given: (h : y <= x)
  proof: by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inl]

中文:
定理 sumLexIicIoi_symm_apply_of_le
  条件: (h : y <= x)
  证明: by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inl]

Depends on / 依赖: sumLexIicIoi_apply_inl, symm_apply_eq
-/
theorem sumLexIicIoi_symm_apply_of_le (h : y <= x) :
    (sumLexIicIoi x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inl]

/--
theorem `sumLexIicIoi_symm_apply_of_lt` / 定理 `sumLexIicIoi_symm_apply_of_lt`

English:
theorem sumLexIicIoi_symm_apply_of_lt
  given: {y : α} (h : x < y)
  proof: by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inr]

@[simp]

中文:
定理 sumLexIicIoi_symm_apply_of_lt
  条件: {y : α} (h : x < y)
  证明: by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inr]

@[simp]

Depends on / 依赖: sumLexIicIoi_apply_inr, symm_apply_eq
-/
theorem sumLexIicIoi_symm_apply_of_lt {y : α} (h : x < y) :
    (sumLexIicIoi x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq]; rw [sumLexIicIoi_apply_inr]

@[simp]
/--
theorem `sumLexIicIoi_symm_apply_Iic` / 定理 `sumLexIicIoi_symm_apply_Iic`

English:
theorem sumLexIicIoi_symm_apply_Iic
  given: (a : Iic x)
  statement: (sumLexIicIoi x).symm a = Sum.inl a
  proof: sumLexIicIoi_symm_apply_of_le a.2

@[simp]

中文:
定理 sumLexIicIoi_symm_apply_Iic
  条件: (a : 左无界右闭区间 x)
  结论: (sumLexIicIoi x).symm a = 和.inl a
  证明: sumLexIicIoi_symm_apply_of_le a.2

@[simp]

Depends on / 依赖: sumLexIicIoi_symm_apply_of_le
-/
theorem sumLexIicIoi_symm_apply_Iic (a : Iic x) : (sumLexIicIoi x).symm a = Sum.inl a :=
  sumLexIicIoi_symm_apply_of_le a.2

@[simp]
/--
theorem `sumLexIicIoi_symm_apply_Ioi` / 定理 `sumLexIicIoi_symm_apply_Ioi`

English:
theorem sumLexIicIoi_symm_apply_Ioi
  given: (a : Ioi x)
  statement: (sumLexIicIoi x).symm a = Sum.inr a
  proof: sumLexIicIoi_symm_apply_of_lt a.2

中文:
定理 sumLexIicIoi_symm_apply_Ioi
  条件: (a : 左开右无界区间 x)
  结论: (sumLexIicIoi x).symm a = 和.inr a
  证明: sumLexIicIoi_symm_apply_of_lt a.2

Depends on / 依赖: sumLexIicIoi_symm_apply_of_lt
-/
theorem sumLexIicIoi_symm_apply_Ioi (a : Ioi x) : (sumLexIicIoi x).symm a = Sum.inr a :=
  sumLexIicIoi_symm_apply_of_lt a.2

end OrderIso

/-! ### Degenerate products -/

namespace Prod.Lex
variable (α β : Type*)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `prodUnique` / `prodUnique` 的定义

English:
definition prodUnique
  signature: [PartialOrder α] [Preorder β] [Unique β]
  body: (ofLex x).1
  invFun x := toLex (x, default)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq b
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    simpa [Prod.Lex.toLex_le_toLex] using le_iff_lt_or_eq

中文:
定义 prodUnique
  签名: [偏序 α] [预序 β] [唯一 β]
  定义体: (ofLex x).1
  invFun x := toLex (x, default)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq b
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    simpa [Prod.Lex.toLex_le_toLex] using le_iff_lt_or_eq
-/
def prodUnique [PartialOrder α] [Preorder β] [Unique β] : α ×ₗ β ≃o α where
  toFun x := (ofLex x).1
  invFun x := toLex (x, default)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq b
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    simpa [Prod.Lex.toLex_le_toLex] using le_iff_lt_or_eq

variable {α β} in
@[simp]
/--
theorem `prodUnique_apply` / 定理 `prodUnique_apply`

English:
theorem prodUnique_apply
  given: [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β)
  proof: rfl

中文:
定理 prodUnique_apply
  条件: [偏序 α] [预序 β] [唯一 β] (x : α ×ₗ β)
  证明: rfl
-/
theorem prodUnique_apply [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β) :
    prodUnique α β x = (ofLex x).1 := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `uniqueProd` / `uniqueProd` 的定义

English:
definition uniqueProd
  signature: [Preorder α] [Unique α] [LE β]
  body: (ofLex x).2
  invFun x := toLex (default, x)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq a
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    simp [Prod.Lex.toLex_le_toLex, heq]

中文:
定义 uniqueProd
  签名: [预序 α] [唯一 α] [LE β]
  定义体: (ofLex x).2
  invFun x := toLex (default, x)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq a
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    simp [Prod.Lex.toLex_le_toLex, heq]
-/
def uniqueProd [Preorder α] [Unique α] [LE β] : α ×ₗ β ≃o β where
  toFun x := (ofLex x).2
  invFun x := toLex (default, x)
  left_inv x := x.rec fun (a, b) => by simpa using Unique.default_eq a
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a => b.rec fun b => by
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    simp [Prod.Lex.toLex_le_toLex, heq]

variable {α β} in
@[simp]
/--
theorem `uniqueProd_apply` / 定理 `uniqueProd_apply`

English:
theorem uniqueProd_apply
  given: [Preorder α] [Unique α] [LE β] (x : α ×ₗ β)
  proof: rfl

中文:
定理 uniqueProd_apply
  条件: [预序 α] [唯一 α] [LE β] (x : α ×ₗ β)
  证明: rfl
-/
theorem uniqueProd_apply [Preorder α] [Unique α] [LE β] (x : α ×ₗ β) :
    uniqueProd α β x = (ofLex x).2 := rfl

/-- `Equiv.prodAssoc` promoted to an order isomorphism of lexicographic products. -/
@[simps!]
/--
Definition of `prodLexAssoc` / `prodLexAssoc` 的定义

English:
definition prodLexAssoc
  signature: (α β γ : Type*)
  body: .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.prodAssoc α β γ) .trans (.prodCongr (.refl _) toLex) toLex
  map_rel_iff' := by
    simp only [Prod.Lex.le_iff, Prod.Lex.lt_iff, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.prodAssoc_apply]
    grind [EmbeddingLike.apply_eq_iff_eq, ofLex_toLex]

中文:
定义 prodLexAssoc
  签名: (α β γ : 类型)
  定义体: .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.prodAssoc α β γ) .trans (.prodCongr (.refl _) toLex) toLex
  map_rel_iff' := by
    simp only [Prod.Lex.le_iff, Prod.Lex.lt_iff, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.prodAssoc_apply]
    grind [EmbeddingLike.apply_eq_iff_eq, ofLex_toLex]

Depends on / 依赖: Cotangent, Module, Module.compHom, P.Cotangent, algebraMap, compHom, prodCongr
-/
def prodLexAssoc (α β γ : Type*)
    [Preorder α] [Preorder β] [Preorder γ] : (α ×ₗ β) ×ₗ γ ≃o α ×ₗ β ×ₗ γ where
toEquiv := .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.prodAssoc α β γ) .trans (.prodCongr (.refl _) toLex) toLex
  map_rel_iff' := by
    simp only [Prod.Lex.le_iff, Prod.Lex.lt_iff, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.prodAssoc_apply]
    grind [EmbeddingLike.apply_eq_iff_eq, ofLex_toLex]

/-- `Equiv.sumProdDistrib` promoted to an order isomorphism of lexicographic products.

Right distributivity doesn't hold. A counterexample is `ℕ ×ₗ (Unit ⊕ₗ Unit) ≃o ℕ`
which is not isomorphic to `ℕ ×ₗ Unit ⊕ₗ ℕ ×ₗ Unit ≃o ℕ ⊕ₗ ℕ`. -/
@[simps!]
/--
Definition of `sumLexProdLexDistrib` / `sumLexProdLexDistrib` 的定义

English:
definition sumLexProdLexDistrib
  signature: (α β γ : Type*)
  body: .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.sumProdDistrib α β γ) .trans (.sumCongr toLex toLex) toLex
  map_rel_iff' := by simp [Prod.Lex.le_iff]

中文:
定义 sumLexProdLexDistrib
  签名: (α β γ : 类型)
  定义体: .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.sumProdDistrib α β γ) .trans (.sumCongr toLex toLex) toLex
  map_rel_iff' := by simp [Prod.Lex.le_iff]

Depends on / 依赖: Algebra, Algebra.smul_def, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, map_mul, mul_smul, prodCongr, smul_def
-/
def sumLexProdLexDistrib (α β γ : Type*)
    [Preorder α] [Preorder β] [Preorder γ] : (α oplusₗ β) ×ₗ γ ≃o α ×ₗ γ oplusₗ β ×ₗ γ where
toEquiv := .trans ofLex .trans (.prodCongr ofLex <| .refl _)
.trans (.sumProdDistrib α β γ) .trans (.sumCongr toLex toLex) toLex
  map_rel_iff' := by simp [Prod.Lex.le_iff]

/-- `Equiv.prodCongr` promoted to an order isomorphism between lexicographic products. -/
@[simps! apply]
/--
Definition of `prodLexCongr` / `prodLexCongr` 的定义

English:
definition prodLexCongr
  signature: {α β γ δ : Type*} [Preorder α] [Preorder β]
  body: ofLex.trans ((Equiv.prodCongr ea eb).trans toLex)
  map_rel_iff' := by simp [Prod.Lex.le_iff]

中文:
定义 prodLexCongr
  签名: {α β γ δ : 类型} [预序 α] [预序 β]
  定义体: ofLex.trans ((Equiv.prodCongr ea eb).trans toLex)
  map_rel_iff' := by simp [Prod.Lex.le_iff]

Depends on / 依赖: Equiv.prodCongr, ofLex.trans, prodCongr
-/
def prodLexCongr {α β γ δ : Type*} [Preorder α] [Preorder β]
    [Preorder γ] [Preorder δ] (ea : α ≃o β) (eb : γ ≃o δ) : α ×ₗ γ ≃o β ×ₗ δ where
  toEquiv := ofLex.trans ((Equiv.prodCongr ea eb).trans toLex)
  map_rel_iff' := by simp [Prod.Lex.le_iff]

end Prod.Lex
