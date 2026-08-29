/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization

/-!
# Comparability and incomparability relations

Two values in a preorder are said to be comparable (`SymmRel`) whenever `a ≤ b` or `b ≤ a`. We
define both the comparability and incomparability relations.

In a linear order, `SymmGen (· ≤ ·) a b` is always true, and `IncompRel (· ≤ ·) a b` is always
false.

## Implementation notes

Although comparability and incomparability are negations of each other, both relations are
convenient in different contexts, and as such, it's useful to keep them distinct. To move from one
to the other, use `not_symmGen_iff` and `not_incompRel_iff_symmGen`.

## Main declarations

* `CompRel`: The comparability relation. `CompRel r a b` means that `a` and `b` is related in
  either direction by `r`. This is deprecated in favor of `Relation.SymmGen`, with naming chosen for
  consistency with `Relation.TransGen` in core and other definitions in `Mathlib.Logic.Relation`.
* `IncompRel`: The incomparability relation. `IncompRel r a b` means that `a` and `b` are related in
  neither direction by `r`.

## Todo

These definitions should be linked to `IsChain` and `IsAntichain`.
-/

@[expose] public section

open Function Relation

variable {α : Type*} {a b c d : α}

/-! ### Comparability -/

section Relation

variable {r : α -> α -> Prop}

/-- The comparability relation `CompRel r a b` means that either `r a b` or `r b a`. -/
@[deprecated SymmGen (since := "2026-01-25")]
/--
Definition of `CompRel` / `CompRel` 的定义

English:
definition CompRel
  signature: (r : α -> α -> Prop) (a b : α)
  body: r a b ∨ r b a

@[deprecated SymmGen.of_rel (since := "2026-01-25")]

中文:
定义 CompRel
  签名: (r : α -> α -> 命题) (a b : α)
  定义体: r a b ∨ r b a

@[deprecated SymmGen.of_rel (since := "2026-01-25")]
-/
def CompRel (r : α -> α -> Prop) (a b : α) : Prop :=
  r a b ∨ r b a

@[deprecated SymmGen.of_rel (since := "2026-01-25")]
/--
theorem `CompRel.of_rel` / 定理 `CompRel.of_rel`

English:
theorem CompRel.of_rel
  given: (h : r a b)
  statement: CompRel r a b
  proof: SymmGen.of_rel h

@[deprecated SymmGen.of_rel_symm (since := "2026-01-25")]

中文:
定理 CompRel.of_rel
  条件: (h : r a b)
  结论: CompRel r a b
  证明: SymmGen.of_rel h

@[deprecated SymmGen.of_rel_symm (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_rel, of_rel
-/
theorem CompRel.of_rel (h : r a b) : CompRel r a b :=
  SymmGen.of_rel h

@[deprecated SymmGen.of_rel_symm (since := "2026-01-25")]
/--
theorem `CompRel.of_rel_symm` / 定理 `CompRel.of_rel_symm`

English:
theorem CompRel.of_rel_symm
  given: (h : r b a)
  statement: CompRel r a b
  proof: SymmGen.of_rel_symm h

@[deprecated symmGen_swap (since := "2026-01-25")]

中文:
定理 CompRel.of_rel_symm
  条件: (h : r b a)
  结论: CompRel r a b
  证明: SymmGen.of_rel_symm h

@[deprecated symmGen_swap (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_rel_symm, of_rel_symm
-/
theorem CompRel.of_rel_symm (h : r b a) : CompRel r a b :=
  SymmGen.of_rel_symm h

@[deprecated symmGen_swap (since := "2026-01-25")]
/--
theorem `compRel_swap` / 定理 `compRel_swap`

English:
theorem compRel_swap
  given: (r : α -> α -> Prop)
  statement: CompRel (swap r) = CompRel r
  proof: symmGen_swap r

@[deprecated symmGen_swap_apply (since := "2026-01-25")]

中文:
定理 compRel_swap
  条件: (r : α -> α -> 命题)
  结论: CompRel (swap r) = CompRel r
  证明: symmGen_swap r

@[deprecated symmGen_swap_apply (since := "2026-01-25")]

Depends on / 依赖: symmGen_swap
-/
theorem compRel_swap (r : α -> α -> Prop) : CompRel (swap r) = CompRel r :=
  symmGen_swap r

@[deprecated symmGen_swap_apply (since := "2026-01-25")]
/--
theorem `compRel_swap_apply` / 定理 `compRel_swap_apply`

English:
theorem compRel_swap_apply
  given: (r : α -> α -> Prop)
  statement: CompRel (swap r) a b ↔ CompRel r a b
  proof: symmGen_swap_apply r

@[simp, refl, deprecated SymmGen.refl (since := "2026-01-25")]

中文:
定理 compRel_swap_apply
  条件: (r : α -> α -> 命题)
  结论: CompRel (swap r) a b ↔ CompRel r a b
  证明: symmGen_swap_apply r

@[simp, refl, deprecated SymmGen.refl (since := "2026-01-25")]

Depends on / 依赖: symmGen_swap_apply
-/
theorem compRel_swap_apply (r : α -> α -> Prop) : CompRel (swap r) a b ↔ CompRel r a b :=
  symmGen_swap_apply r

@[simp, refl, deprecated SymmGen.refl (since := "2026-01-25")]
/--
theorem `CompRel.refl` / 定理 `CompRel.refl`

English:
theorem CompRel.refl
  given: (r : α -> α -> Prop) [Std.Refl r] (a : α)
  statement: CompRel r a a
  proof: SymmGen.refl r a

@[deprecated SymmGen.rfl (since := "2026-01-25")]

中文:
定理 CompRel.refl
  条件: (r : α -> α -> 命题) [Std.Refl r] (a : α)
  结论: CompRel r a a
  证明: SymmGen.refl r a

@[deprecated SymmGen.rfl (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.refl
-/
theorem CompRel.refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : CompRel r a a :=
  SymmGen.refl r a

@[deprecated SymmGen.rfl (since := "2026-01-25")]
/--
theorem `CompRel.rfl` / 定理 `CompRel.rfl`

English:
theorem CompRel.rfl
  given: [Std.Refl r]
  statement: CompRel r a a
  proof: SymmGen.rfl

@[deprecated SymmGen.instRefl (since := "2026-01-25")]

中文:
定理 CompRel.rfl
  条件: [Std.Refl r]
  结论: CompRel r a a
  证明: SymmGen.rfl

@[deprecated SymmGen.instRefl (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.rfl
-/
theorem CompRel.rfl [Std.Refl r] : CompRel r a a := SymmGen.rfl

@[deprecated SymmGen.instRefl (since := "2026-01-25")]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : Std.Refl (CompRel r)
  body: SymmGen.instRefl

@[symm, deprecated SymmGen.symm (since := "2026-01-25")]

中文:
实例 [Std.Refl
  签名: r] : Std.Refl (CompRel r)
  定义体: SymmGen.instRefl

@[symm, deprecated SymmGen.symm (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.instRefl, instRefl
-/
instance [Std.Refl r] : Std.Refl (CompRel r) :=
  SymmGen.instRefl

@[symm, deprecated SymmGen.symm (since := "2026-01-25")]
/--
theorem `CompRel.symm` / 定理 `CompRel.symm`

English:
theorem CompRel.symm
  statement: CompRel r a b -> CompRel r b a
  proof: SymmGen.symm

@[deprecated SymmGen.instSymm (since := "2026-01-25")]

中文:
定理 CompRel.symm
  结论: CompRel r a b -> CompRel r b a
  证明: SymmGen.symm

@[deprecated SymmGen.instSymm (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.symm
-/
theorem CompRel.symm : CompRel r a b -> CompRel r b a :=
  SymmGen.symm

@[deprecated SymmGen.instSymm (since := "2026-01-25")]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (CompRel r)
  body: SymmGen.instSymm

@[deprecated symmGen_comm (since := "2026-01-25")]

中文:
实例 :
  签名: Std.Symm (CompRel r)
  定义体: SymmGen.instSymm

@[deprecated symmGen_comm (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.instSymm, instSymm
-/
instance : Std.Symm (CompRel r) :=
  SymmGen.instSymm

@[deprecated symmGen_comm (since := "2026-01-25")]
/--
theorem `compRel_comm` / 定理 `compRel_comm`

English:
theorem compRel_comm
  given: {a b : α}
  statement: CompRel r a b ↔ CompRel r b a
  proof: symmGen_comm

@[deprecated SymmGen.decidableRel (since := "2026-01-25")]

中文:
定理 compRel_comm
  条件: {a b : α}
  结论: CompRel r a b ↔ CompRel r b a
  证明: symmGen_comm

@[deprecated SymmGen.decidableRel (since := "2026-01-25")]

Depends on / 依赖: symmGen_comm
-/
theorem compRel_comm {a b : α} : CompRel r a b ↔ CompRel r b a :=
  symmGen_comm

@[deprecated SymmGen.decidableRel (since := "2026-01-25")]
/--
Instance `CompRel.decidableRel` / 实例 `CompRel.decidableRel`

English:
instance CompRel.decidableRel
  signature: [DecidableRel r]
  body: SymmGen.decidableRel

@[deprecated AntisymmRel.symmGen (since := "2026-01-25")]

中文:
实例 CompRel.decidableRel
  签名: [DecidableRel r]
  定义体: SymmGen.decidableRel

@[deprecated AntisymmRel.symmGen (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.decidableRel, decidableRel
-/
instance CompRel.decidableRel [DecidableRel r] : DecidableRel (CompRel r) :=
  SymmGen.decidableRel

@[deprecated AntisymmRel.symmGen (since := "2026-01-25")]
/--
theorem `AntisymmRel.compRel` / 定理 `AntisymmRel.compRel`

English:
theorem AntisymmRel.compRel
  given: (h : AntisymmRel r a b)
  statement: CompRel r a b
  proof: AntisymmRel.symmGen h

@[simp, deprecated symmGen_of_total (since := "2026-01-25")]

中文:
定理 AntisymmRel.compRel
  条件: (h : AntisymmRel r a b)
  结论: CompRel r a b
  证明: AntisymmRel.symmGen h

@[simp, deprecated symmGen_of_total (since := "2026-01-25")]

Depends on / 依赖: AntisymmRel, AntisymmRel.symmGen, symmGen
-/
theorem AntisymmRel.compRel (h : AntisymmRel r a b) : CompRel r a b :=
  AntisymmRel.symmGen h

@[simp, deprecated symmGen_of_total (since := "2026-01-25")]
/--
theorem `compRel_of_total` / 定理 `compRel_of_total`

English:
theorem compRel_of_total
  given: [Std.Total r] (a b : α)
  statement: CompRel r a b
  proof: symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.compRel := symmGen_of_total

中文:
定理 compRel_of_total
  条件: [Std.全 r] (a b : α)
  结论: CompRel r a b
  证明: symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.compRel := symmGen_of_total

Depends on / 依赖: symmGen_of_total
-/
theorem compRel_of_total [Std.Total r] (a b : α) : CompRel r a b :=
  symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.compRel := symmGen_of_total

end Relation

section LE

variable [LE α]

@[deprecated SymmGen.of_le (since := "2026-01-25")]
/--
theorem `CompRel.of_le` / 定理 `CompRel.of_le`

English:
theorem CompRel.of_le
  given: (h : a <= b)
  statement: CompRel (· <= ·) a b
  proof: SymmGen.of_le h

@[deprecated SymmGen.of_ge (since := "2026-01-25")]

中文:
定理 CompRel.of_le
  条件: (h : a <= b)
  结论: CompRel (· <= ·) a b
  证明: SymmGen.of_le h

@[deprecated SymmGen.of_ge (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_le, of_le
-/
theorem CompRel.of_le (h : a <= b) : CompRel (· <= ·) a b := SymmGen.of_le h

@[deprecated SymmGen.of_ge (since := "2026-01-25")]
/--
theorem `CompRel.of_ge` / 定理 `CompRel.of_ge`

English:
theorem CompRel.of_ge
  given: (h : b <= a)
  statement: CompRel (· <= ·) a b
  proof: SymmGen.of_ge h

alias LE.le.compRel := CompRel.of_le
alias LE.le.compRel_symm := CompRel.of_ge

中文:
定理 CompRel.of_ge
  条件: (h : b <= a)
  结论: CompRel (· <= ·) a b
  证明: SymmGen.of_ge h

alias LE.le.compRel := CompRel.of_le
alias LE.le.compRel_symm := CompRel.of_ge

Depends on / 依赖: SymmGen, SymmGen.of_ge, of_ge
-/
theorem CompRel.of_ge (h : b <= a) : CompRel (· <= ·) a b := SymmGen.of_ge h

alias LE.le.compRel := CompRel.of_le
alias LE.le.compRel_symm := CompRel.of_ge

end LE

section Preorder

variable [Preorder α]

@[deprecated SymmGen.of_lt (since := "2026-01-25")]
/--
theorem `CompRel.of_lt` / 定理 `CompRel.of_lt`

English:
theorem CompRel.of_lt
  given: (h : a < b)
  statement: CompRel (· <= ·) a b
  proof: SymmGen.of_lt h

@[deprecated SymmGen.of_gt (since := "2026-01-25")]

中文:
定理 CompRel.of_lt
  条件: (h : a < b)
  结论: CompRel (· <= ·) a b
  证明: SymmGen.of_lt h

@[deprecated SymmGen.of_gt (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_lt, of_lt
-/
theorem CompRel.of_lt (h : a < b) : CompRel (· <= ·) a b := SymmGen.of_lt h

@[deprecated SymmGen.of_gt (since := "2026-01-25")]
/--
theorem `CompRel.of_gt` / 定理 `CompRel.of_gt`

English:
theorem CompRel.of_gt
  given: (h : b < a)
  statement: CompRel (· <= ·) a b
  proof: SymmGen.of_gt h

alias LT.lt.compRel := CompRel.of_lt
alias LT.lt.compRel_symm := CompRel.of_gt

@[trans, deprecated SymmGen.of_symmGen_of_antisymmRel (since := "2026-01-25")]

中文:
定理 CompRel.of_gt
  条件: (h : b < a)
  结论: CompRel (· <= ·) a b
  证明: SymmGen.of_gt h

alias LT.lt.compRel := CompRel.of_lt
alias LT.lt.compRel_symm := CompRel.of_gt

@[trans, deprecated SymmGen.of_symmGen_of_antisymmRel (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_gt, of_gt
-/
theorem CompRel.of_gt (h : b < a) : CompRel (· <= ·) a b := SymmGen.of_gt h

alias LT.lt.compRel := CompRel.of_lt
alias LT.lt.compRel_symm := CompRel.of_gt

@[trans, deprecated SymmGen.of_symmGen_of_antisymmRel (since := "2026-01-25")]
/--
theorem `CompRel.of_compRel_of_antisymmRel` / 定理 `CompRel.of_compRel_of_antisymmRel`

English:
theorem CompRel.of_compRel_of_antisymmRel
  proof: SymmGen.of_symmGen_of_antisymmRel h₁ h₂

alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

@[deprecated instTransSymmGenLeAntisymmRel (since := "2026-01-25")]

中文:
定理 CompRel.of_compRel_of_antisymmRel
  证明: SymmGen.of_symmGen_of_antisymmRel h₁ h₂

alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

@[deprecated instTransSymmGenLeAntisymmRel (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_symmGen_of_antisymmRel, of_symmGen_of_antisymmRel
-/
theorem CompRel.of_compRel_of_antisymmRel
    (h₁ : CompRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) b c) : CompRel (· <= ·) a c :=
  SymmGen.of_symmGen_of_antisymmRel h₁ h₂

alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

@[deprecated instTransSymmGenLeAntisymmRel (since := "2026-01-25")]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (CompRel (· <= ·)) (AntisymmRel (· <= ·)) (CompRel (· <= ·))
  body: instTransSymmGenLeAntisymmRel

@[trans, deprecated SymmGen.of_antisymmRel_of_symmGen (since := "2026-01-25")]

中文:
实例 :
  签名: @Trans α α α (CompRel (· <= ·)) (AntisymmRel (· <= ·)) (CompRel (· <= ·))
  定义体: instTransSymmGenLeAntisymmRel

@[trans, deprecated SymmGen.of_antisymmRel_of_symmGen (since := "2026-01-25")]

Depends on / 依赖: instTransSymmGenLeAntisymmRel
-/
instance : @Trans α α α (CompRel (· <= ·)) (AntisymmRel (· <= ·)) (CompRel (· <= ·)) :=
  instTransSymmGenLeAntisymmRel

@[trans, deprecated SymmGen.of_antisymmRel_of_symmGen (since := "2026-01-25")]
/--
theorem `CompRel.of_antisymmRel_of_compRel` / 定理 `CompRel.of_antisymmRel_of_compRel`

English:
theorem CompRel.of_antisymmRel_of_compRel
  proof: SymmGen.of_antisymmRel_of_symmGen h₁ h₂

alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel
@[deprecated instTransAntisymmRelLeSymmGen (since := "2026-01-25")]

中文:
定理 CompRel.of_antisymmRel_of_compRel
  证明: SymmGen.of_antisymmRel_of_symmGen h₁ h₂

alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel
@[deprecated instTransAntisymmRelLeSymmGen (since := "2026-01-25")]

Depends on / 依赖: SymmGen, SymmGen.of_antisymmRel_of_symmGen, of_antisymmRel_of_symmGen
-/
theorem CompRel.of_antisymmRel_of_compRel
    (h₁ : AntisymmRel (· <= ·) a b) (h₂ : CompRel (· <= ·) b c) : CompRel (· <= ·) a c :=
  SymmGen.of_antisymmRel_of_symmGen h₁ h₂

alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel
@[deprecated instTransAntisymmRelLeSymmGen (since := "2026-01-25")]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (AntisymmRel (· <= ·)) (CompRel (· <= ·)) (CompRel (· <= ·))
  body: instTransAntisymmRelLeSymmGen

@[deprecated AntisymmRel.symmGen_congr (since := "2026-01-25")]

中文:
实例 :
  签名: @Trans α α α (AntisymmRel (· <= ·)) (CompRel (· <= ·)) (CompRel (· <= ·))
  定义体: instTransAntisymmRelLeSymmGen

@[deprecated AntisymmRel.symmGen_congr (since := "2026-01-25")]

Depends on / 依赖: instTransAntisymmRelLeSymmGen
-/
instance : @Trans α α α (AntisymmRel (· <= ·)) (CompRel (· <= ·)) (CompRel (· <= ·)) :=
  instTransAntisymmRelLeSymmGen

@[deprecated AntisymmRel.symmGen_congr (since := "2026-01-25")]
/--
theorem `AntisymmRel.compRel_congr` / 定理 `AntisymmRel.compRel_congr`

English:
theorem AntisymmRel.compRel_congr
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  proof: AntisymmRel.symmGen_congr h₁ h₂

@[deprecated AntisymmRel.symmGen_congr_left (since := "2026-01-25")]

中文:
定理 AntisymmRel.compRel_congr
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  证明: AntisymmRel.symmGen_congr h₁ h₂

@[deprecated AntisymmRel.symmGen_congr_left (since := "2026-01-25")]

Depends on / 依赖: AntisymmRel, AntisymmRel.symmGen_congr, symmGen_congr
-/
theorem AntisymmRel.compRel_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    CompRel (· <= ·) a c ↔ CompRel (· <= ·) b d :=
  AntisymmRel.symmGen_congr h₁ h₂

@[deprecated AntisymmRel.symmGen_congr_left (since := "2026-01-25")]
/--
theorem `AntisymmRel.compRel_congr_left` / 定理 `AntisymmRel.compRel_congr_left`

English:
theorem AntisymmRel.compRel_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  proof: AntisymmRel.symmGen_congr_left h

@[deprecated AntisymmRel.symmGen_congr_right (since := "2026-01-25")]

中文:
定理 AntisymmRel.compRel_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  证明: AntisymmRel.symmGen_congr_left h

@[deprecated AntisymmRel.symmGen_congr_right (since := "2026-01-25")]

Depends on / 依赖: AntisymmRel, AntisymmRel.symmGen_congr_left, symmGen_congr_left
-/
theorem AntisymmRel.compRel_congr_left (h : AntisymmRel (· <= ·) a b) :
    CompRel (· <= ·) a c ↔ CompRel (· <= ·) b c :=
  AntisymmRel.symmGen_congr_left h

@[deprecated AntisymmRel.symmGen_congr_right (since := "2026-01-25")]
/--
theorem `AntisymmRel.compRel_congr_right` / 定理 `AntisymmRel.compRel_congr_right`

English:
theorem AntisymmRel.compRel_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  proof: AntisymmRel.symmGen_congr_right h

中文:
定理 AntisymmRel.compRel_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  证明: AntisymmRel.symmGen_congr_right h

Depends on / 依赖: AntisymmRel, AntisymmRel.symmGen_congr_right, symmGen_congr_right
-/
theorem AntisymmRel.compRel_congr_right (h : AntisymmRel (· <= ·) b c) :
    CompRel (· <= ·) a b ↔ CompRel (· <= ·) a c :=
  AntisymmRel.symmGen_congr_right h

end Preorder

/-- A partial order where any two elements are comparable is a linear order. -/
@[instance_reducible]
/--
Definition of `Relation.linearOrderOfSymmGen` / `Relation.linearOrderOfSymmGen` 的定义

English:
definition Relation.linearOrderOfSymmGen
  signature: [PartialOrder α]
  body: h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT

中文:
定义 关系.linearOrderOfSymmGen
  签名: [偏序 α]
  定义体: h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT
-/
def Relation.linearOrderOfSymmGen [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : forall a b : α, Relation.SymmGen (· <= ·) a b) : LinearOrder α where
  le_total := h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT

/-- A partial order where any two elements are comparable is a linear order. -/
@[deprecated linearOrderOfSymmGen (since := "2026-01-25"), instance_reducible]
/--
Definition of `linearOrderOfComprel` / `linearOrderOfComprel` 的定义

English:
definition linearOrderOfComprel
  signature: [PartialOrder α]
  body: linearOrderOfSymmGen h

中文:
定义 linearOrderOfComprel
  签名: [偏序 α]
  定义体: linearOrderOfSymmGen h

Depends on / 依赖: linearOrderOfSymmGen
-/
def linearOrderOfComprel [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : forall a b : α, CompRel (· <= ·) a b) : LinearOrder α :=
  linearOrderOfSymmGen h

/-! ### Incomparability relation -/

section Relation

variable (r : α -> α -> Prop)

/--
Definition of `IncompRel` / `IncompRel` 的定义

English:
definition IncompRel
  signature: (a b : α)
  body: ¬ r a b ∧ ¬ r b a

@[simp]

中文:
定义 IncompRel
  签名: (a b : α)
  定义体: ¬ r a b ∧ ¬ r b a

@[simp]
-/
def IncompRel (a b : α) : Prop :=
  ¬ r a b ∧ ¬ r b a

@[simp]
/--
theorem `antisymmRel_compl` / 定理 `antisymmRel_compl`

English:
theorem antisymmRel_compl
  statement: AntisymmRel rᶜ = IncompRel r
  proof: rfl

中文:
定理 antisymmRel_compl
  结论: AntisymmRel rᶜ = IncompRel r
  证明: rfl
-/
theorem antisymmRel_compl : AntisymmRel rᶜ = IncompRel r :=
  rfl

/--
theorem `antisymmRel_compl_apply` / 定理 `antisymmRel_compl_apply`

English:
theorem antisymmRel_compl_apply
  statement: AntisymmRel rᶜ a b ↔ IncompRel r a b
  proof: .rfl

@[simp]

中文:
定理 antisymmRel_compl_apply
  结论: AntisymmRel rᶜ a b ↔ IncompRel r a b
  证明: .rfl

@[simp]
-/
theorem antisymmRel_compl_apply : AntisymmRel rᶜ a b ↔ IncompRel r a b :=
  .rfl

@[simp]
/--
theorem `incompRel_compl` / 定理 `incompRel_compl`

English:
theorem incompRel_compl
  statement: IncompRel rᶜ = AntisymmRel r
  proof: by
  simp [← antisymmRel_compl, compl]

@[simp]

中文:
定理 incompRel_compl
  结论: IncompRel rᶜ = AntisymmRel r
  证明: by
  simp [← antisymmRel_compl, compl]

@[simp]

Depends on / 依赖: antisymmRel_compl
-/
theorem incompRel_compl : IncompRel rᶜ = AntisymmRel r := by
  simp [← antisymmRel_compl, compl]

@[simp]
/--
theorem `incompRel_compl_apply` / 定理 `incompRel_compl_apply`

English:
theorem incompRel_compl_apply
  statement: IncompRel rᶜ a b ↔ AntisymmRel r a b
  proof: by
  simp

中文:
定理 incompRel_compl_apply
  结论: IncompRel rᶜ a b ↔ AntisymmRel r a b
  证明: by
  simp
-/
theorem incompRel_compl_apply : IncompRel rᶜ a b ↔ AntisymmRel r a b := by
  simp

/--
theorem `incompRel_swap` / 定理 `incompRel_swap`

English:
theorem incompRel_swap
  statement: IncompRel (swap r) = IncompRel r
  proof: antisymmRel_swap rᶜ

中文:
定理 incompRel_swap
  结论: IncompRel (swap r) = IncompRel r
  证明: antisymmRel_swap rᶜ

Depends on / 依赖: antisymmRel_swap
-/
theorem incompRel_swap : IncompRel (swap r) = IncompRel r :=
  antisymmRel_swap rᶜ

/--
theorem `incompRel_swap_apply` / 定理 `incompRel_swap_apply`

English:
theorem incompRel_swap_apply
  statement: IncompRel (swap r) a b ↔ IncompRel r a b
  proof: antisymmRel_swap_apply rᶜ

@[simp, refl]

中文:
定理 incompRel_swap_apply
  结论: IncompRel (swap r) a b ↔ IncompRel r a b
  证明: antisymmRel_swap_apply rᶜ

@[simp, refl]

Depends on / 依赖: antisymmRel_swap_apply
-/
theorem incompRel_swap_apply : IncompRel (swap r) a b ↔ IncompRel r a b :=
  antisymmRel_swap_apply rᶜ

@[simp, refl]
/--
theorem `IncompRel.refl` / 定理 `IncompRel.refl`

English:
theorem IncompRel.refl
  given: [Std.Irrefl r] (a : α)
  statement: IncompRel r a a
  proof: AntisymmRel.refl rᶜ a

中文:
定理 IncompRel.refl
  条件: [Std.Irrefl r] (a : α)
  结论: IncompRel r a a
  证明: AntisymmRel.refl rᶜ a

Depends on / 依赖: AntisymmRel, AntisymmRel.refl, ConcreteCategory, ConcreteCategory.hom, TopRep
-/
theorem IncompRel.refl [Std.Irrefl r] (a : α) : IncompRel r a a :=
  AntisymmRel.refl rᶜ a

variable {r}

/--
theorem `IncompRel.rfl` / 定理 `IncompRel.rfl`

English:
theorem IncompRel.rfl
  given: [Std.Irrefl r] {a : α}
  statement: IncompRel r a a
  proof: .refl ..

中文:
定理 IncompRel.rfl
  条件: [Std.Irrefl r] {a : α}
  结论: IncompRel r a a
  证明: .refl ..
-/
theorem IncompRel.rfl [Std.Irrefl r] {a : α} : IncompRel r a a := .refl ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] : Std.Refl (IncompRel r) where
  body: .refl r

@[symm]

中文:
实例 [Std.Irrefl
  签名: r] : Std.Refl (IncompRel r) where
  定义体: .refl r

@[symm]
-/
instance [Std.Irrefl r] : Std.Refl (IncompRel r) where
  refl := .refl r

@[symm]
/--
theorem `IncompRel.symm` / 定理 `IncompRel.symm`

English:
theorem IncompRel.symm
  statement: IncompRel r a b -> IncompRel r b a
  proof: And.symm

中文:
定理 IncompRel.symm
  结论: IncompRel r a b -> IncompRel r b a
  证明: And.symm

Depends on / 依赖: And.symm
-/
theorem IncompRel.symm : IncompRel r a b -> IncompRel r b a :=
  And.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (IncompRel r)
  body: IncompRel.symm

中文:
实例 :
  签名: Std.Symm (IncompRel r)
  定义体: IncompRel.symm

Depends on / 依赖: IncompRel, IncompRel.symm
-/
instance : Std.Symm (IncompRel r) where
  symm _ _ := IncompRel.symm

/--
theorem `incompRel_comm` / 定理 `incompRel_comm`

English:
theorem incompRel_comm
  given: {a b : α}
  statement: IncompRel r a b ↔ IncompRel r b a
  proof: comm

中文:
定理 incompRel_comm
  条件: {a b : α}
  结论: IncompRel r a b ↔ IncompRel r b a
  证明: comm
-/
theorem incompRel_comm {a b : α} : IncompRel r a b ↔ IncompRel r b a :=
  comm

/--
Instance `IncompRel.decidableRel` / 实例 `IncompRel.decidableRel`

English:
instance IncompRel.decidableRel
  signature: [DecidableRel r]
  body: fun _ _ => inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

中文:
实例 IncompRel.decidableRel
  签名: [DecidableRel r]
  定义体: fun _ _ => inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

Depends on / 依赖: Decidable
-/
instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ => inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

/--
theorem `IncompRel.not_antisymmRel` / 定理 `IncompRel.not_antisymmRel`

English:
theorem IncompRel.not_antisymmRel
  given: (h : IncompRel r a b)
  statement: ¬ AntisymmRel r a b
  proof: fun h' => h.1 h'.1

中文:
定理 IncompRel.not_antisymmRel
  条件: (h : IncompRel r a b)
  结论: ¬ AntisymmRel r a b
  证明: fun h' => h.1 h'.1
-/
theorem IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b :=
  fun h' => h.1 h'.1

/--
theorem `AntisymmRel.not_incompRel` / 定理 `AntisymmRel.not_incompRel`

English:
theorem AntisymmRel.not_incompRel
  given: (h : AntisymmRel r a b)
  statement: ¬ IncompRel r a b
  proof: fun h' => h'.1 h.1

中文:
定理 AntisymmRel.not_incompRel
  条件: (h : AntisymmRel r a b)
  结论: ¬ IncompRel r a b
  证明: fun h' => h'.1 h.1
-/
theorem AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b :=
  fun h' => h'.1 h.1

/--
theorem `not_symmGen_iff` / 定理 `not_symmGen_iff`

English:
theorem not_symmGen_iff
  statement: ¬ Relation.SymmGen r a b ↔ IncompRel r a b
  proof: by
  simp [Relation.SymmGen, IncompRel]

@[deprecated not_symmGen_iff (since := "2026-01-25")]

中文:
定理 not_symmGen_iff
  结论: ¬ 关系.SymmGen r a b ↔ IncompRel r a b
  证明: by
  simp [Relation.SymmGen, IncompRel]

@[deprecated not_symmGen_iff (since := "2026-01-25")]

Depends on / 依赖: IncompRel, Relation, Relation.SymmGen, SymmGen
-/
theorem not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel r a b := by
  simp [Relation.SymmGen, IncompRel]

@[deprecated not_symmGen_iff (since := "2026-01-25")]
/--
theorem `not_compRel_iff` / 定理 `not_compRel_iff`

English:
theorem not_compRel_iff
  statement: ¬ CompRel r a b ↔ IncompRel r a b
  proof: not_symmGen_iff

中文:
定理 not_compRel_iff
  结论: ¬ CompRel r a b ↔ IncompRel r a b
  证明: not_symmGen_iff

Depends on / 依赖: not_symmGen_iff
-/
theorem not_compRel_iff : ¬ CompRel r a b ↔ IncompRel r a b :=
  not_symmGen_iff

/--
theorem `not_incompRel_iff_symmGen` / 定理 `not_incompRel_iff_symmGen`

English:
theorem not_incompRel_iff_symmGen
  statement: ¬ IncompRel r a b ↔ Relation.SymmGen r a b
  proof: by
  rw [← not_symmGen_iff]; rw [not_not]

@[deprecated not_incompRel_iff_symmGen (since := "2026-01-25")]

中文:
定理 not_incompRel_iff_symmGen
  结论: ¬ IncompRel r a b ↔ 关系.SymmGen r a b
  证明: by
  rw [← not_symmGen_iff]; rw [not_not]

@[deprecated not_incompRel_iff_symmGen (since := "2026-01-25")]

Depends on / 依赖: not_not, not_symmGen_iff
-/
theorem not_incompRel_iff_symmGen : ¬ IncompRel r a b ↔ Relation.SymmGen r a b := by
  rw [← not_symmGen_iff]; rw [not_not]

@[deprecated not_incompRel_iff_symmGen (since := "2026-01-25")]
/--
theorem `not_incompRel_iff` / 定理 `not_incompRel_iff`

English:
theorem not_incompRel_iff
  statement: ¬ IncompRel r a b ↔ CompRel r a b
  proof: not_incompRel_iff_symmGen

@[simp]

中文:
定理 not_incompRel_iff
  结论: ¬ IncompRel r a b ↔ CompRel r a b
  证明: not_incompRel_iff_symmGen

@[simp]

Depends on / 依赖: not_incompRel_iff_symmGen
-/
theorem not_incompRel_iff : ¬ IncompRel r a b ↔ CompRel r a b :=
  not_incompRel_iff_symmGen

@[simp]
/--
theorem `not_incompRel_of_total` / 定理 `not_incompRel_of_total`

English:
theorem not_incompRel_of_total
  given: [Std.Total r] (a b : α)
  statement: ¬ IncompRel r a b
  proof: by
  rw [not_incompRel_iff_symmGen]
  exact symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.not_incompRel := not_incompRel_of_total

中文:
定理 not_incompRel_of_total
  条件: [Std.全 r] (a b : α)
  结论: ¬ IncompRel r a b
  证明: by
  rw [not_incompRel_iff_symmGen]
  exact symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.not_incompRel := not_incompRel_of_total

Depends on / 依赖: not_incompRel_iff_symmGen, symmGen_of_total
-/
theorem not_incompRel_of_total [Std.Total r] (a b : α) : ¬ IncompRel r a b := by
  rw [not_incompRel_iff_symmGen]
  exact symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.not_incompRel := not_incompRel_of_total

/--
theorem `IncompRel.ne` / 定理 `IncompRel.ne`

English:
theorem IncompRel.ne
  given: [Std.Refl r] {a b : α} (h : IncompRel r a b)
  statement: a != b
  proof: by
  rintro rfl
exact h.1 refl_of r a

中文:
定理 IncompRel.ne
  条件: [Std.Refl r] {a b : α} (h : IncompRel r a b)
  结论: a != b
  证明: by
  rintro rfl
exact h.1 refl_of r a

Depends on / 依赖: refl_of
-/
theorem IncompRel.ne [Std.Refl r] {a b : α} (h : IncompRel r a b) : a != b := by
  rintro rfl
exact h.1 refl_of r a

end Relation

section LE

variable [LE α]

/--
theorem `IncompRel.not_le` / 定理 `IncompRel.not_le`

English:
theorem IncompRel.not_le
  given: (h : IncompRel (· <= ·) a b)
  statement: ¬ a <= b
  proof: h.1

中文:
定理 IncompRel.not_le
  条件: (h : IncompRel (· <= ·) a b)
  结论: ¬ a <= b
  证明: h.1
-/
theorem IncompRel.not_le (h : IncompRel (· <= ·) a b) : ¬ a <= b := h.1
/--
theorem `IncompRel.not_ge` / 定理 `IncompRel.not_ge`

English:
theorem IncompRel.not_ge
  given: (h : IncompRel (· <= ·) a b)
  statement: ¬ b <= a
  proof: h.2

中文:
定理 IncompRel.not_ge
  条件: (h : IncompRel (· <= ·) a b)
  结论: ¬ b <= a
  证明: h.2
-/
theorem IncompRel.not_ge (h : IncompRel (· <= ·) a b) : ¬ b <= a := h.2
/--
theorem `LE.le.not_incompRel` / 定理 `LE.le.not_incompRel`

English:
theorem LE.le.not_incompRel
  given: (h : a <= b)
  statement: ¬ IncompRel (· <= ·) a b
  proof: fun h' => h'.not_le h

中文:
定理 LE.le.not_incompRel
  条件: (h : a <= b)
  结论: ¬ IncompRel (· <= ·) a b
  证明: fun h' => h'.not_le h

Depends on / 依赖: not_le
-/
theorem LE.le.not_incompRel (h : a <= b) : ¬ IncompRel (· <= ·) a b := fun h' => h'.not_le h

end LE

section Preorder

variable [Preorder α]

/--
theorem `IncompRel.not_lt` / 定理 `IncompRel.not_lt`

English:
theorem IncompRel.not_lt
  given: (h : IncompRel (· <= ·) a b)
  statement: ¬ a < b
  proof: mt le_of_lt h.not_le

中文:
定理 IncompRel.not_lt
  条件: (h : IncompRel (· <= ·) a b)
  结论: ¬ a < b
  证明: mt le_of_lt h.not_le

Depends on / 依赖: h.not_le, le_of_lt, not_le
-/
theorem IncompRel.not_lt (h : IncompRel (· <= ·) a b) : ¬ a < b := mt le_of_lt h.not_le
/--
theorem `IncompRel.not_gt` / 定理 `IncompRel.not_gt`

English:
theorem IncompRel.not_gt
  given: (h : IncompRel (· <= ·) a b)
  statement: ¬ b < a
  proof: mt le_of_lt h.not_ge

中文:
定理 IncompRel.not_gt
  条件: (h : IncompRel (· <= ·) a b)
  结论: ¬ b < a
  证明: mt le_of_lt h.not_ge

Depends on / 依赖: h.not_ge, le_of_lt, not_ge
-/
theorem IncompRel.not_gt (h : IncompRel (· <= ·) a b) : ¬ b < a := mt le_of_lt h.not_ge
/--
theorem `LT.lt.not_incompRel` / 定理 `LT.lt.not_incompRel`

English:
theorem LT.lt.not_incompRel
  given: (h : a < b)
  statement: ¬ IncompRel (· <= ·) a b
  proof: fun h' => h'.not_lt h

中文:
定理 LT.lt.not_incompRel
  条件: (h : a < b)
  结论: ¬ IncompRel (· <= ·) a b
  证明: fun h' => h'.not_lt h

Depends on / 依赖: not_lt
-/
theorem LT.lt.not_incompRel (h : a < b) : ¬ IncompRel (· <= ·) a b := fun h' => h'.not_lt h

/--
theorem `not_le_iff_lt_or_incompRel` / 定理 `not_le_iff_lt_or_incompRel`

English:
theorem not_le_iff_lt_or_incompRel
  statement: ¬ b <= a ↔ a < b ∨ IncompRel (· <= ·) a b
  proof: by
  rw [lt_iff_le_not_ge]; rw [IncompRel]
  tauto

中文:
定理 not_le_iff_lt_or_incompRel
  结论: ¬ b <= a ↔ a < b ∨ IncompRel (· <= ·) a b
  证明: by
  rw [lt_iff_le_not_ge]; rw [IncompRel]
  tauto

Depends on / 依赖: IncompRel, lt_iff_le_not_ge
-/
theorem not_le_iff_lt_or_incompRel : ¬ b <= a ↔ a < b ∨ IncompRel (· <= ·) a b := by
  rw [lt_iff_le_not_ge]; rw [IncompRel]
  tauto

/--
theorem `lt_or_antisymmRel_or_gt_or_incompRel` / 定理 `lt_or_antisymmRel_or_gt_or_incompRel`

English:
theorem lt_or_antisymmRel_or_gt_or_incompRel
  given: (a b : α)
  proof: by
  simp_rw [lt_iff_le_not_ge]
  tauto

@[trans]

中文:
定理 lt_or_antisymmRel_or_gt_or_incompRel
  条件: (a b : α)
  证明: by
  simp_rw [lt_iff_le_not_ge]
  tauto

@[trans]

Depends on / 依赖: lt_iff_le_not_ge, simp_rw
-/
theorem lt_or_antisymmRel_or_gt_or_incompRel (a b : α) :
    a < b ∨ AntisymmRel (· <= ·) a b ∨ b < a ∨ IncompRel (· <= ·) a b := by
  simp_rw [lt_iff_le_not_ge]
  tauto

@[trans]
/--
theorem `incompRel_of_incompRel_of_antisymmRel` / 定理 `incompRel_of_incompRel_of_antisymmRel`

English:
theorem incompRel_of_incompRel_of_antisymmRel
  proof: ⟨fun h => h₁.not_le (h.trans h₂.ge), fun h => h₁.not_ge (h₂.le.trans h)⟩

alias IncompRel.trans_antisymmRel := incompRel_of_incompRel_of_antisymmRel

中文:
定理 incompRel_of_incompRel_of_antisymmRel
  证明: ⟨fun h => h₁.not_le (h.trans h₂.ge), fun h => h₁.not_ge (h₂.le.trans h)⟩

alias IncompRel.trans_antisymmRel := incompRel_of_incompRel_of_antisymmRel

Depends on / 依赖: h.trans, le.trans, not_ge, not_le
-/
theorem incompRel_of_incompRel_of_antisymmRel
    (h₁ : IncompRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) b c) : IncompRel (· <= ·) a c :=
  ⟨fun h => h₁.not_le (h.trans h₂.ge), fun h => h₁.not_ge (h₂.le.trans h)⟩

alias IncompRel.trans_antisymmRel := incompRel_of_incompRel_of_antisymmRel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (IncompRel (· <= ·)) (AntisymmRel (· <= ·)) (IncompRel (· <= ·))
  body: incompRel_of_incompRel_of_antisymmRel

@[trans]

中文:
实例 :
  签名: @Trans α α α (IncompRel (· <= ·)) (AntisymmRel (· <= ·)) (IncompRel (· <= ·))
  定义体: incompRel_of_incompRel_of_antisymmRel

@[trans]

Depends on / 依赖: incompRel_of_incompRel_of_antisymmRel
-/
instance : @Trans α α α (IncompRel (· <= ·)) (AntisymmRel (· <= ·)) (IncompRel (· <= ·)) where
  trans := incompRel_of_incompRel_of_antisymmRel

@[trans]
/--
theorem `incompRel_of_antisymmRel_of_incompRel` / 定理 `incompRel_of_antisymmRel_of_incompRel`

English:
theorem incompRel_of_antisymmRel_of_incompRel
  proof: (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_incompRel := incompRel_of_antisymmRel_of_incompRel

中文:
定理 incompRel_of_antisymmRel_of_incompRel
  证明: (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_incompRel := incompRel_of_antisymmRel_of_incompRel

Depends on / 依赖: symm.trans_antisymmRel, trans_antisymmRel
-/
theorem incompRel_of_antisymmRel_of_incompRel
    (h₁ : AntisymmRel (· <= ·) a b) (h₂ : IncompRel (· <= ·) b c) : IncompRel (· <= ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_incompRel := incompRel_of_antisymmRel_of_incompRel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (AntisymmRel (· <= ·)) (IncompRel (· <= ·)) (IncompRel (· <= ·))
  body: incompRel_of_antisymmRel_of_incompRel

中文:
实例 :
  签名: @Trans α α α (AntisymmRel (· <= ·)) (IncompRel (· <= ·)) (IncompRel (· <= ·))
  定义体: incompRel_of_antisymmRel_of_incompRel

Depends on / 依赖: incompRel_of_antisymmRel_of_incompRel
-/
instance : @Trans α α α (AntisymmRel (· <= ·)) (IncompRel (· <= ·)) (IncompRel (· <= ·)) where
  trans := incompRel_of_antisymmRel_of_incompRel

/--
theorem `AntisymmRel.incompRel_congr` / 定理 `AntisymmRel.incompRel_congr`

English:
theorem AntisymmRel.incompRel_congr
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  proof: (h₁.symm.trans_incompRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_incompRel h).trans_antisymmRel h₂.symm

中文:
定理 AntisymmRel.incompRel_congr
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  证明: (h₁.symm.trans_incompRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_incompRel h).trans_antisymmRel h₂.symm

Depends on / 依赖: symm.trans_incompRel, trans_antisymmRel, trans_incompRel
-/
theorem AntisymmRel.incompRel_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    IncompRel (· <= ·) a c ↔ IncompRel (· <= ·) b d where
  mp h := (h₁.symm.trans_incompRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_incompRel h).trans_antisymmRel h₂.symm

/--
theorem `AntisymmRel.incompRel_congr_left` / 定理 `AntisymmRel.incompRel_congr_left`

English:
theorem AntisymmRel.incompRel_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  proof: h.incompRel_congr AntisymmRel.rfl

中文:
定理 AntisymmRel.incompRel_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  证明: h.incompRel_congr AntisymmRel.rfl

Depends on / 依赖: AntisymmRel, AntisymmRel.rfl, h.incompRel_congr, incompRel_congr
-/
theorem AntisymmRel.incompRel_congr_left (h : AntisymmRel (· <= ·) a b) :
    IncompRel (· <= ·) a c ↔ IncompRel (· <= ·) b c :=
  h.incompRel_congr AntisymmRel.rfl

/--
theorem `AntisymmRel.incompRel_congr_right` / 定理 `AntisymmRel.incompRel_congr_right`

English:
theorem AntisymmRel.incompRel_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  proof: AntisymmRel.rfl.incompRel_congr h

中文:
定理 AntisymmRel.incompRel_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  证明: AntisymmRel.rfl.incompRel_congr h

Depends on / 依赖: AntisymmRel, AntisymmRel.rfl.incompRel_congr, incompRel_congr
-/
theorem AntisymmRel.incompRel_congr_right (h : AntisymmRel (· <= ·) b c) :
    IncompRel (· <= ·) a b ↔ IncompRel (· <= ·) a c :=
  AntisymmRel.rfl.incompRel_congr h

end Preorder

/--
theorem `lt_or_eq_or_gt_or_incompRel` / 定理 `lt_or_eq_or_gt_or_incompRel`

English:
theorem lt_or_eq_or_gt_or_incompRel
  given: [PartialOrder α] (a b : α)
  proof: by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b

中文:
定理 lt_or_eq_or_gt_or_incompRel
  条件: [偏序 α] (a b : α)
  证明: by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b

Depends on / 依赖: lt_or_antisymmRel_or_gt_or_incompRel
-/
theorem lt_or_eq_or_gt_or_incompRel [PartialOrder α] (a b : α) :
    a < b ∨ a = b ∨ b < a ∨ IncompRel (· <= ·) a b := by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b
