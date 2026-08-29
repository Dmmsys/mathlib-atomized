/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.Real.Basic

/-!

# Predicates on monomials

In this file we define `UnitMonomial`: type to represent monomials without coefficient as a list of
its exponents. `[e₁, e₂, ..., eₙ]` corresponds to `basis[0] ^ e₁ * ... * basis[n] ^ eₙ` where
`basis` is the basis of functions.

Then we define some predicates for these lists:
1. `FirstNonzeroIsPos li` means that the first non-zero element of the list `li` is positive.
2. `FirstNonzeroIsNeg li` means that the first non-zero element of the list `li` is negative.
3. `AllZero li` means that all elements in `li` are zero.

This trichotomy determines the asymptotic behaviour of a monomial:
`FirstNonzeroIsPos` means it tends to infinity, `FirstNonzeroIsNeg` means it tends to zero and
`AllZero` means it tends to a constant.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

/--
Definition of `UnitMonomial` / `UnitMonomial` 的定义

English:
abbreviation UnitMonomial
  body: List Real

中文:
缩写 UnitMonomial
  定义体: List Real
-/
abbrev UnitMonomial := List Real

namespace UnitMonomial

/--
Inductive type `Sign` / 归纳类型 `Sign`

English:
inductive Sign
  constructors (1):
    - pos: | neg | zero

中文:
归纳类型 Sign
  构造子 (1 个):
    - pos: | neg | zero
-/
inductive Sign
| pos | neg | zero

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: : UnitMonomial -> Sign

中文:
定义 sign
  签名: : UnitMonomial -> Sign
-/
noncomputable def sign : UnitMonomial -> Sign
  | [] => .zero
  | hd :: tl =>
    if 0 < hd then
      .pos
    else if hd < 0 then
      .neg
    else
      sign tl

/--
Definition of `FirstNonzeroIsPos` / `FirstNonzeroIsPos` 的定义

English:
definition FirstNonzeroIsPos
  signature: (m : UnitMonomial)
  body: m.sign = .pos

中文:
定义 FirstNonzeroIsPos
  签名: (m : UnitMonomial)
  定义体: m.sign = .pos

Depends on / 依赖: m.sign
-/
def FirstNonzeroIsPos (m : UnitMonomial) : Prop := m.sign = .pos

/--
Definition of `FirstNonzeroIsNeg` / `FirstNonzeroIsNeg` 的定义

English:
definition FirstNonzeroIsNeg
  signature: (m : UnitMonomial)
  body: m.sign = .neg

中文:
定义 FirstNonzeroIsNeg
  签名: (m : UnitMonomial)
  定义体: m.sign = .neg

Depends on / 依赖: m.sign
-/
def FirstNonzeroIsNeg (m : UnitMonomial) : Prop := m.sign = .neg

/--
Definition of `AllZero` / `AllZero` 的定义

English:
definition AllZero
  signature: (m : UnitMonomial)
  body: m.sign = .zero

中文:
定义 AllZero
  签名: (m : UnitMonomial)
  定义体: m.sign = .zero

Depends on / 依赖: m.sign
-/
def AllZero (m : UnitMonomial) : Prop := m.sign = .zero

namespace AllZero

/--
theorem `nil` / 定理 `nil`

English:
theorem nil
  statement: AllZero []
  proof: rfl

@[simp]

中文:
定理 nil
  结论: AllZero []
  证明: rfl

@[simp]
-/
theorem nil : AllZero [] :=
  rfl

@[simp]
/--
theorem `cons_iff` / 定理 `cons_iff`

English:
theorem cons_iff
  given: {hd : Real} {tl : UnitMonomial}
  proof: by
  grind [AllZero, sign]

中文:
定理 cons_iff
  条件: {hd : 实数} {tl : UnitMonomial}
  证明: by
  grind [AllZero, sign]

Depends on / 依赖: AllZero
-/
theorem cons_iff {hd : Real} {tl : UnitMonomial} :
    AllZero (hd :: tl) ↔ hd = 0 ∧ AllZero tl := by
  grind [AllZero, sign]

/--
theorem `of_tail` / 定理 `of_tail`

English:
theorem of_tail
  given: {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl)
  proof: cons_iff.mpr ⟨h_hd, h_tl⟩

中文:
定理 of_tail
  条件: {hd : 实数} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl)
  证明: cons_iff.mpr ⟨h_hd, h_tl⟩

Depends on / 依赖: cons_iff, cons_iff.mpr, h_hd, h_tl
-/
theorem of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) :=
  cons_iff.mpr ⟨h_hd, h_tl⟩

/--
theorem `replicate` / 定理 `replicate`

English:
theorem replicate
  given: {n : Nat}
  statement: AllZero (List.replicate n 0)
  proof: by
  induction n <;> grind [AllZero, sign]

中文:
定理 replicate
  条件: {n : 自然数}
  结论: AllZero (List.replicate n 0)
  证明: by
  induction n <;> grind [AllZero, sign]

Depends on / 依赖: AllZero
-/
theorem replicate {n : Nat} : AllZero (List.replicate n 0) := by
  induction n <;> grind [AllZero, sign]

/--
theorem `not_FirstNonzeroIsPos` / 定理 `not_FirstNonzeroIsPos`

English:
theorem not_FirstNonzeroIsPos
  given: {li : UnitMonomial} (h : AllZero li)
  proof: by
  grind [AllZero, FirstNonzeroIsPos]

中文:
定理 not_FirstNonzeroIsPos
  条件: {li : UnitMonomial} (h : AllZero li)
  证明: by
  grind [AllZero, FirstNonzeroIsPos]

Depends on / 依赖: AllZero, FirstNonzeroIsPos
-/
theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsPos li := by
  grind [AllZero, FirstNonzeroIsPos]

/--
theorem `not_FirstNonzeroIsNeg` / 定理 `not_FirstNonzeroIsNeg`

English:
theorem not_FirstNonzeroIsNeg
  given: {li : UnitMonomial} (h : AllZero li)
  proof: by
  grind [AllZero, FirstNonzeroIsNeg]

中文:
定理 not_FirstNonzeroIsNeg
  条件: {li : UnitMonomial} (h : AllZero li)
  证明: by
  grind [AllZero, FirstNonzeroIsNeg]

Depends on / 依赖: AllZero, FirstNonzeroIsNeg
-/
theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : AllZero li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [AllZero, FirstNonzeroIsNeg]

end AllZero

namespace FirstNonzeroIsPos

@[simp]
/--
theorem `not_nil` / 定理 `not_nil`

English:
theorem not_nil
  statement: ¬ FirstNonzeroIsPos []
  proof: by simp [FirstNonzeroIsPos, sign]

@[simp]

中文:
定理 not_nil
  结论: ¬ FirstNonzeroIsPos []
  证明: by simp [FirstNonzeroIsPos, sign]

@[simp]

Depends on / 依赖: FirstNonzeroIsPos
-/
theorem not_nil : ¬ FirstNonzeroIsPos [] := by simp [FirstNonzeroIsPos, sign]

@[simp]
/--
theorem `cons_iff` / 定理 `cons_iff`

English:
theorem cons_iff
  given: {hd : Real} {tl : UnitMonomial}
  proof: by
  grind [FirstNonzeroIsPos, sign]

中文:
定理 cons_iff
  条件: {hd : 实数} {tl : UnitMonomial}
  证明: by
  grind [FirstNonzeroIsPos, sign]

Depends on / 依赖: FirstNonzeroIsPos
-/
theorem cons_iff {hd : Real} {tl : UnitMonomial} :
    FirstNonzeroIsPos (hd :: tl) ↔ 0 < hd ∨ (hd = 0 ∧ FirstNonzeroIsPos tl) := by
  grind [FirstNonzeroIsPos, sign]

/--
theorem `of_head` / 定理 `of_head`

English:
theorem of_head
  given: {hd : Real} (tl : UnitMonomial) (h_hd : 0 < hd)
  proof: by
  simp [h_hd]

中文:
定理 of_head
  条件: {hd : 实数} (tl : UnitMonomial) (h_hd : 0 < hd)
  证明: by
  simp [h_hd]

Depends on / 依赖: h_hd
-/
theorem of_head {hd : Real} (tl : UnitMonomial) (h_hd : 0 < hd) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd]

/--
theorem `of_tail` / 定理 `of_tail`

English:
theorem of_tail
  statement: {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0)
  proof: by
  simp [h_hd, h_tl]

中文:
定理 of_tail
  结论: {hd : 实数} {tl : UnitMonomial} (h_hd : hd = 0)
  证明: by
  simp [h_hd, h_tl]

Depends on / 依赖: h_hd, h_tl
-/
theorem of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0)
    (h_tl : FirstNonzeroIsPos tl) :
    FirstNonzeroIsPos (hd :: tl) := by
  simp [h_hd, h_tl]

/--
theorem `not_AllZero` / 定理 `not_AllZero`

English:
theorem not_AllZero
  given: {li : UnitMonomial} (h : FirstNonzeroIsPos li)
  proof: fun h' => h'.not_FirstNonzeroIsPos h

中文:
定理 not_AllZero
  条件: {li : UnitMonomial} (h : FirstNonzeroIsPos li)
  证明: fun h' => h'.not_FirstNonzeroIsPos h

Depends on / 依赖: not_FirstNonzeroIsPos
-/
theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ AllZero li :=
  fun h' => h'.not_FirstNonzeroIsPos h

/--
theorem `not_FirstNonzeroIsNeg` / 定理 `not_FirstNonzeroIsNeg`

English:
theorem not_FirstNonzeroIsNeg
  given: {li : UnitMonomial} (h : FirstNonzeroIsPos li)
  proof: by
  grind [FirstNonzeroIsPos, FirstNonzeroIsNeg]

中文:
定理 not_FirstNonzeroIsNeg
  条件: {li : UnitMonomial} (h : FirstNonzeroIsPos li)
  证明: by
  grind [FirstNonzeroIsPos, FirstNonzeroIsNeg]

Depends on / 依赖: FirstNonzeroIsNeg, FirstNonzeroIsPos
-/
theorem not_FirstNonzeroIsNeg {li : UnitMonomial} (h : FirstNonzeroIsPos li) :
    ¬ FirstNonzeroIsNeg li := by
  grind [FirstNonzeroIsPos, FirstNonzeroIsNeg]

end FirstNonzeroIsPos

namespace FirstNonzeroIsNeg

@[simp]
/--
theorem `not_nil` / 定理 `not_nil`

English:
theorem not_nil
  statement: ¬ FirstNonzeroIsNeg []
  proof: by simp [FirstNonzeroIsNeg, sign]

@[simp]

中文:
定理 not_nil
  结论: ¬ FirstNonzeroIsNeg []
  证明: by simp [FirstNonzeroIsNeg, sign]

@[simp]

Depends on / 依赖: FirstNonzeroIsNeg
-/
theorem not_nil : ¬ FirstNonzeroIsNeg [] := by simp [FirstNonzeroIsNeg, sign]

@[simp]
/--
theorem `cons_iff` / 定理 `cons_iff`

English:
theorem cons_iff
  given: {hd : Real} {tl : UnitMonomial}
  proof: by
  grind [FirstNonzeroIsNeg, sign]

中文:
定理 cons_iff
  条件: {hd : 实数} {tl : UnitMonomial}
  证明: by
  grind [FirstNonzeroIsNeg, sign]

Depends on / 依赖: FirstNonzeroIsNeg
-/
theorem cons_iff {hd : Real} {tl : UnitMonomial} :
    FirstNonzeroIsNeg (hd :: tl) ↔ hd < 0 ∨ (hd = 0 ∧ FirstNonzeroIsNeg tl) := by
  grind [FirstNonzeroIsNeg, sign]

/--
theorem `of_head` / 定理 `of_head`

English:
theorem of_head
  given: {hd : Real} (tl : UnitMonomial) (h_hd : hd < 0)
  proof: by
  simp [h_hd]

中文:
定理 of_head
  条件: {hd : 实数} (tl : UnitMonomial) (h_hd : hd < 0)
  证明: by
  simp [h_hd]

Depends on / 依赖: h_hd
-/
theorem of_head {hd : Real} (tl : UnitMonomial) (h_hd : hd < 0) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd]

/--
theorem `of_tail` / 定理 `of_tail`

English:
theorem of_tail
  given: {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonzeroIsNeg tl)
  proof: by
  simp [h_hd, h_tl]

中文:
定理 of_tail
  条件: {hd : 实数} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonzeroIsNeg tl)
  证明: by
  simp [h_hd, h_tl]

Depends on / 依赖: h_hd, h_tl
-/
theorem of_tail {hd : Real} {tl : UnitMonomial} (h_hd : hd = 0) (h_tl : FirstNonzeroIsNeg tl) :
    FirstNonzeroIsNeg (hd :: tl) := by
  simp [h_hd, h_tl]

/--
theorem `not_AllZero` / 定理 `not_AllZero`

English:
theorem not_AllZero
  given: {li : UnitMonomial} (h : FirstNonzeroIsNeg li)
  proof: fun h' => h'.not_FirstNonzeroIsNeg h

中文:
定理 not_AllZero
  条件: {li : UnitMonomial} (h : FirstNonzeroIsNeg li)
  证明: fun h' => h'.not_FirstNonzeroIsNeg h

Depends on / 依赖: not_FirstNonzeroIsNeg
-/
theorem not_AllZero {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ AllZero li :=
  fun h' => h'.not_FirstNonzeroIsNeg h

/--
theorem `not_FirstNonzeroIsPos` / 定理 `not_FirstNonzeroIsPos`

English:
theorem not_FirstNonzeroIsPos
  given: {li : UnitMonomial} (h : FirstNonzeroIsNeg li)
  proof: fun h' => h'.not_FirstNonzeroIsNeg h

中文:
定理 not_FirstNonzeroIsPos
  条件: {li : UnitMonomial} (h : FirstNonzeroIsNeg li)
  证明: fun h' => h'.not_FirstNonzeroIsNeg h

Depends on / 依赖: not_FirstNonzeroIsNeg
-/
theorem not_FirstNonzeroIsPos {li : UnitMonomial} (h : FirstNonzeroIsNeg li) :
    ¬ FirstNonzeroIsPos li :=
  fun h' => h'.not_FirstNonzeroIsNeg h

end FirstNonzeroIsNeg

end Tactic.ComputeAsymptotics.UnitMonomial
