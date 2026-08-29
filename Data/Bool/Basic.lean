/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Booleans

This file proves various trivial lemmas about Booleans and their
relation to decidable propositions.

## Tags
bool, boolean, Bool, De Morgan

-/

@[expose] public section

namespace Bool

section


/--
theorem `true_eq_false_eq_False` / 定理 `true_eq_false_eq_False`

English:
theorem true_eq_false_eq_False
  statement: ¬(true = false)
  proof: by decide

中文:
定理 true_eq_false_eq_False
  结论: ¬(true = false)
  证明: by decide
-/
theorem true_eq_false_eq_False : ¬(true = false) := by decide

/--
theorem `false_eq_true_eq_False` / 定理 `false_eq_true_eq_False`

English:
theorem false_eq_true_eq_False
  statement: ¬(false = true)
  proof: by decide

中文:
定理 false_eq_true_eq_False
  结论: ¬(false = true)
  证明: by decide
-/
theorem false_eq_true_eq_False : ¬(false = true) := by decide

/--
theorem `eq_false_eq_not_eq_true` / 定理 `eq_false_eq_not_eq_true`

English:
theorem eq_false_eq_not_eq_true
  given: (b : Bool)
  statement: (¬(b = true)) = (b = false)
  proof: by simp

中文:
定理 eq_false_eq_not_eq_true
  条件: (b : 布尔值)
  结论: (¬(b = true)) = (b = false)
  证明: by simp
-/
theorem eq_false_eq_not_eq_true (b : Bool) : (¬(b = true)) = (b = false) := by simp

/--
theorem `eq_true_eq_not_eq_false` / 定理 `eq_true_eq_not_eq_false`

English:
theorem eq_true_eq_not_eq_false
  given: (b : Bool)
  statement: (¬(b = false)) = (b = true)
  proof: by simp

中文:
定理 eq_true_eq_not_eq_false
  条件: (b : 布尔值)
  结论: (¬(b = false)) = (b = true)
  证明: by simp
-/
theorem eq_true_eq_not_eq_false (b : Bool) : (¬(b = false)) = (b = true) := by simp

/--
theorem `eq_false_of_not_eq_true` / 定理 `eq_false_of_not_eq_true`

English:
theorem eq_false_of_not_eq_true
  given: {b : Bool}
  statement: ¬b = true -> b = false
  proof: Eq.mp (eq_false_eq_not_eq_true b)

中文:
定理 eq_false_of_not_eq_true
  条件: {b : 布尔值}
  结论: ¬b = true -> b = false
  证明: Eq.mp (eq_false_eq_not_eq_true b)

Depends on / 依赖: Eq.mp, eq_false_eq_not_eq_true
-/
theorem eq_false_of_not_eq_true {b : Bool} : ¬b = true -> b = false :=
  Eq.mp (eq_false_eq_not_eq_true b)

/--
theorem `eq_true_of_not_eq_false` / 定理 `eq_true_of_not_eq_false`

English:
theorem eq_true_of_not_eq_false
  given: {b : Bool}
  statement: ¬b = false -> b = true
  proof: Eq.mp (eq_true_eq_not_eq_false b)

中文:
定理 eq_true_of_not_eq_false
  条件: {b : 布尔值}
  结论: ¬b = false -> b = true
  证明: Eq.mp (eq_true_eq_not_eq_false b)

Depends on / 依赖: Eq.mp, eq_true_eq_not_eq_false
-/
theorem eq_true_of_not_eq_false {b : Bool} : ¬b = false -> b = true :=
  Eq.mp (eq_true_eq_not_eq_false b)

/--
theorem `and_eq_true_eq_eq_true_and_eq_true` / 定理 `and_eq_true_eq_eq_true_and_eq_true`

English:
theorem and_eq_true_eq_eq_true_and_eq_true
  given: (a b : Bool)
  proof: by simp

中文:
定理 and_eq_true_eq_eq_true_and_eq_true
  条件: (a b : 布尔值)
  证明: by simp
-/
theorem and_eq_true_eq_eq_true_and_eq_true (a b : Bool) :
    ((a && b) = true) = (a = true ∧ b = true) := by simp

/--
theorem `or_eq_true_eq_eq_true_or_eq_true` / 定理 `or_eq_true_eq_eq_true_or_eq_true`

English:
theorem or_eq_true_eq_eq_true_or_eq_true
  given: (a b : Bool)
  proof: by simp

中文:
定理 or_eq_true_eq_eq_true_or_eq_true
  条件: (a b : 布尔值)
  证明: by simp
-/
theorem or_eq_true_eq_eq_true_or_eq_true (a b : Bool) :
    ((a || b) = true) = (a = true ∨ b = true) := by simp

/--
theorem `not_eq_true_eq_eq_false` / 定理 `not_eq_true_eq_eq_false`

English:
theorem not_eq_true_eq_eq_false
  given: (a : Bool)
  statement: (not a = true) = (a = false)
  proof: by grind

中文:
定理 not_eq_true_eq_eq_false
  条件: (a : 布尔值)
  结论: (not a = true) = (a = false)
  证明: by grind
-/
theorem not_eq_true_eq_eq_false (a : Bool) : (not a = true) = (a = false) := by grind

/--
theorem `and_eq_false_eq_eq_false_or_eq_false` / 定理 `and_eq_false_eq_eq_false_or_eq_false`

English:
theorem and_eq_false_eq_eq_false_or_eq_false
  given: (a b : Bool)
  proof: by grind

中文:
定理 and_eq_false_eq_eq_false_or_eq_false
  条件: (a b : 布尔值)
  证明: by grind
-/
theorem and_eq_false_eq_eq_false_or_eq_false (a b : Bool) :
    ((a && b) = false) = (a = false ∨ b = false) := by grind

/--
theorem `or_eq_false_eq_eq_false_and_eq_false` / 定理 `or_eq_false_eq_eq_false_and_eq_false`

English:
theorem or_eq_false_eq_eq_false_and_eq_false
  given: (a b : Bool)
  proof: by grind

中文:
定理 or_eq_false_eq_eq_false_and_eq_false
  条件: (a b : 布尔值)
  证明: by grind
-/
theorem or_eq_false_eq_eq_false_and_eq_false (a b : Bool) :
    ((a || b) = false) = (a = false ∧ b = false) := by grind

/--
theorem `not_eq_false_eq_eq_true` / 定理 `not_eq_false_eq_eq_true`

English:
theorem not_eq_false_eq_eq_true
  given: (a : Bool)
  statement: (not a = false) = (a = true)
  proof: by grind

中文:
定理 not_eq_false_eq_eq_true
  条件: (a : 布尔值)
  结论: (not a = false) = (a = true)
  证明: by grind
-/
theorem not_eq_false_eq_eq_true (a : Bool) : (not a = false) = (a = true) := by grind

/--
theorem `coe_false` / 定理 `coe_false`

English:
theorem coe_false
  statement: ↑false = False
  proof: by simp

中文:
定理 coe_false
  结论: ↑false = 假
  证明: by simp
-/
theorem coe_false : ↑false = False := by simp

/--
theorem `coe_true` / 定理 `coe_true`

English:
theorem coe_true
  statement: ↑true = True
  proof: by simp

中文:
定理 coe_true
  结论: ↑true = 真
  证明: by simp
-/
theorem coe_true : ↑true = True := by simp

/--
theorem `coe_sort_false` / 定理 `coe_sort_false`

English:
theorem coe_sort_false
  statement: (false : Prop) = False
  proof: by simp

中文:
定理 coe_sort_false
  结论: (false : 命题) = 假
  证明: by simp
-/
theorem coe_sort_false : (false : Prop) = False := by simp

/--
theorem `coe_sort_true` / 定理 `coe_sort_true`

English:
theorem coe_sort_true
  statement: (true : Prop) = True
  proof: by simp

中文:
定理 coe_sort_true
  结论: (true : 命题) = 真
  证明: by simp
-/
theorem coe_sort_true : (true : Prop) = True := by simp

/--
theorem `decide_iff` / 定理 `decide_iff`

English:
theorem decide_iff
  given: (p : Prop) [d : Decidable p]
  statement: decide p = true ↔ p
  proof: by simp

中文:
定理 decide_iff
  条件: (p : 命题) [d : 可判定 p]
  结论: decide p = true ↔ p
  证明: by simp
-/
theorem decide_iff (p : Prop) [d : Decidable p] : decide p = true ↔ p := by simp

/--
theorem `decide_true` / 定理 `decide_true`

English:
theorem decide_true
  given: {p : Prop} [Decidable p]
  statement: p -> decide p
  proof: (decide_iff p).2

中文:
定理 decide_true
  条件: {p : 命题} [可判定 p]
  结论: p -> decide p
  证明: (decide_iff p).2

Depends on / 依赖: decide_iff
-/
theorem decide_true {p : Prop} [Decidable p] : p -> decide p :=
  (decide_iff p).2

/--
theorem `of_decide_true` / 定理 `of_decide_true`

English:
theorem of_decide_true
  given: {p : Prop} [Decidable p]
  statement: decide p -> p
  proof: (decide_iff p).1

中文:
定理 of_decide_true
  条件: {p : 命题} [可判定 p]
  结论: decide p -> p
  证明: (decide_iff p).1

Depends on / 依赖: decide_iff
-/
theorem of_decide_true {p : Prop} [Decidable p] : decide p -> p :=
  (decide_iff p).1

/--
theorem `bool_iff_false` / 定理 `bool_iff_false`

English:
theorem bool_iff_false
  given: {b : Bool}
  statement: ¬b ↔ b = false
  proof: by grind

中文:
定理 bool_iff_false
  条件: {b : 布尔值}
  结论: ¬b ↔ b = false
  证明: by grind
-/
theorem bool_iff_false {b : Bool} : ¬b ↔ b = false := by grind

/--
theorem `bool_eq_false` / 定理 `bool_eq_false`

English:
theorem bool_eq_false
  given: {b : Bool}
  statement: ¬b -> b = false
  proof: bool_iff_false.1

中文:
定理 bool_eq_false
  条件: {b : 布尔值}
  结论: ¬b -> b = false
  证明: bool_iff_false.1

Depends on / 依赖: bool_iff_false
-/
theorem bool_eq_false {b : Bool} : ¬b -> b = false :=
  bool_iff_false.1

/--
theorem `decide_false_iff` / 定理 `decide_false_iff`

English:
theorem decide_false_iff
  given: (p : Prop) {_ : Decidable p}
  statement: decide p = false ↔ ¬p
  proof: bool_iff_false.symm.trans (not_congr (decide_iff _))

中文:
定理 decide_false_iff
  条件: (p : 命题) {_ : 可判定 p}
  结论: decide p = false ↔ ¬p
  证明: bool_iff_false.symm.trans (not_congr (decide_iff _))

Depends on / 依赖: bool_iff_false, bool_iff_false.symm.trans, decide_iff, not_congr
-/
theorem decide_false_iff (p : Prop) {_ : Decidable p} : decide p = false ↔ ¬p :=
  bool_iff_false.symm.trans (not_congr (decide_iff _))

/--
theorem `decide_false` / 定理 `decide_false`

English:
theorem decide_false
  given: {p : Prop} [Decidable p]
  statement: ¬p -> decide p = false
  proof: (decide_false_iff p).2

中文:
定理 decide_false
  条件: {p : 命题} [可判定 p]
  结论: ¬p -> decide p = false
  证明: (decide_false_iff p).2

Depends on / 依赖: decide_false_iff
-/
theorem decide_false {p : Prop} [Decidable p] : ¬p -> decide p = false :=
  (decide_false_iff p).2

/--
theorem `of_decide_false` / 定理 `of_decide_false`

English:
theorem of_decide_false
  given: {p : Prop} [Decidable p]
  statement: decide p = false -> ¬p
  proof: (decide_false_iff p).1

中文:
定理 of_decide_false
  条件: {p : 命题} [可判定 p]
  结论: decide p = false -> ¬p
  证明: (decide_false_iff p).1

Depends on / 依赖: decide_false_iff
-/
theorem of_decide_false {p : Prop} [Decidable p] : decide p = false -> ¬p :=
  (decide_false_iff p).1

/--
theorem `decide_congr` / 定理 `decide_congr`

English:
theorem decide_congr
  given: {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q)
  statement: decide p = decide q
  proof: decide_eq_decide.mpr h

中文:
定理 decide_congr
  条件: {p q : 命题} [可判定 p] [可判定 q] (h : p ↔ q)
  结论: decide p = decide q
  证明: decide_eq_decide.mpr h

Depends on / 依赖: decide_eq_decide, decide_eq_decide.mpr
-/
theorem decide_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h

/--
theorem `coe_xor_iff` / 定理 `coe_xor_iff`

English:
theorem coe_xor_iff
  given: (a b : Bool)
  statement: xor a b ↔ Xor (a = true) (b = true)
  proof: by grind

中文:
定理 coe_xor_iff
  条件: (a b : 布尔值)
  结论: xor a b ↔ Xor (a = true) (b = true)
  证明: by grind
-/
theorem coe_xor_iff (a b : Bool) : xor a b ↔ Xor (a = true) (b = true) := by grind

end

/--
theorem `dichotomy` / 定理 `dichotomy`

English:
theorem dichotomy
  given: (b : Bool)
  statement: b = false ∨ b = true
  proof: by grind

中文:
定理 dichotomy
  条件: (b : 布尔值)
  结论: b = false ∨ b = true
  证明: by grind
-/
theorem dichotomy (b : Bool) : b = false ∨ b = true := by grind

/--
theorem `not_ne_id` / 定理 `not_ne_id`

English:
theorem not_ne_id
  statement: not != id
  proof: fun h => false_ne_true congrFun h true

中文:
定理 not_ne_id
  结论: not != id
  证明: fun h => false_ne_true congrFun h true

Depends on / 依赖: false_ne_true
-/
theorem not_ne_id : not != id := fun h => false_ne_true congrFun h true

/--
theorem `or_inl` / 定理 `or_inl`

English:
theorem or_inl
  given: {a b : Bool} (H : a)
  statement: a || b
  proof: by simp [H]

中文:
定理 or_inl
  条件: {a b : 布尔值} (H : a)
  结论: a || b
  证明: by simp [H]
-/
theorem or_inl {a b : Bool} (H : a) : a || b := by simp [H]

/--
theorem `or_inr` / 定理 `or_inr`

English:
theorem or_inr
  given: {a b : Bool} (H : b)
  statement: a || b
  proof: by grind

中文:
定理 or_inr
  条件: {a b : 布尔值} (H : b)
  结论: a || b
  证明: by grind
-/
theorem or_inr {a b : Bool} (H : b) : a || b := by grind

/--
theorem `and_elim_left` / 定理 `and_elim_left`

English:
theorem and_elim_left
  statement: forall {a b : Bool}, a && b -> a
  proof: by decide

中文:
定理 and_elim_left
  结论: 对任意 {a b : 布尔值}, a && b -> a
  证明: by decide
-/
theorem and_elim_left : forall {a b : Bool}, a && b -> a := by decide

/--
theorem `and_intro` / 定理 `and_intro`

English:
theorem and_intro
  statement: forall {a b : Bool}, a -> b -> a && b
  proof: by decide

中文:
定理 and_intro
  结论: 对任意 {a b : 布尔值}, a -> b -> a && b
  证明: by decide
-/
theorem and_intro : forall {a b : Bool}, a -> b -> a && b := by decide

/--
theorem `and_elim_right` / 定理 `and_elim_right`

English:
theorem and_elim_right
  statement: forall {a b : Bool}, a && b -> b
  proof: by decide

中文:
定理 and_elim_right
  结论: 对任意 {a b : 布尔值}, a && b -> b
  证明: by decide
-/
theorem and_elim_right : forall {a b : Bool}, a && b -> b := by decide

/--
lemma `eq_not_iff` / 引理 `eq_not_iff`

English:
lemma eq_not_iff
  statement: forall {a b : Bool}, a = !b ↔ a != b
  proof: by decide

中文:
引理 eq_not_iff
  结论: 对任意 {a b : 布尔值}, a = !b ↔ a != b
  证明: by decide
-/
lemma eq_not_iff : forall {a b : Bool}, a = !b ↔ a != b := by decide

/--
lemma `not_eq_iff` / 引理 `not_eq_iff`

English:
lemma not_eq_iff
  statement: forall {a b : Bool}, (!a) = b ↔ a != b
  proof: by decide

中文:
引理 not_eq_iff
  结论: 对任意 {a b : 布尔值}, (!a) = b ↔ a != b
  证明: by decide
-/
lemma not_eq_iff : forall {a b : Bool}, (!a) = b ↔ a != b := by decide

/--
theorem `ne_not` / 定理 `ne_not`

English:
theorem ne_not
  given: {a b : Bool}
  statement: a != !b ↔ a = b
  proof: not_eq_not

中文:
定理 ne_not
  条件: {a b : 布尔值}
  结论: a != !b ↔ a = b
  证明: not_eq_not

Depends on / 依赖: not_eq_not
-/
theorem ne_not {a b : Bool} : a != !b ↔ a = b :=
  not_eq_not

/--
lemma `not_ne_self` / 引理 `not_ne_self`

English:
lemma not_ne_self
  statement: forall b : Bool, (!b) != b
  proof: by decide

中文:
引理 not_ne_self
  结论: 对任意 b : 布尔值, (!b) != b
  证明: by decide
-/
lemma not_ne_self : forall b : Bool, (!b) != b := by decide

/--
lemma `self_ne_not` / 引理 `self_ne_not`

English:
lemma self_ne_not
  statement: forall b : Bool, b != !b
  proof: by decide

中文:
引理 self_ne_not
  结论: 对任意 b : 布尔值, b != !b
  证明: by decide
-/
lemma self_ne_not : forall b : Bool, b != !b := by decide

/--
lemma `eq_or_eq_not` / 引理 `eq_or_eq_not`

English:
lemma eq_or_eq_not
  statement: forall a b, a = b ∨ a = !b
  proof: by decide

中文:
引理 eq_or_eq_not
  结论: 对任意 a b, a = b ∨ a = !b
  证明: by decide
-/
lemma eq_or_eq_not : forall a b, a = b ∨ a = !b := by decide

-- TODO naming issue: these two `not` are different.
/--
theorem `not_iff_not` / 定理 `not_iff_not`

English:
theorem not_iff_not
  statement: forall {b : Bool}, !b ↔ ¬b
  proof: by simp

中文:
定理 not_iff_not
  结论: 对任意 {b : 布尔值}, !b ↔ ¬b
  证明: by simp
-/
theorem not_iff_not : forall {b : Bool}, !b ↔ ¬b := by simp

/--
theorem `eq_true_of_not_eq_false'` / 定理 `eq_true_of_not_eq_false'`

English:
theorem eq_true_of_not_eq_false'
  given: {a : Bool}
  statement: (!a) = false -> a = true
  proof: by decide +revert

中文:
定理 eq_true_of_not_eq_false'
  条件: {a : 布尔值}
  结论: (!a) = false -> a = true
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem eq_true_of_not_eq_false' {a : Bool} : (!a) = false -> a = true := by decide +revert

/--
theorem `eq_false_of_not_eq_true'` / 定理 `eq_false_of_not_eq_true'`

English:
theorem eq_false_of_not_eq_true'
  given: {a : Bool}
  statement: (!a) = true -> a = false
  proof: by decide +revert

中文:
定理 eq_false_of_not_eq_true'
  条件: {a : 布尔值}
  结论: (!a) = true -> a = false
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem eq_false_of_not_eq_true' {a : Bool} : (!a) = true -> a = false := by decide +revert

/--
theorem `bne_eq_xor` / 定理 `bne_eq_xor`

English:
theorem bne_eq_xor
  statement: bne = xor
  proof: by constructor

中文:
定理 bne_eq_xor
  结论: bne = xor
  证明: by constructor
-/
theorem bne_eq_xor : bne = xor := by constructor

attribute [simp] xor_assoc

/--
theorem `xor_iff_ne` / 定理 `xor_iff_ne`

English:
theorem xor_iff_ne
  statement: forall {x y : Bool}, xor x y = true ↔ x != y
  proof: by decide

中文:
定理 xor_iff_ne
  结论: 对任意 {x y : 布尔值}, xor x y = true ↔ x != y
  证明: by decide
-/
theorem xor_iff_ne : forall {x y : Bool}, xor x y = true ↔ x != y := by decide


/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder Bool where
  body: by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := by decide
  max_def := by decide
  min_def := by decide

中文:
实例 linearOrder
  签名: : 线性序 布尔值 where
  定义体: by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := by decide
  max_def := by decide
  min_def := by decide

Depends on / 依赖: le_antisymm, le_total, le_trans, lt_iff_le_not_ge, max_def, min_def, toDecidableEq, toDecidableLE, toDecidableLT
-/
instance linearOrder : LinearOrder Bool where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := by decide
  max_def := by decide
  min_def := by decide

/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  statement: forall {x y : Bool}, x < y ↔ x = false ∧ y = true
  proof: by decide

@[simp]

中文:
定理 lt_iff
  结论: 对任意 {x y : 布尔值}, x < y ↔ x = false ∧ y = true
  证明: by decide

@[simp]
-/
theorem lt_iff : forall {x y : Bool}, x < y ↔ x = false ∧ y = true := by decide

@[simp]
/--
theorem `false_lt_true` / 定理 `false_lt_true`

English:
theorem false_lt_true
  statement: false < true
  proof: lt_iff.2 ⟨rfl, rfl⟩

中文:
定理 false_lt_true
  结论: false < true
  证明: lt_iff.2 ⟨rfl, rfl⟩

Depends on / 依赖: lt_iff
-/
theorem false_lt_true : false < true :=
  lt_iff.2 ⟨rfl, rfl⟩

/--
theorem `le_iff_imp` / 定理 `le_iff_imp`

English:
theorem le_iff_imp
  statement: forall {x y : Bool}, x <= y ↔ x -> y
  proof: by decide

中文:
定理 le_iff_imp
  结论: 对任意 {x y : 布尔值}, x <= y ↔ x -> y
  证明: by decide
-/
theorem le_iff_imp : forall {x y : Bool}, x <= y ↔ x -> y := by decide

/--
theorem `and_le_left` / 定理 `and_le_left`

English:
theorem and_le_left
  statement: forall x y : Bool, (x && y) <= x
  proof: by decide

中文:
定理 and_le_left
  结论: 对任意 x y : 布尔值, (x && y) <= x
  证明: by decide
-/
theorem and_le_left : forall x y : Bool, (x && y) <= x := by decide

/--
theorem `and_le_right` / 定理 `and_le_right`

English:
theorem and_le_right
  statement: forall x y : Bool, (x && y) <= y
  proof: by decide

中文:
定理 and_le_right
  结论: 对任意 x y : 布尔值, (x && y) <= y
  证明: by decide
-/
theorem and_le_right : forall x y : Bool, (x && y) <= y := by decide

/--
theorem `le_and` / 定理 `le_and`

English:
theorem le_and
  statement: forall {x y z : Bool}, x <= y -> x <= z -> x <= (y && z)
  proof: by decide

中文:
定理 le_and
  结论: 对任意 {x y z : 布尔值}, x <= y -> x <= z -> x <= (y && z)
  证明: by decide
-/
theorem le_and : forall {x y z : Bool}, x <= y -> x <= z -> x <= (y && z) := by decide

/--
theorem `left_le_or` / 定理 `left_le_or`

English:
theorem left_le_or
  statement: forall x y : Bool, x <= (x || y)
  proof: by decide

中文:
定理 left_le_or
  结论: 对任意 x y : 布尔值, x <= (x || y)
  证明: by decide
-/
theorem left_le_or : forall x y : Bool, x <= (x || y) := by decide

/--
theorem `right_le_or` / 定理 `right_le_or`

English:
theorem right_le_or
  statement: forall x y : Bool, y <= (x || y)
  proof: by decide

中文:
定理 right_le_or
  结论: 对任意 x y : 布尔值, y <= (x || y)
  证明: by decide
-/
theorem right_le_or : forall x y : Bool, y <= (x || y) := by decide

/--
theorem `or_le` / 定理 `or_le`

English:
theorem or_le
  statement: forall {x y z}, x <= z -> y <= z -> (x || y) <= z
  proof: by decide

中文:
定理 or_le
  结论: 对任意 {x y z}, x <= z -> y <= z -> (x || y) <= z
  证明: by decide
-/
theorem or_le : forall {x y z}, x <= z -> y <= z -> (x || y) <= z := by decide

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: (n : Nat)
  body: decide (n != 0)

@[simp, grind =]

中文:
定义 of自然数
  签名: (n : 自然数)
  定义体: decide (n != 0)

@[simp, grind =]
-/
def ofNat (n : Nat) : Bool :=
  decide (n != 0)

@[simp, grind =]
/--
theorem `ofNat_zero` / 定理 `ofNat_zero`

English:
theorem ofNat_zero
  statement: ofNat 0 = false
  proof: rfl

@[simp, grind =]

中文:
定理 of自然数_zero
  结论: of自然数 0 = false
  证明: rfl

@[simp, grind =]
-/
theorem ofNat_zero : ofNat 0 = false := rfl

@[simp, grind =]
/--
theorem `ofNat_add_one` / 定理 `ofNat_add_one`

English:
theorem ofNat_add_one
  given: {n : Nat}
  statement: ofNat (n + 1) = true
  proof: rfl

中文:
定理 of自然数_add_one
  条件: {n : 自然数}
  结论: of自然数 (n + 1) = true
  证明: rfl
-/
theorem ofNat_add_one {n : Nat} : ofNat (n + 1) = true := rfl

/--
lemma `toNat_beq_zero` / 引理 `toNat_beq_zero`

English:
lemma toNat_beq_zero
  given: (b : Bool)
  statement: (b.toNat == 0) = !b
  proof: by grind

中文:
引理 to自然数_beq_zero
  条件: (b : 布尔值)
  结论: (b.to自然数 == 0) = !b
  证明: by grind
-/
@[simp] lemma toNat_beq_zero (b : Bool) : (b.toNat == 0) = !b := by grind
/--
lemma `toNat_bne_zero` / 引理 `toNat_bne_zero`

English:
lemma toNat_bne_zero
  given: (b : Bool)
  statement: (b.toNat != 0) = b
  proof: by simp [bne]

中文:
引理 to自然数_bne_zero
  条件: (b : 布尔值)
  结论: (b.to自然数 != 0) = b
  证明: by simp [bne]
-/
@[simp] lemma toNat_bne_zero (b : Bool) : (b.toNat != 0) = b := by simp [bne]
/--
lemma `toNat_beq_one` / 引理 `toNat_beq_one`

English:
lemma toNat_beq_one
  given: (b : Bool)
  statement: (b.toNat == 1) = b
  proof: by cases b <;> rfl

中文:
引理 to自然数_beq_one
  条件: (b : 布尔值)
  结论: (b.to自然数 == 1) = b
  证明: by cases b <;> rfl
-/
@[simp] lemma toNat_beq_one (b : Bool) : (b.toNat == 1) = b := by cases b <;> rfl
/--
lemma `toNat_bne_one` / 引理 `toNat_bne_one`

English:
lemma toNat_bne_one
  given: (b : Bool)
  statement: (b.toNat != 1) = !b
  proof: by simp [bne]

中文:
引理 to自然数_bne_one
  条件: (b : 布尔值)
  结论: (b.to自然数 != 1) = !b
  证明: by simp [bne]
-/
@[simp] lemma toNat_bne_one (b : Bool) : (b.toNat != 1) = !b := by simp [bne]

/--
theorem `ofNat_le_ofNat` / 定理 `ofNat_le_ofNat`

English:
theorem ofNat_le_ofNat
  given: {n m : Nat} (h : n <= m)
  statement: ofNat n <= ofNat m
  proof: by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => grind [Bool.false_le]
  | isFalse hn => cases Nat.decEq m 0 with grind [Bool.le_true]

中文:
定理 of自然数_le_of自然数
  条件: {n m : 自然数} (h : n <= m)
  结论: of自然数 n <= of自然数 m
  证明: by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => grind [Bool.false_le]
  | isFalse hn => cases Nat.decEq m 0 with grind [Bool.le_true]

Depends on / 依赖: Bool.false_le, Bool.le_true, Nat.decEq, _root_, _root_.decide_not, decide_not, false_le, isFalse, isTrue, le_true, ne_eq
-/
theorem ofNat_le_ofNat {n m : Nat} (h : n <= m) : ofNat n <= ofNat m := by
  simp only [ofNat, ne_eq, _root_.decide_not]
  cases Nat.decEq n 0 with
  | isTrue hn => grind [Bool.false_le]
  | isFalse hn => cases Nat.decEq m 0 with grind [Bool.le_true]

/--
theorem `toNat_le_toNat` / 定理 `toNat_le_toNat`

English:
theorem toNat_le_toNat
  given: {b₀ b₁ : Bool} (h : b₀ <= b₁)
  statement: toNat b₀ <= toNat b₁
  proof: by
  cases b₀ <;> cases b₁ <;> simp_all +decide

中文:
定理 to自然数_le_to自然数
  条件: {b₀ b₁ : 布尔值} (h : b₀ <= b₁)
  结论: to自然数 b₀ <= to自然数 b₁
  证明: by
  cases b₀ <;> cases b₁ <;> simp_all +decide
-/
theorem toNat_le_toNat {b₀ b₁ : Bool} (h : b₀ <= b₁) : toNat b₀ <= toNat b₁ := by
  cases b₀ <;> cases b₁ <;> simp_all +decide

/--
theorem `ofNat_toNat` / 定理 `ofNat_toNat`

English:
theorem ofNat_toNat
  given: (b : Bool)
  statement: ofNat (toNat b) = b
  proof: by grind [cases Bool]

@[simp]

中文:
定理 of自然数_to自然数
  条件: (b : 布尔值)
  结论: of自然数 (to自然数 b) = b
  证明: by grind [cases Bool]

@[simp]
-/
theorem ofNat_toNat (b : Bool) : ofNat (toNat b) = b := by grind [cases Bool]

@[simp]
/--
theorem `injective_iff` / 定理 `injective_iff`

English:
theorem injective_iff
  given: {α : Sort*} {f : Bool -> α}
  statement: Function.Injective f ↔ f false != f true
  proof: ⟨fun Hinj Heq => false_ne_true (Hinj Heq), fun H x y => by grind [cases Bool]⟩

中文:
定理 injective_iff
  条件: {α : 类型层*} {f : 布尔值 -> α}
  结论: 函数.单射 f ↔ f false != f true
  证明: ⟨fun Hinj Heq => false_ne_true (Hinj Heq), fun H x y => by grind [cases Bool]⟩

Depends on / 依赖: false_ne_true
-/
theorem injective_iff {α : Sort*} {f : Bool -> α} : Function.Injective f ↔ f false != f true :=
  ⟨fun Hinj Heq => false_ne_true (Hinj Heq), fun H x y => by grind [cases Bool]⟩

/--
theorem `apply_apply_apply` / 定理 `apply_apply_apply`

English:
theorem apply_apply_apply
  given: (f : Bool -> Bool) (x : Bool)
  statement: f (f (f x)) = f x
  proof: by
  cases h₁ : f true <;> cases h₂ : f false <;> grind [cases Bool]

中文:
定理 apply_apply_apply
  条件: (f : 布尔值 -> 布尔值) (x : 布尔值)
  结论: f (f (f x)) = f x
  证明: by
  cases h₁ : f true <;> cases h₂ : f false <;> grind [cases Bool]
-/
theorem apply_apply_apply (f : Bool -> Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h₁ : f true <;> cases h₂ : f false <;> grind [cases Bool]

/--
Definition of `xor3` / `xor3` 的定义

English:
definition xor3
  signature: (x y c : Bool)
  body: xor (xor x y) c

中文:
定义 xor3
  签名: (x y c : 布尔值)
  定义体: xor (xor x y) c
-/
protected def xor3 (x y c : Bool) :=
  xor (xor x y) c

/--
Definition of `carry` / `carry` 的定义

English:
definition carry
  signature: (x y c : Bool)
  body: x && y || x && c || y && c

中文:
定义 carry
  签名: (x y c : 布尔值)
  定义体: x && y || x && c || y && c
-/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c

end Bool
