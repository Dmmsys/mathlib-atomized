/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Units

/-!
# Associated elements in rings
-/

public section

assert_not_exists IsOrderedMonoid Multiset Field

namespace Associated
variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

/--
lemma `neg_left` / 引理 `neg_left`

English:
lemma neg_left
  given: (h : Associated a b)
  statement: Associated (-a) b
  proof: let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩

中文:
引理 neg_left
  条件: (h : Associated a b)
  结论: Associated (-a) b
  证明: let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩
-/
lemma neg_left (h : Associated a b) : Associated (-a) b := let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩
/--
lemma `neg_right` / 引理 `neg_right`

English:
lemma neg_right
  given: (h : Associated a b)
  statement: Associated a (-b)
  proof: h.symm.neg_left.symm

中文:
引理 neg_right
  条件: (h : Associated a b)
  结论: Associated a (-b)
  证明: h.symm.neg_left.symm

Depends on / 依赖: h.symm.neg_left.symm, neg_left
-/
lemma neg_right (h : Associated a b) : Associated a (-b) := h.symm.neg_left.symm
/--
lemma `neg_neg` / 引理 `neg_neg`

English:
lemma neg_neg
  given: (h : Associated a b)
  statement: Associated (-a) (-b)
  proof: h.neg_left.neg_right

@[simp]

中文:
引理 neg_neg
  条件: (h : Associated a b)
  结论: Associated (-a) (-b)
  证明: h.neg_left.neg_right

@[simp]

Depends on / 依赖: h.neg_left.neg_right, neg_left, neg_right
-/
lemma neg_neg (h : Associated a b) : Associated (-a) (-b) := h.neg_left.neg_right

@[simp]
/--
lemma `neg_left_iff` / 引理 `neg_left_iff`

English:
lemma neg_left_iff
  statement: Associated (-a) b ↔ Associated a b
  proof: ⟨fun h => _root_.neg_neg a ▸ h.neg_left, fun h => h.neg_left⟩

@[simp]

中文:
引理 neg_left_iff
  结论: Associated (-a) b ↔ Associated a b
  证明: ⟨fun h => _root_.neg_neg a ▸ h.neg_left, fun h => h.neg_left⟩

@[simp]

Depends on / 依赖: _root_, _root_.neg_neg, h.neg_left, neg_left, neg_neg
-/
lemma neg_left_iff : Associated (-a) b ↔ Associated a b :=
  ⟨fun h => _root_.neg_neg a ▸ h.neg_left, fun h => h.neg_left⟩

@[simp]
/--
lemma `neg_right_iff` / 引理 `neg_right_iff`

English:
lemma neg_right_iff
  statement: Associated a (-b) ↔ Associated a b
  proof: ⟨fun h => _root_.neg_neg b ▸ h.neg_right, fun h => h.neg_right⟩

中文:
引理 neg_right_iff
  结论: Associated a (-b) ↔ Associated a b
  证明: ⟨fun h => _root_.neg_neg b ▸ h.neg_right, fun h => h.neg_right⟩

Depends on / 依赖: _root_, _root_.neg_neg, h.neg_right, neg_neg, neg_right
-/
lemma neg_right_iff : Associated a (-b) ↔ Associated a b :=
  ⟨fun h => _root_.neg_neg b ▸ h.neg_right, fun h => h.neg_right⟩

end Associated
