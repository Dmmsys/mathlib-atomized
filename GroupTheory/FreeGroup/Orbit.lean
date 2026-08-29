/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Krause
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
For any `w : α × Bool`, `FreeGroup.startsWith w` is the set of all elements of `FreeGroup α` that
start with `w`.

The main theorem `Orbit.duplicate` proves that applying `w⁻¹` to the orbit of `x` under the action
of `FreeGroup.startsWith w` yields the orbit of `x` under the action of `FreeGroup.startsWith v`
for every `v ≠ w⁻¹` (and the point `x`).
-/

@[expose] public section

variable {α X : Type*} [DecidableEq α]

namespace FreeGroup

/--
Definition of `startsWith` / `startsWith` 的定义

English:
definition startsWith
  signature: (w : α × Bool)
  body: {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

中文:
定义 startsWith
  签名: (w : α × 布尔值)
  定义体: {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

Depends on / 依赖: FreeGroup, FreeGroup.toWord, toWord
-/
def startsWith (w : α × Bool) := {g : FreeGroup α | (FreeGroup.toWord g)[0]? = some w}

/--
theorem `startsWith.ne_one` / 定理 `startsWith.ne_one`

English:
theorem startsWith.ne_one
  given: {w : α × Bool} (g : FreeGroup α) (h : g in FreeGroup.startsWith w)
  proof: fun h1 => by simp [h1, startsWith, FreeGroup.toWord_one] at h

@[simp]

中文:
定理 startsWith.ne_one
  条件: {w : α × 布尔值} (g : 自由群 α) (h : g in 自由群.startsWith w)
  证明: fun h1 => by simp [h1, startsWith, FreeGroup.toWord_one] at h

@[simp]

Depends on / 依赖: FreeGroup, FreeGroup.toWord_one, startsWith, toWord_one
-/
theorem startsWith.ne_one {w : α × Bool} (g : FreeGroup α) (h : g in FreeGroup.startsWith w) :
    g != 1 := fun h1 => by simp [h1, startsWith, FreeGroup.toWord_one] at h

@[simp]
/--
lemma `startsWith.disjoint_iff_ne` / 引理 `startsWith.disjoint_iff_ne`

English:
lemma startsWith.disjoint_iff_ne
  given: {w w' : α × Bool}
  proof: by
  simp_all only [ne_eq, startsWith, Set.disjoint_iff_inter_eq_empty, Set.ext_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, Option.some.injEq]
  exact Iff.intro (fun h => h (mk [w]) (by simp)) (by grind)

.Injective := fun a b h => by lemma startsWith.

中文:
引理 startsWith.disjoint_iff_ne
  条件: {w w' : α × 布尔值}
  证明: by
  simp_all only [ne_eq, startsWith, Set.disjoint_iff_inter_eq_empty, Set.ext_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, Option.some.injEq]
  exact Iff.intro (fun h => h (mk [w]) (by simp)) (by grind)

.Injective := fun a b h => by lemma startsWith.

Depends on / 依赖: Iff.intro, Option.some.injEq, Set.disjoint_iff_inter_eq_empty, Set.ext_iff, Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_ofPred_eq, disjoint_iff_inter_eq_empty, ext_iff, iff_false, mem_empty_iff_false, mem_inter_iff, mem_ofPred_eq, ne_eq, not_and, startsWith
-/
lemma startsWith.disjoint_iff_ne {w w' : α × Bool} :
    Disjoint (startsWith w) (startsWith w') ↔ w != w' := by
  simp_all only [ne_eq, startsWith, Set.disjoint_iff_inter_eq_empty, Set.ext_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, Option.some.injEq]
  exact Iff.intro (fun h => h (mk [w]) (by simp)) (by grind)

.Injective := fun a b h => by lemma startsWith.Injective : @startsWith α _
  simp only [startsWith, Set.ext_iff, Set.mem_ofPred_eq] at h
  simpa using h (mk [a])

/--
theorem `startsWith_mk_mul` / 定理 `startsWith_mk_mul`

English:
theorem startsWith_mk_mul
  statement: {w : α × Bool} (g : FreeGroup α)
  proof: by
  by_cases hC : 0 < g.toWord.length
  · simp only [startsWith, Set.mem_ofPred_eq, getElem?_pos, Option.some.injEq,
      Prod.eq_iff_fst_eq_snd_eq, not_and, Bool.not_eq_not, toWord_mul, toWord_mk, reduce.cons,
      reduce_nil, List.cons_append, List.nil_append, reduce_toWord, hC] at *
    rw [sh

中文:
定理 startsWith_mk_mul
  结论: {w : α × 布尔值} (g : 自由群 α)
  证明: by
  by_cases hC : 0 < g.toWord.length
  · simp only [startsWith, Set.mem_ofPred_eq, getElem?_pos, Option.some.injEq,
      Prod.eq_iff_fst_eq_snd_eq, not_and, Bool.not_eq_not, toWord_mul, toWord_mk, reduce.cons,
      reduce_nil, List.cons_append, List.nil_append, reduce_toWord, hC] at *
    rw [sh

Depends on / 依赖: Bool.not_eq_not, List.cons_append, List.nil_append, Option.some.injEq, Prod.eq_iff_fst_eq_snd_eq, Set.mem_ofPred_eq, _pos, cons_append, eq_iff_fst_eq_snd_eq, g.toWord, g.toWord.head, g.toWord.length, g.toWord.tail, getElem, length, mem_ofPred_eq, nil_append, not_and, not_eq_not, reduce.cons
-/
theorem startsWith_mk_mul {w : α × Bool} (g : FreeGroup α)
    (h : ¬ g in startsWith (w.1, !w.2)) : mk [w] * g in startsWith w := by
  by_cases hC : 0 < g.toWord.length
  · simp only [startsWith, Set.mem_ofPred_eq, getElem?_pos, Option.some.injEq,
      Prod.eq_iff_fst_eq_snd_eq, not_and, Bool.not_eq_not, toWord_mul, toWord_mk, reduce.cons,
      reduce_nil, List.cons_append, List.nil_append, reduce_toWord, hC] at *
    rw [show g.toWord = g.toWord.head (by grind) :: g.toWord.tail by grind]
    grind
  · simp_all [startsWith]

variable [MulAction (FreeGroup α) X]

instance {w : α × Bool} : SMul (startsWith w) X where
  smul g x := g.val • x

@[simp]
/--
lemma `startsWith.smul_def` / 引理 `startsWith.smul_def`

English:
lemma startsWith.smul_def
  given: {w : α × Bool} {g : startsWith w} {x : X}
  statement: g • x = g.val • x
  proof: by
  rfl

中文:
引理 startsWith.smul_def
  条件: {w : α × 布尔值} {g : startsWith w} {x : X}
  结论: g • x = g.val • x
  证明: by
  rfl
-/
lemma startsWith.smul_def {w : α × Bool} {g : startsWith w} {x : X} : g • x = g.val • x := by
  rfl

/--
theorem `Orbit.duplicate` / 定理 `Orbit.duplicate`

English:
theorem Orbit.duplicate
  given: (x : X) (w : α × Bool)
  proof: by
  ext i
  constructor
  · rintro ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    set l := g.toWord with hl
    have h : (⟨g, hg⟩ : startsWith w) = ⟨mk g.toWord, by simp [g.mk_toWord, hg]⟩ := by
      simp [g.mk_toWord]
    match l with
    | [] => simp [← hl, startsWith] at hg
    | [a] =>
      simp_rw [h, ← hl, s

中文:
定理 Orbit.duplicate
  条件: (x : X) (w : α × 布尔值)
  证明: by
  ext i
  constructor
  · rintro ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    set l := g.toWord with hl
    have h : (⟨g, hg⟩ : startsWith w) = ⟨mk g.toWord, by simp [g.mk_toWord, hg]⟩ := by
      simp [g.mk_toWord]
    match l with
    | [] => simp [← hl, startsWith] at hg
    | [a] =>
      simp_rw [h, ← hl, s

Depends on / 依赖: Or.inr, g.mk_toWord, g.toWord, inv_smul_smul, isReduced_cons_cons, isReduced_cons_cons.mp, isReduced_toWord, mk_toWord, simp_rw, smul_def, startsWith, startsWith.smul_def, toWord
-/
theorem Orbit.duplicate (x : X) (w : α × Bool) :
    {(mk [w])⁻¹ • y | y in MulAction.orbit (startsWith w) x} =
      (⋃ v in {z : α × Bool | z != (w.1, !w.2)}, MulAction.orbit (startsWith v) x) union {x} := by
  ext i
  constructor
  · rintro ⟨-, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    set l := g.toWord with hl
    have h : (⟨g, hg⟩ : startsWith w) = ⟨mk g.toWord, by simp [g.mk_toWord, hg]⟩ := by
      simp [g.mk_toWord]
    match l with
    | [] => simp [← hl, startsWith] at hg
    | [a] =>
      simp_rw [h, ← hl, show a = w by simpa [← hl, startsWith] using hg, startsWith.smul_def,
        inv_smul_smul]
      exact Or.inr rfl
    | a :: b :: l =>
      have ha : a = w := by simpa [← hl, startsWith] using hg
      have h1 := isReduced_cons_cons.mp (hl ▸ isReduced_toWord)
      refine Or.inl (Set.mem_biUnion (x := b) (by grind) ?_)
      simp_rw [h, ← hl, ha, ← List.singleton_append (l := b :: l), ← mul_mk, startsWith.smul_def,
        mul_smul, inv_smul_smul]
      exact ⟨⟨mk (b :: l), by simp [startsWith, h1.2.reduce_eq]⟩, rfl⟩
  · rintro (⟨-, ⟨w', rfl⟩, -, ⟨hw, rfl⟩, ⟨g, hg⟩, rfl⟩ | rfl)
    · exact ⟨mk [w] • g • x, ⟨⟨mk [w] * g, startsWith_mk_mul g
        ((startsWith.disjoint_iff_ne.mpr hw).notMem_of_mem_left hg)⟩,
        mul_smul (mk [w]) g x⟩, inv_smul_smul (mk [w]) (g • x)⟩
    · exact ⟨mk [w] • i, ⟨⟨mk [w], rfl⟩, rfl⟩, inv_smul_smul (mk [w]) i⟩

end FreeGroup
