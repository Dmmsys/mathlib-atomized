/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.Interval.Set.Defs

/-!
# Order properties on tuples
-/

@[expose] public section

assert_not_exists Monoid

open Function Set

namespace Fin
variable {m n : Nat} {α : Fin (n + 1) -> Type*} (x : α 0) (q : forall i, α i) (p : forall i : Fin n, α i.succ)
  (i : Fin n) (y : α i.succ) (z : α 0)

/--
lemma `pi_lex_lt_cons_cons` / 引理 `pi_lex_lt_cons_cons`

English:
lemma pi_lex_lt_cons_cons
  statement: {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ}
  proof: by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_iff_succ]
  simp [and_assoc, exists_and_left]

中文:
引理 pi_lex_lt_cons_cons
  结论: {x₀ y₀ : α 0} {x y : 对任意 i : 有限集 n, α i.succ}
  证明: by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_iff_succ]
  simp [and_assoc, exists_and_left]

Depends on / 依赖: Fin.cons_succ, Fin.cons_zero, Fin.exists_fin_succ, Fin.forall_iff_succ, Pi.Lex, and_assoc, cons_succ, cons_zero, exists_and_left, exists_fin_succ, forall_iff_succ, simp_rw
-/
lemma pi_lex_lt_cons_cons {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ}
    (s : forall {i : Fin n.succ}, α i -> α i -> Prop) :
    Pi.Lex (· < ·) (@s) (Fin.cons x₀ x) (Fin.cons y₀ y) ↔
      s x₀ y₀ ∨ x₀ = y₀ ∧ Pi.Lex (· < ·) (@fun i : Fin n => @s i.succ) x y := by
  simp_rw [Pi.Lex, Fin.exists_fin_succ, Fin.cons_succ, Fin.cons_zero, Fin.forall_iff_succ]
  simp [and_assoc, exists_and_left]

variable [forall i, Preorder (α i)]

/--
lemma `insertNth_mem_Icc` / 引理 `insertNth_mem_Icc`

English:
lemma insertNth_mem_Icc
  statement: {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)}
  proof: by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x <= q₂ i)]

中文:
引理 insertNth_mem_Icc
  结论: {i : 有限集 (n + 1)} {x : α i} {p : 对任意 j, α (i.succAbove j)}
  证明: by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x <= q₂ i)]

Depends on / 依赖: and_assoc, and_left_comm, insertNth_le_iff, le_insertNth_iff, mem_Icc
-/
lemma insertNth_mem_Icc {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)}
    {q₁ q₂ : forall j, α j} :
    i.insertNth x p in Icc q₁ q₂ ↔
      x in Icc (q₁ i) (q₂ i) ∧ p in Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) := by
  simp only [mem_Icc, insertNth_le_iff, le_insertNth_iff, and_assoc, @and_left_comm (x <= q₂ i)]

/--
lemma `preimage_insertNth_Icc_of_mem` / 引理 `preimage_insertNth_Icc_of_mem`

English:
lemma preimage_insertNth_Icc_of_mem
  statement: {i : Fin (n + 1)} {x : α i} {q₁ q₂ : forall j, α j}
  proof: Set.ext fun p => by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and]

中文:
引理 preimage_insertNth_Icc_of_mem
  结论: {i : 有限集 (n + 1)} {x : α i} {q₁ q₂ : 对任意 j, α j}
  证明: Set.ext fun p => by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and]

Depends on / 依赖: Set.ext, insertNth_mem_Icc, mem_preimage, true_and
-/
lemma preimage_insertNth_Icc_of_mem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : forall j, α j}
    (hx : x in Icc (q₁ i) (q₂ i)) :
    i.insertNth x ⁻¹' Icc q₁ q₂ = Icc (fun j => q₁ (i.succAbove j)) fun j => q₂ (i.succAbove j) :=
  Set.ext fun p => by simp only [mem_preimage, insertNth_mem_Icc, hx, true_and]

/--
lemma `preimage_insertNth_Icc_of_notMem` / 引理 `preimage_insertNth_Icc_of_notMem`

English:
lemma preimage_insertNth_Icc_of_notMem
  statement: {i : Fin (n + 1)} {x : α i} {q₁ q₂ : forall j, α j}
  proof: Set.ext fun p => by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and, mem_empty_iff_false]

中文:
引理 preimage_insertNth_Icc_of_notMem
  结论: {i : 有限集 (n + 1)} {x : α i} {q₁ q₂ : 对任意 j, α j}
  证明: Set.ext fun p => by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and, mem_empty_iff_false]

Depends on / 依赖: Set.ext, false_and, insertNth_mem_Icc, mem_empty_iff_false, mem_preimage
-/
lemma preimage_insertNth_Icc_of_notMem {i : Fin (n + 1)} {x : α i} {q₁ q₂ : forall j, α j}
    (hx : x ∉ Icc (q₁ i) (q₂ i)) : i.insertNth x ⁻¹' Icc q₁ q₂ = ∅ :=
  Set.ext fun p => by
    simp only [mem_preimage, insertNth_mem_Icc, hx, false_and, mem_empty_iff_false]

end Fin

open Fin Matrix

variable {α : Type*}

open scoped Relator in
/--
lemma `liftFun_vecCons` / 引理 `liftFun_vecCons`

English:
lemma liftFun_vecCons
  given: {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (n + 1) -> α} {a : α}
  proof: by
  simp only [liftFun_iff_succ r, forall_iff_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]

中文:
引理 liftFun_vecCons
  条件: {n : 自然数} (r : α -> α -> 命题) [是Trans α r] {f : 有限集 (n + 1) -> α} {a : α}
  证明: by
  simp only [liftFun_iff_succ r, forall_iff_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]

Depends on / 依赖: castSucc_zero, cons_val_succ, cons_val_zero, forall_iff_succ, liftFun_iff_succ, succ_castSucc
-/
lemma liftFun_vecCons {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin (n + 1) -> α} {a : α} :
    ((· < ·) ⇒ r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·) ⇒ r) f f := by
  simp only [liftFun_iff_succ r, forall_iff_succ, cons_val_succ, cons_val_zero, ← succ_castSucc,
    castSucc_zero]

open scoped Relator in
/--
lemma `Fin.liftFun_cons` / 引理 `Fin.liftFun_cons`

English:
lemma Fin.liftFun_cons
  given: {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin n -> α} {a : α}
  proof: by
  match n with
  | 0 => simp [Relator.LiftFun]
  | n + 1 =>
    apply (liftFun_vecCons r).trans
    simp only [forall_iff_succ, and_congr_left_iff, iff_self_and]
    intro h r0 i
    exact _root_.trans r0 (h (by grind))

中文:
引理 有限集.liftFun_cons
  条件: {n : 自然数} (r : α -> α -> 命题) [是Trans α r] {f : 有限集 n -> α} {a : α}
  证明: by
  match n with
  | 0 => simp [Relator.LiftFun]
  | n + 1 =>
    apply (liftFun_vecCons r).trans
    simp only [forall_iff_succ, and_congr_left_iff, iff_self_and]
    intro h r0 i
    exact _root_.trans r0 (h (by grind))

Depends on / 依赖: LiftFun, Relator, Relator.LiftFun, _root_, _root_.trans, and_congr_left_iff, forall_iff_succ, iff_self_and, liftFun_vecCons
-/
lemma Fin.liftFun_cons {n : Nat} (r : α -> α -> Prop) [IsTrans α r] {f : Fin n -> α} {a : α} :
    ((· < ·) ⇒ r) (cons a f) (cons a f) ↔ (forall i, r a (f i)) ∧ ((· < ·) ⇒ r) f f := by
  match n with
  | 0 => simp [Relator.LiftFun]
  | n + 1 =>
    apply (liftFun_vecCons r).trans
    simp only [forall_iff_succ, and_congr_left_iff, iff_self_and]
    intro h r0 i
    exact _root_.trans r0 (h (by grind))

variable [Preorder α] {n : Nat}

/--
lemma `Fin.strictMono_insertNth_iff` / 引理 `Fin.strictMono_insertNth_iff`

English:
lemma Fin.strictMono_insertNth_iff
  given: (q : Fin (n + 1)) (x : α) (f : Fin n -> α)
  proof: by
  refine ⟨fun h => ⟨fun a b hab => ?_, ⟨fun i hlt => ?_, fun i hlt => ?_⟩⟩, ?_⟩
  · simpa [hab] using h (a := q.succAbove a) (b := q.succAbove b)
  · have : q.succAbove i < q := by simp [succAbove_of_castSucc_lt, hlt]
    simpa using h this
  · have : q < q.succAbove i := by simp [succAbove_of_le

中文:
引理 有限集.strictMono_insertNth_iff
  条件: (q : 有限集 (n + 1)) (x : α) (f : 有限集 n -> α)
  证明: by
  refine ⟨fun h => ⟨fun a b hab => ?_, ⟨fun i hlt => ?_, fun i hlt => ?_⟩⟩, ?_⟩
  · simpa [hab] using h (a := q.succAbove a) (b := q.succAbove b)
  · have : q.succAbove i < q := by simp [succAbove_of_castSucc_lt, hlt]
    simpa using h this
  · have : q < q.succAbove i := by simp [succAbove_of_le

Depends on / 依赖: castSucc, j.castSucc, le_castSucc_iff, q.succAbove, rename_i, succAbove, succAboveCases, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
lemma Fin.strictMono_insertNth_iff (q : Fin (n + 1)) (x : α) (f : Fin n -> α) :
    StrictMono (q.insertNth x f) ↔
      StrictMono f ∧ (forall i, i.castSucc < q -> f i < x) ∧ (forall i, q <= i.castSucc -> x < f i) := by
  refine ⟨fun h => ⟨fun a b hab => ?_, ⟨fun i hlt => ?_, fun i hlt => ?_⟩⟩, ?_⟩
  · simpa [hab] using h (a := q.succAbove a) (b := q.succAbove b)
  · have : q.succAbove i < q := by simp [succAbove_of_castSucc_lt, hlt]
    simpa using h this
  · have : q < q.succAbove i := by simp [succAbove_of_le_castSucc, hlt, ← le_castSucc_iff]
    simpa using h this
  · rintro ⟨h, hlt, hgt⟩ a b hab
    cases a using succAboveCases q <;> cases b using succAboveCases q
    · simp at hab
    · rename_i j
      have : q <= j.castSucc := by simpa [lt_succAbove_iff_le_castSucc] using hab
      simpa using hgt _ this
    · rename_i j
      have : j.castSucc < q := by simpa [succAbove_lt_iff_castSucc_lt] using hab
      simpa using hlt _ this
· simpa using h (strictMono_succAbove _).lt_iff_lt.mp hab

/--
lemma `Fin.strictMono_cons` / 引理 `Fin.strictMono_cons`

English:
lemma Fin.strictMono_cons
  given: {f : Fin n -> α} {a : α}
  proof: liftFun_cons (· < ·)

中文:
引理 有限集.strictMono_cons
  条件: {f : 有限集 n -> α} {a : α}
  证明: liftFun_cons (· < ·)

Depends on / 依赖: liftFun_cons
-/
lemma Fin.strictMono_cons {f : Fin n -> α} {a : α} :
    StrictMono (Fin.cons a f) ↔ (forall j, a < f j) ∧ StrictMono f :=
  liftFun_cons (· < ·)

/--
lemma `Fin.strictMono_cons_zero_succ` / 引理 `Fin.strictMono_cons_zero_succ`

English:
lemma Fin.strictMono_cons_zero_succ
  given: {f : Fin n -> Fin (n + 1)}
  proof: by
  refine ⟨fun h => funext fun i => ?_, fun h => by simp [h, strictMono_id]⟩
  have key (g : Fin (n + 1) -> Fin (n + 1)) (hg : StrictMono g) : g = id := by
    -- Import restrictions prevent us using `StrictMono.eq_id`: hence this manual proof.
    refine funext fun x => le_antisymm ?_ (hg.id_le x

中文:
引理 有限集.strictMono_cons_zero_succ
  条件: {f : 有限集 n -> 有限集 (n + 1)}
  证明: by
  refine ⟨fun h => funext fun i => ?_, fun h => by simp [h, strictMono_id]⟩
  have key (g : Fin (n + 1) -> Fin (n + 1)) (hg : StrictMono g) : g = id := by
    -- Import restrictions prevent us using `StrictMono.eq_id`: hence this manual proof.
    refine funext fun x => le_antisymm ?_ (hg.id_le x
-/
@[simp] lemma Fin.strictMono_cons_zero_succ {f : Fin n -> Fin (n + 1)} :
    StrictMono (Fin.cons 0 f) ↔ f = Fin.succ := by
  refine ⟨fun h => funext fun i => ?_, fun h => by simp [h, strictMono_id]⟩
  have key (g : Fin (n + 1) -> Fin (n + 1)) (hg : StrictMono g) : g = id := by
    -- Import restrictions prevent us using `StrictMono.eq_id`: hence this manual proof.
    refine funext fun x => le_antisymm ?_ (hg.id_le x)
    simpa using ((Fin.rev_strictAnti.comp_strictMono hg).comp Fin.rev_strictAnti).id_le (Fin.rev x)
  simpa using congrFun (key _ h) i.succ

variable {f : Fin (n + 1) -> α} {a : α}

/--
lemma `strictMono_vecCons` / 引理 `strictMono_vecCons`

English:
lemma strictMono_vecCons
  statement: StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f
  proof: liftFun_vecCons (· < ·)

@[simp]

中文:
引理 strictMono_vecCons
  结论: 严格递增 (vecCons a f) ↔ a < f 0 ∧ 严格递增 f
  证明: liftFun_vecCons (· < ·)

@[simp]
-/
@[simp] lemma strictMono_vecCons : StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f :=
  liftFun_vecCons (· < ·)

@[simp]
/--
lemma `monotone_vecCons` / 引理 `monotone_vecCons`

English:
lemma monotone_vecCons
  statement: Monotone (vecCons a f) ↔ a <= f 0 ∧ Monotone f
  proof: by
  simpa only [monotone_iff_forall_lt] using! @liftFun_vecCons α n (· <= ·) _ f a

中文:
引理 monotone_vecCons
  结论: 递增 (vecCons a f) ↔ a <= f 0 ∧ 递增 f
  证明: by
  simpa only [monotone_iff_forall_lt] using! @liftFun_vecCons α n (· <= ·) _ f a

Depends on / 依赖: liftFun_vecCons, monotone_iff_forall_lt
-/
lemma monotone_vecCons : Monotone (vecCons a f) ↔ a <= f 0 ∧ Monotone f := by
  simpa only [monotone_iff_forall_lt] using! @liftFun_vecCons α n (· <= ·) _ f a

/--
lemma `monotone_vecEmpty` / 引理 `monotone_vecEmpty`

English:
lemma monotone_vecEmpty
  statement: Monotone ![a]

中文:
引理 monotone_vecEmpty
  结论: 递增 ![a]
-/
@[simp] lemma monotone_vecEmpty : Monotone ![a]
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_refl _

/--
lemma `strictMono_vecEmpty` / 引理 `strictMono_vecEmpty`

English:
lemma strictMono_vecEmpty
  statement: StrictMono ![a]

中文:
引理 strictMono_vecEmpty
  结论: 严格递增 ![a]
-/
@[simp] lemma strictMono_vecEmpty : StrictMono ![a]
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

/--
lemma `strictAnti_vecCons` / 引理 `strictAnti_vecCons`

English:
lemma strictAnti_vecCons
  statement: StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f
  proof: liftFun_vecCons (· > ·)

中文:
引理 strictAnti_vecCons
  结论: 严格递减 (vecCons a f) ↔ f 0 < a ∧ 严格递减 f
  证明: liftFun_vecCons (· > ·)
-/
@[simp] lemma strictAnti_vecCons : StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f :=
  liftFun_vecCons (· > ·)

/--
lemma `antitone_vecCons` / 引理 `antitone_vecCons`

English:
lemma antitone_vecCons
  statement: Antitone (vecCons a f) ↔ f 0 <= a ∧ Antitone f
  proof: monotone_vecCons (α := αᵒᵈ)

中文:
引理 antitone_vecCons
  结论: 递减 (vecCons a f) ↔ f 0 <= a ∧ 递减 f
  证明: monotone_vecCons (α := αᵒᵈ)
-/
@[simp] lemma antitone_vecCons : Antitone (vecCons a f) ↔ f 0 <= a ∧ Antitone f :=
  monotone_vecCons (α := αᵒᵈ)

/--
lemma `antitone_vecEmpty` / 引理 `antitone_vecEmpty`

English:
lemma antitone_vecEmpty
  statement: Antitone (vecCons a vecEmpty)

中文:
引理 antitone_vecEmpty
  结论: 递减 (vecCons a vecEmpty)
-/
@[simp] lemma antitone_vecEmpty : Antitone (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, _ => le_rfl

/--
lemma `strictAnti_vecEmpty` / 引理 `strictAnti_vecEmpty`

English:
lemma strictAnti_vecEmpty
  statement: StrictAnti (vecCons a vecEmpty)

中文:
引理 strictAnti_vecEmpty
  结论: 严格递减 (vecCons a vecEmpty)
-/
@[simp] lemma strictAnti_vecEmpty : StrictAnti (vecCons a vecEmpty)
  | ⟨0, _⟩, ⟨0, _⟩, h => (irrefl _ h).elim

/--
lemma `StrictMono.vecCons` / 引理 `StrictMono.vecCons`

English:
lemma StrictMono.vecCons
  given: (hf : StrictMono f) (ha : a < f 0)
  statement: StrictMono (vecCons a f)
  proof: strictMono_vecCons.2 ⟨ha, hf⟩

中文:
引理 严格递增.vecCons
  条件: (hf : 严格递增 f) (ha : a < f 0)
  结论: 严格递增 (vecCons a f)
  证明: strictMono_vecCons.2 ⟨ha, hf⟩

Depends on / 依赖: strictMono_vecCons
-/
lemma StrictMono.vecCons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCons a f) :=
  strictMono_vecCons.2 ⟨ha, hf⟩

/--
lemma `StrictMono.removeNth` / 引理 `StrictMono.removeNth`

English:
lemma StrictMono.removeNth
  given: (hf : StrictMono f) (i : Fin (n + 1))
  statement: StrictMono (i.removeNth f)
  proof: hf.comp (Fin.strictMono_succAbove i)

中文:
引理 严格递增.removeNth
  条件: (hf : 严格递增 f) (i : 有限集 (n + 1))
  结论: 严格递增 (i.removeNth f)
  证明: hf.comp (Fin.strictMono_succAbove i)

Depends on / 依赖: Fin.strictMono_succAbove, hf.comp, strictMono_succAbove
-/
lemma StrictMono.removeNth (hf : StrictMono f) (i : Fin (n + 1)) : StrictMono (i.removeNth f) :=
  hf.comp (Fin.strictMono_succAbove i)

/--
lemma `StrictAnti.vecCons` / 引理 `StrictAnti.vecCons`

English:
lemma StrictAnti.vecCons
  given: (hf : StrictAnti f) (ha : f 0 < a)
  statement: StrictAnti (vecCons a f)
  proof: strictAnti_vecCons.2 ⟨ha, hf⟩

中文:
引理 严格递减.vecCons
  条件: (hf : 严格递减 f) (ha : f 0 < a)
  结论: 严格递减 (vecCons a f)
  证明: strictAnti_vecCons.2 ⟨ha, hf⟩

Depends on / 依赖: strictAnti_vecCons
-/
lemma StrictAnti.vecCons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCons a f) :=
  strictAnti_vecCons.2 ⟨ha, hf⟩

/--
lemma `Monotone.vecCons` / 引理 `Monotone.vecCons`

English:
lemma Monotone.vecCons
  given: (hf : Monotone f) (ha : a <= f 0)
  statement: Monotone (vecCons a f)
  proof: monotone_vecCons.2 ⟨ha, hf⟩

中文:
引理 递增.vecCons
  条件: (hf : 递增 f) (ha : a <= f 0)
  结论: 递增 (vecCons a f)
  证明: monotone_vecCons.2 ⟨ha, hf⟩

Depends on / 依赖: monotone_vecCons
-/
lemma Monotone.vecCons (hf : Monotone f) (ha : a <= f 0) : Monotone (vecCons a f) :=
  monotone_vecCons.2 ⟨ha, hf⟩

/--
lemma `Antitone.vecCons` / 引理 `Antitone.vecCons`

English:
lemma Antitone.vecCons
  given: (hf : Antitone f) (ha : f 0 <= a)
  statement: Antitone (vecCons a f)
  proof: antitone_vecCons.2 ⟨ha, hf⟩

example : Monotone ![1, 2, 2, 3] := by decide

中文:
引理 递减.vecCons
  条件: (hf : 递减 f) (ha : f 0 <= a)
  结论: 递减 (vecCons a f)
  证明: antitone_vecCons.2 ⟨ha, hf⟩

example : Monotone ![1, 2, 2, 3] := by decide

Depends on / 依赖: antitone_vecCons
-/
lemma Antitone.vecCons (hf : Antitone f) (ha : f 0 <= a) : Antitone (vecCons a f) :=
  antitone_vecCons.2 ⟨ha, hf⟩

example : Monotone ![1, 2, 2, 3] := by decide


variable {n : Nat}

/--
Definition of `OrderIso.piFinTwoIso` / `OrderIso.piFinTwoIso` 的定义

English:
definition OrderIso.piFinTwoIso
  signature: (α : Fin 2 -> Type*) [forall i, Preorder (α i)]
  body: piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

中文:
定义 OrderIso.piFinTwoIso
  签名: (α : 有限集 2 -> 类型) [对任意 i, 预序 (α i)]
  定义体: piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

Depends on / 依赖: piFinTwoEquiv
-/
def OrderIso.piFinTwoIso (α : Fin 2 -> Type*) [forall i, Preorder (α i)] : (forall i, α i) ≃o α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  map_rel_iff' := Iff.symm Fin.forall_fin_two

/--
Definition of `OrderIso.finTwoArrowIso` / `OrderIso.finTwoArrowIso` 的定义

English:
definition OrderIso.finTwoArrowIso
  signature: (α : Type*) [Preorder α]
  body: { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

中文:
定义 OrderIso.finTwoArrowIso
  签名: (α : 类型) [预序 α]
  定义体: { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

Depends on / 依赖: OrderIso, OrderIso.piFinTwoIso, finTwoArrowEquiv, piFinTwoIso, toEquiv
-/
def OrderIso.finTwoArrowIso (α : Type*) [Preorder α] : (Fin 2 -> α) ≃o α × α :=
  { OrderIso.piFinTwoIso fun _ => α with toEquiv := finTwoArrowEquiv α }

namespace Fin

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the first element of the tuple.

This is `Fin.cons` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/--
Definition of `consOrderIso` / `consOrderIso` 的定义

English:
definition consOrderIso
  signature: (α : Fin (n + 1) -> Type*) [forall i, LE (α i)]
  body: consEquiv α
  map_rel_iff' := forall_iff_succ

中文:
定义 consOrderIso
  签名: (α : 有限集 (n + 1) -> 类型) [对任意 i, LE (α i)]
  定义体: consEquiv α
  map_rel_iff' := forall_iff_succ

Depends on / 依赖: consEquiv
-/
def consOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] :
    α 0 × (forall i, α (succ i)) ≃o forall i, α i where
  toEquiv := consEquiv α
  map_rel_iff' := forall_iff_succ

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the last element of the tuple.

This is `Fin.snoc` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/--
Definition of `snocOrderIso` / `snocOrderIso` 的定义

English:
definition snocOrderIso
  signature: (α : Fin (n + 1) -> Type*) [forall i, LE (α i)]
  body: snocEquiv α
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, forall_iff_castSucc]

中文:
定义 snocOrderIso
  签名: (α : 有限集 (n + 1) -> 类型) [对任意 i, LE (α i)]
  定义体: snocEquiv α
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, forall_iff_castSucc]

Depends on / 依赖: snocEquiv
-/
def snocOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] :
    α (last n) × (forall i, α (castSucc i)) ≃o forall i, α i where
  toEquiv := snocEquiv α
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, forall_iff_castSucc]

/-- Order isomorphism between tuples of length `n + 1` and pairs of an element and a tuple of length
`n` given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `OrderIso`. -/
@[simps!, simps toEquiv]
/--
Definition of `insertNthOrderIso` / `insertNthOrderIso` 的定义

English:
definition insertNthOrderIso
  signature: (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] (p : Fin (n + 1))
  body: insertNthEquiv α p
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, p.forall_iff_succAbove]

中文:
定义 insertNthOrderIso
  签名: (α : 有限集 (n + 1) -> 类型) [对任意 i, LE (α i)] (p : 有限集 (n + 1))
  定义体: insertNthEquiv α p
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, p.forall_iff_succAbove]

Depends on / 依赖: insertNthEquiv
-/
def insertNthOrderIso (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] (p : Fin (n + 1)) :
    α p × (forall i, α (p.succAbove i)) ≃o forall i, α i where
  toEquiv := insertNthEquiv α p
  map_rel_iff' := by simp [Pi.le_def, Prod.le_def, p.forall_iff_succAbove]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `insertNthOrderIso_zero` / 引理 `insertNthOrderIso_zero`

English:
lemma insertNthOrderIso_zero
  given: (α : Fin (n + 1) -> Type*) [forall i, LE (α i)]
  proof: by ext; simp [insertNthOrderIso]

中文:
引理 insertNthOrderIso_zero
  条件: (α : 有限集 (n + 1) -> 类型) [对任意 i, LE (α i)]
  证明: by ext; simp [insertNthOrderIso]
-/
@[simp] lemma insertNthOrderIso_zero (α : Fin (n + 1) -> Type*) [forall i, LE (α i)] :
    insertNthOrderIso α 0 = consOrderIso α := by ext; simp [insertNthOrderIso]

/--
lemma `insertNthOrderIso_last` / 引理 `insertNthOrderIso_last`

English:
lemma insertNthOrderIso_last
  given: (n : Nat) (α : Type*) [LE α]
  proof: by ext; simp

中文:
引理 insertNthOrderIso_last
  条件: (n : 自然数) (α : 类型) [LE α]
  证明: by ext; simp
-/
@[simp] lemma insertNthOrderIso_last (n : Nat) (α : Type*) [LE α] :
    insertNthOrderIso (fun _ => α) (last n) = snocOrderIso (fun _ => α) := by ext; simp

end Fin

/--
Definition of `finSuccAboveOrderIso` / `finSuccAboveOrderIso` 的定义

English:
definition finSuccAboveOrderIso
  signature: (p : Fin (n + 1))
  body: finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'

中文:
定义 finSuccAboveOrderIso
  签名: (p : 有限集 (n + 1))
  定义体: finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'

Depends on / 依赖: finSuccAboveEquiv
-/
def finSuccAboveOrderIso (p : Fin (n + 1)) : Fin n ≃o { x : Fin (n + 1) // x != p } where
  __ := finSuccAboveEquiv p
  map_rel_iff' := p.succAboveOrderEmb.map_rel_iff'

/--
lemma `finSuccAboveOrderIso_apply` / 引理 `finSuccAboveOrderIso_apply`

English:
lemma finSuccAboveOrderIso_apply
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: rfl

中文:
引理 finSuccAboveOrderIso_apply
  条件: (p : 有限集 (n + 1)) (i : 有限集 n)
  证明: rfl
-/
lemma finSuccAboveOrderIso_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveOrderIso p i = ⟨p.succAbove i, p.succAbove_ne i⟩ := rfl

/--
lemma `finSuccAboveOrderIso_symm_apply_last` / 引理 `finSuccAboveOrderIso_symm_apply_last`

English:
lemma finSuccAboveOrderIso_symm_apply_last
  given: (x : { x : Fin (n + 1) // x != Fin.last n })
  proof: by
  rw [← Option.some_inj]
  simp [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]

中文:
引理 finSuccAboveOrderIso_symm_apply_last
  条件: (x : { x : 有限集 (n + 1) // x != 有限集.last n })
  证明: by
  rw [← Option.some_inj]
  simp [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]

Depends on / 依赖: Option.some_inj, OrderIso, OrderIso.symm, finSuccAboveEquiv, finSuccAboveOrderIso, some_inj
-/
lemma finSuccAboveOrderIso_symm_apply_last (x : { x : Fin (n + 1) // x != Fin.last n }) :
    (finSuccAboveOrderIso (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveOrderIso, finSuccAboveEquiv, OrderIso.symm]

/--
lemma `finSuccAboveOrderIso_symm_apply_ne_last` / 引理 `finSuccAboveOrderIso_symm_apply_ne_last`

English:
lemma finSuccAboveOrderIso_symm_apply_ne_last
  statement: {p : Fin (n + 1)} (h : p != Fin.last n)
  proof: by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property

中文:
引理 finSuccAboveOrderIso_symm_apply_ne_last
  结论: {p : 有限集 (n + 1)} (h : p != 有限集.last n)
  证明: by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property

Depends on / 依赖: Option.some_inj, OrderIso, OrderIso.symm, _ne_last_apply, finSuccAboveEquiv, finSuccEquiv, property, some_inj, x.property
-/
lemma finSuccAboveOrderIso_symm_apply_ne_last {p : Fin (n + 1)} (h : p != Fin.last n)
    (x : { x : Fin (n + 1) // x != p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv, OrderIso.symm] using finSuccEquiv'_ne_last_apply h x.property

set_option backward.isDefEq.respectTransparency false in
/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained. This is the `OrderIso` version of `Fin.castLE`. -/
@[simps apply symm_apply]
/--
Definition of `Fin.castLEOrderIso` / `Fin.castLEOrderIso` 的定义

English:
definition Fin.castLEOrderIso
  signature: {n m : Nat} (h : n <= m)
  body: ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]

中文:
定义 有限集.castLEOrderIso
  签名: {n m : 自然数} (h : n <= m)
  定义体: ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]

Depends on / 依赖: Fin.castLE, castLE
-/
def Fin.castLEOrderIso {n m : Nat} (h : n <= m) : Fin n ≃o { i : Fin m // (i : Nat) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_rel_iff' := by simp [(strictMono_castLE h).le_iff_le]
