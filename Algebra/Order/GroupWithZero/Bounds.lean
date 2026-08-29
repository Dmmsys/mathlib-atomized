/-
Copyright (c) 2025 María Inés de Frutos-Fernández . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Bounds.Image

/-!
# Lemmas about `BddAbove`
-/

public section

open Set

/--
lemma `BddAbove.range_comp_of_nonneg` / 引理 `BddAbove.range_comp_of_nonneg`

English:
lemma BddAbove.range_comp_of_nonneg
  statement: {α β γ : Type*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ]
  proof: by
  suffices hg' : BddAbove (g '' range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

中文:
引理 BddAbove.range_comp_of_nonneg
  结论: {α β γ : 类型} [非空 α] [预序 β] [零 β] [预序 γ]
  证明: by
  suffices hg' : BddAbove (g '' range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

Depends on / 依赖: BddAbove, Classical, Classical.ofNonempty, Function, Function.comp_def, Set.range_comp, comp_def, forall_apply_eq_imp_iff, forall_exists_index, hg.map_bddAbove, le_trans, map_bddAbove, mem_range, mem_upperBounds, ofNonempty, range_comp
-/
lemma BddAbove.range_comp_of_nonneg {α β γ : Type*} [Nonempty α] [Preorder β] [Zero β] [Preorder γ]
    {f : α -> β} {g : β -> γ} (hf : BddAbove (range f)) (hf0 : 0 <= f)
    (hg : MonotoneOn g {x : β | 0 <= x}) : BddAbove (range (fun x => g (f x))) := by
  suffices hg' : BddAbove (g '' range f) by
    rwa [← Function.comp_def, Set.range_comp]
  apply hg.map_bddAbove (by rintro x ⟨a, rfl⟩; exact hf0 a)
  obtain ⟨b, hb⟩ := hf
  use b, hb
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
  exact le_trans (hf0 Classical.ofNonempty) (hb Classical.ofNonempty)

/--
theorem `bddAbove_range_mul` / 定理 `bddAbove_range_mul`

English:
theorem bddAbove_range_mul
  statement: {α β : Type*} [Nonempty α] {u v : α -> β} [Preorder β] [Zero β] [Mul β]
  proof: letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i => (u i, v i)) (g := fun x => x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x => ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx => hx.1) (fun _ hx => hx.2))

中文:
定理 bddAbove_range_mul
  结论: {α β : 类型} [非空 α] {u v : α -> β} [预序 β] [零 β] [乘法 β]
  证明: letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i => (u i, v i)) (g := fun x => x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x => ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx => hx.1) (fun _ hx => hx.2))

Depends on / 依赖: BddAbove, BddAbove.range_comp_of_nonneg, bddAbove_range_prod, bddAbove_range_prod.mpr, monotoneOn, monotone_fst, monotone_fst.monotoneOn, monotone_snd, monotone_snd.monotoneOn, range_comp_of_nonneg
-/
theorem bddAbove_range_mul {α β : Type*} [Nonempty α] {u v : α -> β} [Preorder β] [Zero β] [Mul β]
    [PosMulMono β] [MulPosMono β] (hu : BddAbove (Set.range u)) (hu0 : 0 <= u)
    (hv : BddAbove (Set.range v)) (hv0 : 0 <= v) : BddAbove (Set.range (u * v)) :=
  letI : Zero (β × β) := ⟨(0, 0)⟩
  BddAbove.range_comp_of_nonneg (f := fun i => (u i, v i)) (g := fun x => x.1 * x.2)
    (bddAbove_range_prod.mpr ⟨hu, hv⟩) (fun x => ⟨hu0 x, hv0 x⟩) ((monotone_fst.monotoneOn _).mul
      (monotone_snd.monotoneOn _) (fun _ hx => hx.1) (fun _ hx => hx.2))
