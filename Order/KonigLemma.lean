/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Grade

/-!
# Kőnig's infinity lemma

Kőnig's infinity lemma is most often stated as a graph theory result:
every infinite, locally finite connected graph contains an infinite path.
It has links to computability and proof theory, and it has a number of formulations.

In practice, most applications are not to an abstract graph,
but to a concrete collection of objects that are organized in a graph-like way,
often where the graph is a rooted tree representing a graded order.
In fact, the lemma is most easily stated and proved
in terms of covers in a strongly atomic order rather than a graph;
in this setting, the proof is almost trivial.

A common formulation of Kőnig's lemma is in terms of directed systems,
with the grading explicitly represented using an `ℕ`-indexed family of types,
which we also provide in this module.
This is a specialization of the much more general `nonempty_sections_of_finite_cofiltered_system`,
which goes through topology and category theory,
but here it is stated and proved independently with much fewer dependencies.

We leave the explicitly graph-theoretic version of the statement as TODO.

## Main Results

* `exists_seq_covby_of_forall_covby_finite` : Kőnig's lemma for strongly atomic orders.

* `exists_orderEmbedding_covby_of_forall_covby_finite` : Kőnig's lemma, where the sequence
  is given as an `OrderEmbedding` instead of a function.

* `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` : Kőnig's lemma where the sequence
  starts at the minimum of an infinite type.

* `exist_seq_forall_proj_of_forall_finite` : Kőnig's lemma for inverse systems,
  proved using the above applied to an order on a sigma-type `(i : ℕ) × α i`.

## TODO

Formulate the lemma as a statement about graphs.

-/

public section

open Set
section Sequence

variable {α : Type*} [PartialOrder α] [IsStronglyAtomic α] {b : α}

/--
theorem `exists_seq_covby_of_forall_covby_finite` / 定理 `exists_seq_covby_of_forall_covby_finite`

English:
theorem exists_seq_covby_of_forall_covby_finite
  statement: (hfin : forall (a : α), {x | a ⋖ x}.Finite)
  proof: let h := fun a : {a : α // (Ici a).Infinite} =>
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : Nat -> {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a => ⟨_, (h a).choose_spec.2⟩
  ⟨fun i => (ks i).1, by simp [ks], fun i => by simpa using (h (ks i)).choose_spec.1⟩

中文:
定理 exists_seq_covby_of_forall_covby_finite
  结论: (hfin : 对任意 (a : α), {x | a ⋖ x}.Finite)
  证明: let h := fun a : {a : α // (Ici a).Infinite} =>
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : Nat -> {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a => ⟨_, (h a).choose_spec.2⟩
  ⟨fun i => (ks i).1, by simp [ks], fun i => by simpa using (h (ks i)).choose_spec.1⟩

Depends on / 依赖: Infinite, Nat.rec, choose_spec, exists_covby_infinite_Ici_of_infinite_Ici
-/
theorem exists_seq_covby_of_forall_covby_finite (hfin : forall (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : exists f : Nat -> α, f 0 = b ∧ forall i, f i ⋖ f (i + 1) :=
  let h := fun a : {a : α // (Ici a).Infinite} =>
    exists_covby_infinite_Ici_of_infinite_Ici a.2 (hfin a)
  let ks : Nat -> {a : α // (Ici a).Infinite} := Nat.rec ⟨b, hb⟩ fun _ a => ⟨_, (h a).choose_spec.2⟩
  ⟨fun i => (ks i).1, by simp [ks], fun i => by simpa using (h (ks i)).choose_spec.1⟩

/--
theorem `exists_orderEmbedding_covby_of_forall_covby_finite` / 定理 `exists_orderEmbedding_covby_of_forall_covby_finite`

English:
theorem exists_orderEmbedding_covby_of_forall_covby_finite
  statement: (hfin : forall (a : α), {x | a ⋖ x}.Finite)
  proof: by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i => (hf.2 i).lt)), hf⟩

中文:
定理 exists_orderEmbedding_covby_of_forall_covby_finite
  结论: (hfin : 对任意 (a : α), {x | a ⋖ x}.Finite)
  证明: by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i => (hf.2 i).lt)), hf⟩

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, exists_seq_covby_of_forall_covby_finite, ofStrictMono, strictMono_nat_of_lt_succ
-/
theorem exists_orderEmbedding_covby_of_forall_covby_finite (hfin : forall (a : α), {x | a ⋖ x}.Finite)
    (hb : (Ici b).Infinite) : exists f : Nat ↪o α, f 0 = b ∧ forall i, f i ⋖ f (i + 1) := by
  obtain ⟨f, hf⟩ := exists_seq_covby_of_forall_covby_finite hfin hb
  exact ⟨OrderEmbedding.ofStrictMono f (strictMono_nat_of_lt_succ (fun i => (hf.2 i).lt)), hf⟩

/--
theorem `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot` / 定理 `exists_orderEmbedding_covby_of_forall_covby_finite_of_bot`

English:
theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot
  statement: [OrderBot α] [Infinite α]
  proof: exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

中文:
定理 exists_orderEmbedding_covby_of_forall_covby_finite_of_bot
  结论: [OrderBot α] [Infinite α]
  证明: exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

Depends on / 依赖: exists_orderEmbedding_covby_of_forall_covby_finite, infinite_univ
-/
theorem exists_orderEmbedding_covby_of_forall_covby_finite_of_bot [OrderBot α] [Infinite α]
    (hfin : forall (a : α), {x | a ⋖ x}.Finite) : exists f : Nat ↪o α, f 0 = ⊥ ∧ forall i, f i ⋖ f (i + 1) :=
  exists_orderEmbedding_covby_of_forall_covby_finite hfin (by simpa using infinite_univ)

/--
theorem `GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite` / 定理 `GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite`

English:
theorem GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
  proof: by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i => ?_⟩
  induction i with
  | zero => simp [h0]
| succ i ih => simpa [Order.covBy_iff_add_one_eq, ih, eq_comm] using CovBy.grade Nat hf i

中文:
定理 GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
  证明: by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i => ?_⟩
  induction i with
  | zero => simp [h0]
| succ i ih => simpa [Order.covBy_iff_add_one_eq, ih, eq_comm] using CovBy.grade Nat hf i

Depends on / 依赖: CovBy.grade, Order.covBy_iff_add_one_eq, covBy_iff_add_one_eq, eq_comm, exists_orderEmbedding_covby_of_forall_covby_finite_of_bot
-/
theorem GradeMinOrder.exists_nat_orderEmbedding_of_forall_covby_finite
    [GradeMinOrder Nat α] [OrderBot α] [Infinite α] (hfin : forall (a : α), {x | a ⋖ x}.Finite) :
    exists f : Nat ↪o α, f 0 = ⊥ ∧ (forall i, f i ⋖ f (i + 1)) ∧ forall i, grade Nat (f i) = i := by
  obtain ⟨f, h0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite_of_bot hfin
  refine ⟨f, h0, hf, fun i => ?_⟩
  induction i with
  | zero => simp [h0]
| succ i ih => simpa [Order.covBy_iff_add_one_eq, ih, eq_comm] using CovBy.grade Nat hf i

end Sequence

section Graded

/--
theorem `exists_seq_forall_proj_of_forall_finite` / 定理 `exists_seq_forall_proj_of_forall_finite`

English:
theorem exists_seq_forall_proj_of_forall_finite
  statement: {α : Nat -> Type*} [Finite (α 0)] [forall i, Nonempty (α i)]
  proof: by
  set αs := (i : Nat) × α i
  let _ : PartialOrder αs := {
    le := fun a b => exists h, π h b.2 = a.2
    le_refl := fun a => ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' => ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by grind }
  have hcovby : forall {a 

中文:
定理 exists_seq_forall_proj_of_forall_finite
  结论: {α : 自然数 -> 类型} [Finite (α 0)] [对任意 i, Nonempty (α i)]
  证明: by
  set αs := (i : Nat) × α i
  let _ : PartialOrder αs := {
    le := fun a b => exists h, π h b.2 = a.2
    le_refl := fun a => ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' => ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by grind }
  have hcovby : forall {a 

Depends on / 依赖: PartialOrder, Sigma.forall, and_assoc, and_congr_right_iff, covBy_iff_lt_and_eq_or_eq, hcovby, le_antisymm, le_refl, le_trans, lt_iff_le_and_ne, ne_eq, or_iff_not_imp_left, rfl.le
-/
theorem exists_seq_forall_proj_of_forall_finite {α : Nat -> Type*} [Finite (α 0)] [forall i, Nonempty (α i)]
    (π : {i j : Nat} -> (hij : i <= j) -> α j -> α i)
    (π_refl : forall ⦃i⦄ (a : α i), π rfl.le a = a)
    (π_trans : forall ⦃i j k⦄ (hij : i <= j) (hjk : j <= k) a, π hij (π hjk a) = π (hij.trans hjk) a)
    (hfin : forall i a, {b : α (i+1) | π (Nat.le_add_right i 1) b = a}.Finite) :
    exists f : (i : Nat) -> α i, forall ⦃i j⦄ (hij : i <= j), π hij (f j) = f i := by
  set αs := (i : Nat) × α i
  let _ : PartialOrder αs := {
    le := fun a b => exists h, π h b.2 = a.2
    le_refl := fun a => ⟨rfl.le, π_refl _⟩
    le_trans := fun _ _ c h h' => ⟨h.1.trans h'.1, by rw [← π_trans h.1 h'.1 c.2, h'.2, h.2]⟩
    le_antisymm := by grind }
  have hcovby : forall {a b : αs}, a ⋖ b ↔ a <= b ∧ a.1 + 1 = b.1 := by
    simp only [αs, covBy_iff_lt_and_eq_or_eq, lt_iff_le_and_ne, ne_eq, Sigma.forall, and_assoc,
      and_congr_right_iff, or_iff_not_imp_left]
    rintro i a j b ⟨h : i <= j, rfl : π h b = a⟩
    refine ⟨fun ⟨hne, h'⟩ => ?_, ?_⟩
· have hle' : i + 1 <= j := h.lt_of_ne by rintro rfl; simp [π_refl] at hne
exact congr_arg Sigma.fst h' (i + 1) (π hle' b) ⟨by simp, by rw [π_trans]⟩ ⟨hle', by simp⟩
        (fun h => by simp at h)
    rintro rfl
    refine ⟨fun h => by simp at h, ?_⟩
    rintro j c ⟨hij : i <= j, hcb : π _ c = π _ b⟩ ⟨hji : j <= i + 1, rfl : π hji b = c⟩ hne
    replace hne := show i != j by rintro rfl; contradiction
    obtain rfl := hji.antisymm (hij.lt_of_ne hne)
    rw [π_refl]
  have : IsStronglyAtomic αs := by
    simp_rw [isStronglyAtomic_iff, lt_iff_le_and_ne, hcovby]
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨⟨hij : i <= j, h2 : π hij b = a⟩, hne⟩
    have hle : i + 1 <= j := hij.lt_of_ne (by rintro rfl; simp [← h2, π_refl] at hne)
    exact ⟨⟨_, π hle b⟩, ⟨⟨by simp, by rw [π_trans, ← h2]⟩, by simp⟩, ⟨hle, by simp⟩⟩
  obtain ⟨a₀, ha₀, ha₀inf⟩ : exists a₀ : αs, a₀.1 = 0 ∧ (Ici a₀).Infinite := by
    obtain ⟨a₀, ha₀⟩ := Finite.exists_infinite_fiber (fun (a : αs) => π zero_le a.2)
    refine ⟨⟨0, a₀⟩, rfl, (infinite_coe_iff.1 ha₀).mono ?_⟩
    simp only [αs, subset_def, mem_preimage, mem_singleton_iff, mem_Ici, Sigma.forall]
    exact fun i x h => ⟨zero_le, h⟩
  have hfin : forall (a : αs), {x | a ⋖ x}.Finite := by
    refine fun ⟨i, a⟩ => ((hfin i a).image (fun b => ⟨_, b⟩)).subset ?_
    simp only [αs, hcovby, subset_def, mem_ofPred_eq, mem_image, and_imp, Sigma.forall]
    exact fun j b ⟨_, _⟩ hj => ⟨π hj.le b, by rwa [π_trans], by cases hj; rw [π_refl]⟩
  obtain ⟨f, hf0, hf⟩ := exists_orderEmbedding_covby_of_forall_covby_finite hfin ha₀inf
  have hr : forall i, (f i).1 = i :=
    Nat.rec (by rw [hf0, ha₀]) (fun i ih => by rw [← (hcovby.1 (hf i)).2, ih])
  refine ⟨fun i => by rw [← hr i]; exact (f i).2, fun i j hij => ?_⟩
  convert! (f.monotone hij).2 <;>
  simp [hr]

end Graded
