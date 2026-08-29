/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi

/-!
# Fin-indexed tuples of finsets
-/

public section

open Fin Fintype

namespace Fin
variable {n : Nat} {α : Fin (n + 1) -> Type*} {f : forall i, α i} {s : forall i, Finset (α i)} {p : Fin (n + 1)}

/--
lemma `mem_piFinset_iff_zero_tail` / 引理 `mem_piFinset_iff_zero_tail`

English:
lemma mem_piFinset_iff_zero_tail
  proof: by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]

中文:
引理 mem_piFinset_iff_zero_tail
  证明: by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]

Depends on / 依赖: Fintype, Fintype.mem_piFinset, forall_fin_succ, mem_piFinset
-/
lemma mem_piFinset_iff_zero_tail :
    f in Fintype.piFinset s ↔ f 0 in s 0 ∧ tail f in piFinset (tail s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]

/--
lemma `mem_piFinset_iff_last_init` / 引理 `mem_piFinset_iff_last_init`

English:
lemma mem_piFinset_iff_last_init
  proof: by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]

中文:
引理 mem_piFinset_iff_last_init
  证明: by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]

Depends on / 依赖: Fintype, Fintype.mem_piFinset, and_comm, forall_fin_succ, mem_piFinset
-/
lemma mem_piFinset_iff_last_init :
    f in piFinset s ↔ f (last n) in s (last n) ∧ init f in piFinset (init s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]

/--
lemma `mem_piFinset_iff_pivot_removeNth` / 引理 `mem_piFinset_iff_pivot_removeNth`

English:
lemma mem_piFinset_iff_pivot_removeNth
  given: (p : Fin (n + 1))
  proof: by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]

中文:
引理 mem_piFinset_iff_pivot_removeNth
  条件: (p : 有限集 (n + 1))
  证明: by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]

Depends on / 依赖: Fintype, Fintype.mem_piFinset, forall_iff_succAbove, mem_piFinset, removeNth
-/
lemma mem_piFinset_iff_pivot_removeNth (p : Fin (n + 1)) :
    f in piFinset s ↔ f p in s p ∧ removeNth p f in piFinset (removeNth p s) := by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]

/--
lemma `cons_mem_piFinset_cons` / 引理 `cons_mem_piFinset_cons`

English:
lemma cons_mem_piFinset_cons
  statement: {x_zero : α 0} {x_tail : (i : Fin n) -> α i.succ}
  proof: by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]

中文:
引理 cons_mem_piFinset_cons
  结论: {x_zero : α 0} {x_tail : (i : 有限集 n) -> α i.succ}
  证明: by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]

Depends on / 依赖: cons_zero, mem_piFinset_iff_zero_tail, simp_rw, tail_cons
-/
lemma cons_mem_piFinset_cons {x_zero : α 0} {x_tail : (i : Fin n) -> α i.succ}
    {s_zero : Finset (α 0)} {s_tail : (i : Fin n) -> Finset (α i.succ)} :
    cons x_zero x_tail in piFinset (cons s_zero s_tail) ↔
      x_zero in s_zero ∧ x_tail in piFinset s_tail := by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]

/--
lemma `snoc_mem_piFinset_snoc` / 引理 `snoc_mem_piFinset_snoc`

English:
lemma snoc_mem_piFinset_snoc
  statement: {x_last : α (last n)} {x_init : (i : Fin n) -> α i.castSucc}
  proof: by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]

中文:
引理 snoc_mem_piFinset_snoc
  结论: {x_last : α (last n)} {x_init : (i : 有限集 n) -> α i.castSucc}
  证明: by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]

Depends on / 依赖: init_snoc, mem_piFinset_iff_last_init, simp_rw, snoc_last
-/
lemma snoc_mem_piFinset_snoc {x_last : α (last n)} {x_init : (i : Fin n) -> α i.castSucc}
    {s_last : Finset (α (last n))} {s_init : (i : Fin n) -> Finset (α i.castSucc)} :
    snoc x_init x_last in piFinset (snoc s_init s_last) ↔
      x_last in s_last ∧ x_init in piFinset s_init := by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]

/--
lemma `insertNth_mem_piFinset_insertNth` / 引理 `insertNth_mem_piFinset_insertNth`

English:
lemma insertNth_mem_piFinset_insertNth
  statement: {x_pivot : α p} {x_remove : forall i, α (succAbove p i)}
  proof: by
  simp [mem_piFinset_iff_pivot_removeNth p]

中文:
引理 insertNth_mem_piFinset_insertNth
  结论: {x_pivot : α p} {x_remove : 对任意 i, α (succAbove p i)}
  证明: by
  simp [mem_piFinset_iff_pivot_removeNth p]

Depends on / 依赖: mem_piFinset_iff_pivot_removeNth
-/
lemma insertNth_mem_piFinset_insertNth {x_pivot : α p} {x_remove : forall i, α (succAbove p i)}
    {s_pivot : Finset (α p)} {s_remove : forall i, Finset (α (succAbove p i))} :
    insertNth p x_pivot x_remove in piFinset (insertNth p s_pivot s_remove) ↔
      x_pivot in s_pivot ∧ x_remove in piFinset s_remove := by
  simp [mem_piFinset_iff_pivot_removeNth p]

end Fin

namespace Finset
variable {n : Nat} {α : Fin (n + 1) -> Type*} {p : Fin (n + 1)} (S : forall i, Finset (α i))

/--
lemma `map_consEquiv_filter_piFinset` / 引理 `map_consEquiv_filter_piFinset`

English:
lemma map_consEquiv_filter_piFinset
  given: (P : (forall i, α (succ i)) -> Prop) [DecidablePred P]
  proof: by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]

中文:
引理 map_consEquiv_filter_piFinset
  条件: (P : (对任意 i, α (succ i)) -> 命题) [DecidablePred P]
  证明: by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]

Depends on / 依赖: Fin.forall_iff_succ, and_assoc, forall_iff_succ
-/
lemma map_consEquiv_filter_piFinset (P : (forall i, α (succ i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (tail r)}.map (consEquiv α).symm.toEmbedding =
      S 0 ×ˢ {r in piFinset (tail S) | P r} := by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]

/--
lemma `map_snocEquiv_filter_piFinset` / 引理 `map_snocEquiv_filter_piFinset`

English:
lemma map_snocEquiv_filter_piFinset
  given: (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P]
  proof: by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]

中文:
引理 map_snocEquiv_filter_piFinset
  条件: (P : (对任意 i, α (castSucc i)) -> 命题) [DecidablePred P]
  证明: by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]

Depends on / 依赖: Fin.forall_iff_castSucc, and_assoc, forall_iff_castSucc
-/
lemma map_snocEquiv_filter_piFinset (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (init r)}.map (snocEquiv α).symm.toEmbedding =
      S (last _) ×ˢ {r in piFinset (init S) | P r} := by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]

/--
lemma `map_insertNthEquiv_filter_piFinset` / 引理 `map_insertNthEquiv_filter_piFinset`

English:
lemma map_insertNthEquiv_filter_piFinset
  given: (P : (forall i, α (p.succAbove i)) -> Prop) [DecidablePred P]
  proof: by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]

中文:
引理 map_insertNthEquiv_filter_piFinset
  条件: (P : (对任意 i, α (p.succAbove i)) -> 命题) [DecidablePred P]
  证明: by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]

Depends on / 依赖: Fin.forall_iff_succAbove, and_assoc, forall_iff_succAbove, removeNth
-/
lemma map_insertNthEquiv_filter_piFinset (P : (forall i, α (p.succAbove i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (p.removeNth r)}.map (p.insertNthEquiv α).symm.toEmbedding =
      S p ×ˢ {r in piFinset (p.removeNth S) | P r} := by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]

/--
lemma `filter_piFinset_eq_map_consEquiv` / 引理 `filter_piFinset_eq_map_consEquiv`

English:
lemma filter_piFinset_eq_map_consEquiv
  given: (P : (forall i, α (succ i)) -> Prop) [DecidablePred P]
  proof: by
  simp [← map_consEquiv_filter_piFinset, map_map]

中文:
引理 filter_piFinset_eq_map_consEquiv
  条件: (P : (对任意 i, α (succ i)) -> 命题) [DecidablePred P]
  证明: by
  simp [← map_consEquiv_filter_piFinset, map_map]

Depends on / 依赖: map_consEquiv_filter_piFinset, map_map
-/
lemma filter_piFinset_eq_map_consEquiv (P : (forall i, α (succ i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (tail r)} =
      (S 0 ×ˢ {r in piFinset (tail S) | P r}).map (consEquiv α).toEmbedding := by
  simp [← map_consEquiv_filter_piFinset, map_map]

/--
lemma `filter_piFinset_eq_map_snocEquiv` / 引理 `filter_piFinset_eq_map_snocEquiv`

English:
lemma filter_piFinset_eq_map_snocEquiv
  given: (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P]
  proof: by
  simp [← map_snocEquiv_filter_piFinset, map_map]

中文:
引理 filter_piFinset_eq_map_snocEquiv
  条件: (P : (对任意 i, α (castSucc i)) -> 命题) [DecidablePred P]
  证明: by
  simp [← map_snocEquiv_filter_piFinset, map_map]

Depends on / 依赖: map_map, map_snocEquiv_filter_piFinset
-/
lemma filter_piFinset_eq_map_snocEquiv (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (init r)} =
      (S (last _) ×ˢ {r in piFinset (init S) | P r}).map (snocEquiv α).toEmbedding := by
  simp [← map_snocEquiv_filter_piFinset, map_map]

/--
lemma `filter_piFinset_eq_map_insertNthEquiv` / 引理 `filter_piFinset_eq_map_insertNthEquiv`

English:
lemma filter_piFinset_eq_map_insertNthEquiv
  statement: (P : (forall i, α (p.succAbove i)) -> Prop)
  proof: by
  simp [← map_insertNthEquiv_filter_piFinset, map_map]

中文:
引理 filter_piFinset_eq_map_insertNthEquiv
  结论: (P : (对任意 i, α (p.succAbove i)) -> 命题)
  证明: by
  simp [← map_insertNthEquiv_filter_piFinset, map_map]

Depends on / 依赖: map_insertNthEquiv_filter_piFinset, map_map
-/
lemma filter_piFinset_eq_map_insertNthEquiv (P : (forall i, α (p.succAbove i)) -> Prop)
    [DecidablePred P] :
    {r in piFinset S | P (p.removeNth r)} =
      (S p ×ˢ {r in piFinset (p.removeNth S) | P r}).map (p.insertNthEquiv α).toEmbedding := by
  simp [← map_insertNthEquiv_filter_piFinset, map_map]

/--
lemma `card_consEquiv_filter_piFinset` / 引理 `card_consEquiv_filter_piFinset`

English:
lemma card_consEquiv_filter_piFinset
  given: (P : (forall i, α (succ i)) -> Prop) [DecidablePred P]
  proof: by
  rw [← card_product]; rw [← map_consEquiv_filter_piFinset]; rw [card_map]

中文:
引理 card_consEquiv_filter_piFinset
  条件: (P : (对任意 i, α (succ i)) -> 命题) [DecidablePred P]
  证明: by
  rw [← card_product]; rw [← map_consEquiv_filter_piFinset]; rw [card_map]

Depends on / 依赖: card_map, card_product, map_consEquiv_filter_piFinset
-/
lemma card_consEquiv_filter_piFinset (P : (forall i, α (succ i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (tail r)}.card = (S 0).card * {r in piFinset (tail S) | P r}.card := by
  rw [← card_product]; rw [← map_consEquiv_filter_piFinset]; rw [card_map]

/--
lemma `card_snocEquiv_filter_piFinset` / 引理 `card_snocEquiv_filter_piFinset`

English:
lemma card_snocEquiv_filter_piFinset
  given: (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P]
  proof: by
  rw [← card_product]; rw [← map_snocEquiv_filter_piFinset]; rw [card_map]

中文:
引理 card_snocEquiv_filter_piFinset
  条件: (P : (对任意 i, α (castSucc i)) -> 命题) [DecidablePred P]
  证明: by
  rw [← card_product]; rw [← map_snocEquiv_filter_piFinset]; rw [card_map]

Depends on / 依赖: card_map, card_product, map_snocEquiv_filter_piFinset
-/
lemma card_snocEquiv_filter_piFinset (P : (forall i, α (castSucc i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (init r)}.card =
      (S (last _)).card * {r in piFinset (init S) | P r}.card := by
  rw [← card_product]; rw [← map_snocEquiv_filter_piFinset]; rw [card_map]

/--
lemma `card_insertNthEquiv_filter_piFinset` / 引理 `card_insertNthEquiv_filter_piFinset`

English:
lemma card_insertNthEquiv_filter_piFinset
  given: (P : (forall i, α (p.succAbove i)) -> Prop) [DecidablePred P]
  proof: by
  rw [← card_product]; rw [← map_insertNthEquiv_filter_piFinset]; rw [card_map]

中文:
引理 card_insertNthEquiv_filter_piFinset
  条件: (P : (对任意 i, α (p.succAbove i)) -> 命题) [DecidablePred P]
  证明: by
  rw [← card_product]; rw [← map_insertNthEquiv_filter_piFinset]; rw [card_map]

Depends on / 依赖: card_map, card_product, map_insertNthEquiv_filter_piFinset
-/
lemma card_insertNthEquiv_filter_piFinset (P : (forall i, α (p.succAbove i)) -> Prop) [DecidablePred P] :
    {r in piFinset S | P (p.removeNth r)}.card =
      (S p).card * {r in piFinset (p.removeNth S) | P r}.card := by
  rw [← card_product]; rw [← map_insertNthEquiv_filter_piFinset]; rw [card_map]

end Finset
