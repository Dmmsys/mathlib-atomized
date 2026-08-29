/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison, Alex Keizer
-/
module

public import Mathlib.Data.List.OfFn
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Nodup

/-!
# Lists of elements of `Fin n`

This file develops some results on `finRange n`.
-/

public section

assert_not_exists Monoid

universe u

namespace List

variable {α : Type u}


@[simp]
/--
lemma `count_finRange` / 引理 `count_finRange`

English:
lemma count_finRange
  given: {n : Nat} (a : Fin n)
  statement: count a (finRange n) = 1
  proof: by
  simp [List.Nodup.count (nodup_finRange n)]

中文:
引理 count_finRange
  条件: {n : 自然数} (a : Fin n)
  结论: count a (finRange n) = 1
  证明: by
  simp [List.Nodup.count (nodup_finRange n)]

Depends on / 依赖: List.Nodup.count, nodup_finRange
-/
lemma count_finRange {n : Nat} (a : Fin n) : count a (finRange n) = 1 := by
  simp [List.Nodup.count (nodup_finRange n)]

/--
theorem `idxOf_finRange` / 定理 `idxOf_finRange`

English:
theorem idxOf_finRange
  given: {k : Nat} (i : Fin k)
  statement: (finRange k).idxOf i = i
  proof: by
  simpa using (nodup_finRange k).idxOf_getElem i

中文:
定理 idxOf_finRange
  条件: {k : 自然数} (i : Fin k)
  结论: (finRange k).idxOf i = i
  证明: by
  simpa using (nodup_finRange k).idxOf_getElem i
-/
@[simp] theorem idxOf_finRange {k : Nat} (i : Fin k) : (finRange k).idxOf i = i := by
  simpa using (nodup_finRange k).idxOf_getElem i

/--
theorem `ofFn_eq_pmap` / 定理 `ofFn_eq_pmap`

English:
theorem ofFn_eq_pmap
  given: {n} {f : Fin n -> α}
  proof: by
  ext
  grind

中文:
定理 ofFn_eq_pmap
  条件: {n} {f : Fin n -> α}
  证明: by
  ext
  grind
-/
theorem ofFn_eq_pmap {n} {f : Fin n -> α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  ext
  grind

/--
theorem `ofFn_id` / 定理 `ofFn_id`

English:
theorem ofFn_id
  given: (n)
  statement: ofFn id = finRange n
  proof: (rfl)

中文:
定理 ofFn_id
  条件: (n)
  结论: ofFn id = finRange n
  证明: (rfl)
-/
theorem ofFn_id (n) : ofFn id = finRange n :=
  (rfl)

/--
theorem `ofFn_eq_map` / 定理 `ofFn_eq_map`

English:
theorem ofFn_eq_map
  given: {n} {f : Fin n -> α}
  statement: ofFn f = (finRange n).map f
  proof: by
  rw [← ofFn_id]; rw [map_ofFn]; rw [Function.comp_id]

中文:
定理 ofFn_eq_map
  条件: {n} {f : Fin n -> α}
  结论: ofFn f = (finRange n).map f
  证明: by
  rw [← ofFn_id]; rw [map_ofFn]; rw [Function.comp_id]

Depends on / 依赖: Function, Function.comp_id, comp_id, map_ofFn, ofFn_id
-/
theorem ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange n).map f := by
  rw [← ofFn_id]; rw [map_ofFn]; rw [Function.comp_id]

/--
theorem `nodup_ofFn_ofInjective` / 定理 `nodup_ofFn_ofInjective`

English:
theorem nodup_ofFn_ofInjective
  given: {n} {f : Fin n -> α} (hf : Function.Injective f)
  proof: by
  rw [ofFn_eq_pmap]
exact nodup_range.pmap fun _ _ _ _ H => Fin.val_eq_of_eq hf H

中文:
定理 nodup_ofFn_ofInjective
  条件: {n} {f : Fin n -> α} (hf : Function.Injective f)
  证明: by
  rw [ofFn_eq_pmap]
exact nodup_range.pmap fun _ _ _ _ H => Fin.val_eq_of_eq hf H

Depends on / 依赖: Fin.val_eq_of_eq, nodup_range, nodup_range.pmap, ofFn_eq_pmap, val_eq_of_eq
-/
theorem nodup_ofFn_ofInjective {n} {f : Fin n -> α} (hf : Function.Injective f) :
    Nodup (ofFn f) := by
  rw [ofFn_eq_pmap]
exact nodup_range.pmap fun _ _ _ _ H => Fin.val_eq_of_eq hf H

/--
theorem `nodup_ofFn` / 定理 `nodup_ofFn`

English:
theorem nodup_ofFn
  given: {n} {f : Fin n -> α}
  statement: Nodup (ofFn f) ↔ Function.Injective f
  proof: by
  refine ⟨?_, nodup_ofFn_ofInjective⟩
  refine Fin.consInduction ?_ (fun x₀ xs ih => ?_) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right 

中文:
定理 nodup_ofFn
  条件: {n} {f : Fin n -> α}
  结论: Nodup (ofFn f) ↔ Function.Injective f
  证明: by
  refine ⟨?_, nodup_ofFn_ofInjective⟩
  refine Fin.consInduction ?_ (fun x₀ xs ih => ?_) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right 

Depends on / 依赖: Fin.consInduction, Fin.cons_injective_iff, Fin.cons_succ, Fin.cons_zero, Function, Function.injective_of_subsingleton, consInduction, cons_injective_iff, cons_succ, cons_zero, h.imp_right, imp_right, injective_of_subsingleton, mem_ofFn, nodup_cons, nodup_ofFn_ofInjective, ofFn_succ, simp_rw
-/
theorem nodup_ofFn {n} {f : Fin n -> α} : Nodup (ofFn f) ↔ Function.Injective f := by
  refine ⟨?_, nodup_ofFn_ofInjective⟩
  refine Fin.consInduction ?_ (fun x₀ xs ih => ?_) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right ih

end List

open List

/--
theorem `Equiv.Perm.map_finRange_perm` / 定理 `Equiv.Perm.map_finRange_perm`

English:
theorem Equiv.Perm.map_finRange_perm
  given: {n : Nat} (σ : Equiv.Perm (Fin n))
  proof: by
  rw [perm_ext_iff_of_nodup ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange] using! σ.surjective

中文:
定理 Equiv.Perm.map_finRange_perm
  条件: {n : 自然数} (σ : Equiv.Perm (Fin n))
  证明: by
  rw [perm_ext_iff_of_nodup ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange] using! σ.surjective

Depends on / 依赖: injective, mem_finRange, mem_map, nodup_finRange, perm_ext_iff_of_nodup, surjective
-/
theorem Equiv.Perm.map_finRange_perm {n : Nat} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
  rw [perm_ext_iff_of_nodup ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange] using! σ.surjective

/--
theorem `Equiv.Perm.ofFn_comp_perm` / 定理 `Equiv.Perm.ofFn_comp_perm`

English:
theorem Equiv.Perm.ofFn_comp_perm
  given: {n : Nat} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n -> α)
  proof: by
  rw [ofFn_eq_map]; rw [ofFn_eq_map]; rw [← map_map]
  exact σ.map_finRange_perm.map f

中文:
定理 Equiv.Perm.ofFn_comp_perm
  条件: {n : 自然数} {α : 类型u} (σ : Equiv.Perm (Fin n)) (f : Fin n -> α)
  证明: by
  rw [ofFn_eq_map]; rw [ofFn_eq_map]; rw [← map_map]
  exact σ.map_finRange_perm.map f

Depends on / 依赖: map_finRange_perm, map_finRange_perm.map, map_map, ofFn_eq_map
-/
theorem Equiv.Perm.ofFn_comp_perm {n : Nat} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n -> α) :
    ofFn (f ∘ σ) ~ ofFn f := by
  rw [ofFn_eq_map]; rw [ofFn_eq_map]; rw [← map_map]
  exact σ.map_finRange_perm.map f
