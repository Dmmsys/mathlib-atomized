/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.Congruence.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Interactions between `∑, ∏` and two-sided ideals

-/

public section

namespace TwoSidedIdeal

section sum

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

/--
lemma `listSum_mem` / 引理 `listSum_mem`

English:
lemma listSum_mem
  given: {ι : Type*} (l : List ι) (f : ι -> R) (hl : forall x in l, f x in I)
  proof: by
  rw [mem_iff]; rw [← List.sum_map_zero]
  exact I.ringCon.listSum l hl

中文:
引理 listSum_mem
  条件: {ι : 类型} (l : 列表 ι) (f : ι -> R) (hl : 对任意 x in l, f x in I)
  证明: by
  rw [mem_iff]; rw [← List.sum_map_zero]
  exact I.ringCon.listSum l hl

Depends on / 依赖: I.ringCon.listSum, List.sum_map_zero, listSum, mem_iff, ringCon, sum_map_zero
-/
lemma listSum_mem {ι : Type*} (l : List ι) (f : ι -> R) (hl : forall x in l, f x in I) :
    (l.map f).sum in I := by
  rw [mem_iff]; rw [← List.sum_map_zero]
  exact I.ringCon.listSum l hl

/--
lemma `multisetSum_mem` / 引理 `multisetSum_mem`

English:
lemma multisetSum_mem
  given: {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : forall x in s, f x in I)
  proof: by
  rw [mem_iff]; rw [← Multiset.sum_map_zero]
  exact I.ringCon.multisetSum s hs

中文:
引理 multisetSum_mem
  条件: {ι : 类型} (s : Multiset ι) (f : ι -> R) (hs : 对任意 x in s, f x in I)
  证明: by
  rw [mem_iff]; rw [← Multiset.sum_map_zero]
  exact I.ringCon.multisetSum s hs

Depends on / 依赖: I.ringCon.multisetSum, Multiset, Multiset.sum_map_zero, mem_iff, multisetSum, ringCon, sum_map_zero
-/
lemma multisetSum_mem {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : forall x in s, f x in I) :
    (s.map f).sum in I := by
  rw [mem_iff]; rw [← Multiset.sum_map_zero]
  exact I.ringCon.multisetSum s hs

/--
lemma `finsetSum_mem` / 引理 `finsetSum_mem`

English:
lemma finsetSum_mem
  given: {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : forall x in s, f x in I)
  proof: by
  rw [mem_iff]; rw [← Finset.sum_const_zero]
  exact I.ringCon.finsetSum s hs

中文:
引理 finsetSum_mem
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R) (hs : 对任意 x in s, f x in I)
  证明: by
  rw [mem_iff]; rw [← Finset.sum_const_zero]
  exact I.ringCon.finsetSum s hs

Depends on / 依赖: Finset, Finset.sum_const_zero, I.ringCon.finsetSum, finsetSum, mem_iff, ringCon, sum_const_zero
-/
lemma finsetSum_mem {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : forall x in s, f x in I) :
    s.sum f in I := by
  rw [mem_iff]; rw [← Finset.sum_const_zero]
  exact I.ringCon.finsetSum s hs

/--
lemma `finsuppSum_mem` / 引理 `finsuppSum_mem`

English:
lemma finsuppSum_mem
  statement: {ι : Type*} {β : Type*} [Zero β]
  proof: finsetSum_mem _ _ _ h

中文:
引理 finsuppSum_mem
  结论: {ι : 类型} {β : 类型} [零 β]
  证明: finsetSum_mem _ _ _ h

Depends on / 依赖: finsetSum_mem
-/
lemma finsuppSum_mem {ι : Type*} {β : Type*} [Zero β]
    {f : ι ->₀ β} (g : ι -> β -> R) (h : forall i in f.support, g i (f i) in I) :
    f.sum g in I :=
  finsetSum_mem _ _ _ h

/--
lemma `dfinsuppSum_mem` / 引理 `dfinsuppSum_mem`

English:
lemma dfinsuppSum_mem
  statement: {ι : Type*} {β : ι -> Type*}
  proof: finsetSum_mem _ _ _ h

中文:
引理 dfinsuppSum_mem
  结论: {ι : 类型} {β : ι -> 类型}
  证明: finsetSum_mem _ _ _ h

Depends on / 依赖: finsetSum_mem
-/
lemma dfinsuppSum_mem {ι : Type*} {β : ι -> Type*}
    [DecidableEq ι] [forall i, Zero (β i)] [(i : ι) -> (x : β i) -> Decidable (x != 0)]
    {f : Π₀ i, β i} (g : (i : ι) -> β i -> R) (h : forall i in f.support, g i (f i) in I) :
    f.sum g in I :=
  finsetSum_mem _ _ _ h

end sum

section prod

section ring

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

/--
lemma `listProd_mem` / 引理 `listProd_mem`

English:
lemma listProd_mem
  given: {ι : Type*} (l : List ι) (f : ι -> R) (hl : exists x in l, f x in I)
  proof: by
  induction l with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hl
  | cons x l ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hl
    rcases hl with h | hal
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
· simpa only [List.map_cons, L

中文:
引理 listProd_mem
  条件: {ι : 类型} (l : 列表 ι) (f : ι -> R) (hl : 存在 x in l, f x in I)
  证明: by
  induction l with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hl
  | cons x l ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hl
    rcases hl with h | hal
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
· simpa only [List.map_cons, L

Depends on / 依赖: I.mul_mem_left, I.mul_mem_right, List.map_cons, List.mem_cons, List.not_mem_nil, List.prod_cons, exists_eq_or_imp, exists_false, false_and, map_cons, mem_cons, mul_mem_left, mul_mem_right, not_mem_nil, prod_cons
-/
lemma listProd_mem {ι : Type*} (l : List ι) (f : ι -> R) (hl : exists x in l, f x in I) :
    (l.map f).prod in I := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hl
  | cons x l ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hl
    rcases hl with h | hal
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
· simpa only [List.map_cons, List.prod_cons] using I.mul_mem_left _ _ ih hal

end ring

section commRing

variable {R : Type*} [CommRing R] (I : TwoSidedIdeal R)

/--
lemma `multiSetProd_mem` / 引理 `multiSetProd_mem`

English:
lemma multiSetProd_mem
  given: {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : exists x in s, f x in I)
  proof: by
  rcases s
  simpa using listProd_mem (hl := hs)

中文:
引理 multiSetProd_mem
  条件: {ι : 类型} (s : Multiset ι) (f : ι -> R) (hs : 存在 x in s, f x in I)
  证明: by
  rcases s
  simpa using listProd_mem (hl := hs)

Depends on / 依赖: listProd_mem
-/
lemma multiSetProd_mem {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : exists x in s, f x in I) :
    (s.map f).prod in I := by
  rcases s
  simpa using listProd_mem (hl := hs)

/--
lemma `finsetProd_mem` / 引理 `finsetProd_mem`

English:
lemma finsetProd_mem
  given: {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : exists x in s, f x in I)
  proof: by
  rcases s
  simpa using multiSetProd_mem (hs := hs)

中文:
引理 finsetProd_mem
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> R) (hs : 存在 x in s, f x in I)
  证明: by
  rcases s
  simpa using multiSetProd_mem (hs := hs)

Depends on / 依赖: multiSetProd_mem
-/
lemma finsetProd_mem {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : exists x in s, f x in I) :
    s.prod f in I := by
  rcases s
  simpa using multiSetProd_mem (hs := hs)

/--
lemma `finsuppProd_mem` / 引理 `finsuppProd_mem`

English:
lemma finsuppProd_mem
  statement: {ι : Type*} {β : Type*} [Zero β]
  proof: finsetProd_mem _ _ _ H

中文:
引理 finsuppProd_mem
  结论: {ι : 类型} {β : 类型} [零 β]
  证明: finsetProd_mem _ _ _ H

Depends on / 依赖: finsetProd_mem
-/
lemma finsuppProd_mem {ι : Type*} {β : Type*} [Zero β]
    (h : ι -> β -> R) {f : ι ->₀ β} (H : exists i in f.support, h i (f i) in I) : f.prod h in I :=
  finsetProd_mem _ _ _ H

/--
lemma `dfinsuppProd_mem` / 引理 `dfinsuppProd_mem`

English:
lemma dfinsuppProd_mem
  statement: {ι : Type*} {β : ι -> Type*}
  proof: finsetProd_mem _ _ _ h

中文:
引理 dfinsuppProd_mem
  结论: {ι : 类型} {β : ι -> 类型}
  证明: finsetProd_mem _ _ _ h

Depends on / 依赖: finsetProd_mem
-/
lemma dfinsuppProd_mem {ι : Type*} {β : ι -> Type*}
    [DecidableEq ι] [forall i, Zero (β i)] [(i : ι) -> (x : β i) -> Decidable (x != 0)]
    {f : Π₀ i, β i} (g : (i : ι) -> β i -> R) (h : exists i in f.support, g i (f i) in I) :
    f.prod g in I :=
  finsetProd_mem _ _ _ h

end commRing

end prod

end TwoSidedIdeal
