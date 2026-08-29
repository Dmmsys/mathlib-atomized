/-
Copyright (c) 2024 Joachim Breitner, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice

/-!
# Sum of suprema in `ENat`
-/

public section

assert_not_exists Field

namespace ENat

variable {a b c d : Nat∞} {r p q : Nat}

section OperationsAndInfty

variable {α : Type*}

@[simp]
/--
theorem `toNat_prod` / 定理 `toNat_prod`

English:
theorem toNat_prod
  given: {ι : Type*} {s : Finset ι} {f : ι -> Nat∞}
  proof: map_prod toNatHom _ _

中文:
定理 to自然数_prod
  条件: {ι : 类型} {s : 有限集 ι} {f : ι -> 自然数∞}
  证明: map_prod toNatHom _ _

Depends on / 依赖: map_prod, toNatHom
-/
theorem toNat_prod {ι : Type*} {s : Finset ι} {f : ι -> Nat∞} :
    (∏ i in s, f i).toNat = ∏ i in s, (f i).toNat :=
  map_prod toNatHom _ _

/--
theorem `iInf_sum` / 定理 `iInf_sum`

English:
theorem iInf_sum
  statement: {ι α : Type*} {f : ι -> α -> Nat∞} {s : Finset α} [Nonempty ι]
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_c

中文:
定理 iInf_sum
  结论: {ι α : 类型} {f : ι -> α -> 自然数∞} {s : 有限集 α} [非空 ι]
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_c

Depends on / 依赖: Finset, Finset.cons, Finset.cons_induction_on, Finset.forall_mem_cons, Finset.sum_cons, Finset.sum_empty, Finset.sum_le_sum, List.isRotatedDecidable, add_le_add, ciInf_const, cons_induction_on, forall_mem_cons, iInf_add_iInf, isRotatedDecidable, sum_cons, sum_empty, sum_le_sum
-/
theorem iInf_sum {ι α : Type*} {f : ι -> α -> Nat∞} {s : Finset α} [Nonempty ι]
    (h : forall (t : Finset α) (i j : ι), exists k, forall a in t, f k a <= f i a ∧ f k a <= f j a) :
    ⨅ i, ∑ a in s, f i a = ∑ a in s, ⨅ i, f i a := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

end OperationsAndInfty

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α -> Nat∞}

/--
lemma `prod_ne_top` / 引理 `prod_ne_top`

English:
lemma prod_ne_top
  given: (h : forall a in s, f a != ⊤)
  statement: ∏ a in s, f a != ⊤
  proof: WithTop.prod_ne_top h

中文:
引理 prod_ne_top
  条件: (h : 对任意 a in s, f a != ⊤)
  结论: ∏ a in s, f a != ⊤
  证明: WithTop.prod_ne_top h

Depends on / 依赖: WithTop, WithTop.prod_ne_top, prod_ne_top
-/
lemma prod_ne_top (h : forall a in s, f a != ⊤) : ∏ a in s, f a != ⊤ := WithTop.prod_ne_top h

/--
lemma `prod_lt_top` / 引理 `prod_lt_top`

English:
lemma prod_lt_top
  given: (h : forall a in s, f a < ⊤)
  statement: ∏ a in s, f a < ⊤
  proof: WithTop.prod_lt_top h

中文:
引理 prod_lt_top
  条件: (h : 对任意 a in s, f a < ⊤)
  结论: ∏ a in s, f a < ⊤
  证明: WithTop.prod_lt_top h

Depends on / 依赖: WithTop, WithTop.prod_lt_top, prod_lt_top
-/
lemma prod_lt_top (h : forall a in s, f a < ⊤) : ∏ a in s, f a < ⊤ := WithTop.prod_lt_top h

/--
lemma `sum_eq_top` / 引理 `sum_eq_top`

English:
lemma sum_eq_top
  statement: ∑ x in s, f x = ⊤ ↔ exists a in s, f a = ⊤
  proof: WithTop.sum_eq_top

中文:
引理 sum_eq_top
  结论: ∑ x in s, f x = ⊤ ↔ 存在 a in s, f a = ⊤
  证明: WithTop.sum_eq_top
-/
@[simp] lemma sum_eq_top : ∑ x in s, f x = ⊤ ↔ exists a in s, f a = ⊤ := WithTop.sum_eq_top

/--
lemma `sum_ne_top` / 引理 `sum_ne_top`

English:
lemma sum_ne_top
  statement: ∑ a in s, f a != ⊤ ↔ forall a in s, f a != ⊤
  proof: WithTop.sum_ne_top

中文:
引理 sum_ne_top
  结论: ∑ a in s, f a != ⊤ ↔ 对任意 a in s, f a != ⊤
  证明: WithTop.sum_ne_top

Depends on / 依赖: WithTop, WithTop.sum_ne_top, sum_ne_top
-/
lemma sum_ne_top : ∑ a in s, f a != ⊤ ↔ forall a in s, f a != ⊤ := WithTop.sum_ne_top

/--
lemma `sum_lt_top` / 引理 `sum_lt_top`

English:
lemma sum_lt_top
  statement: ∑ a in s, f a < ⊤ ↔ forall a in s, f a < ⊤
  proof: WithTop.sum_lt_top

中文:
引理 sum_lt_top
  结论: ∑ a in s, f a < ⊤ ↔ 对任意 a in s, f a < ⊤
  证明: WithTop.sum_lt_top
-/
@[simp] lemma sum_lt_top : ∑ a in s, f a < ⊤ ↔ forall a in s, f a < ⊤ := WithTop.sum_lt_top

/--
theorem `lt_top_of_sum_ne_top` / 定理 `lt_top_of_sum_ne_top`

English:
theorem lt_top_of_sum_ne_top
  statement: {s : Finset α} {f : α -> Nat∞} (h : ∑ x in s, f x != ⊤) {a : α}
  proof: sum_lt_top.1 h.lt_top a ha

中文:
定理 lt_top_of_sum_ne_top
  结论: {s : 有限集 α} {f : α -> 自然数∞} (h : ∑ x in s, f x != ⊤) {a : α}
  证明: sum_lt_top.1 h.lt_top a ha

Depends on / 依赖: h.lt_top, lt_top, sum_lt_top
-/
theorem lt_top_of_sum_ne_top {s : Finset α} {f : α -> Nat∞} (h : ∑ x in s, f x != ⊤) {a : α}
    (ha : a in s) : f a < ⊤ :=
  sum_lt_top.1 h.lt_top a ha

/--
theorem `toNat_sum` / 定理 `toNat_sum`

English:
theorem toNat_sum
  given: {s : Finset α} {f : α -> Nat∞} (hf : forall a in s, f a != ⊤)
  proof: by
  rw [← natCast_inj]; rw [natCast_toNat (sum_ne_top.2 hf)]; rw [Nat.cast_sum]
  exact sum_congr rfl fun x hx => (natCast_toNat (hf x hx)).symm

中文:
定理 to自然数_sum
  条件: {s : 有限集 α} {f : α -> 自然数∞} (hf : 对任意 a in s, f a != ⊤)
  证明: by
  rw [← natCast_inj]; rw [natCast_toNat (sum_ne_top.2 hf)]; rw [Nat.cast_sum]
  exact sum_congr rfl fun x hx => (natCast_toNat (hf x hx)).symm

Depends on / 依赖: Nat.cast_sum, cast_sum, natCast_inj, natCast_toNat, sum_congr, sum_ne_top
-/
theorem toNat_sum {s : Finset α} {f : α -> Nat∞} (hf : forall a in s, f a != ⊤) :
    ENat.toNat (∑ a in s, f a) = ∑ a in s, ENat.toNat (f a) := by
  rw [← natCast_inj]; rw [natCast_toNat (sum_ne_top.2 hf)]; rw [Nat.cast_sum]
  exact sum_congr rfl fun x hx => (natCast_toNat (hf x hx)).symm

/--
theorem `sum_lt_sum_of_nonempty` / 定理 `sum_lt_sum_of_nonempty`

English:
theorem sum_lt_sum_of_nonempty
  statement: {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞}
  proof: by
  induction hs using Nonempty.cons_induction with
  | singleton => simp [Hlt _ (mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENat.add_lt_add Hlt.1 (ih Hlt.2)

中文:
定理 sum_lt_sum_of_nonempty
  结论: {s : 有限集 α} (hs : s.非空) {f g : α -> 自然数∞}
  证明: by
  induction hs using Nonempty.cons_induction with
  | singleton => simp [Hlt _ (mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENat.add_lt_add Hlt.1 (ih Hlt.2)

Depends on / 依赖: ENat.add_lt_add, Nonempty, Nonempty.cons_induction, add_lt_add, cons_induction, forall_mem_cons, mem_singleton_self, singleton, sum_cons
-/
theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞}
    (Hlt : forall i in s, f i < g i) : ∑ i in s, f i < ∑ i in s, g i := by
  induction hs using Nonempty.cons_induction with
  | singleton => simp [Hlt _ (mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENat.add_lt_add Hlt.1 (ih Hlt.2)

/--
theorem `exists_le_of_sum_le` / 定理 `exists_le_of_sum_le`

English:
theorem exists_le_of_sum_le
  statement: {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞}
  proof: by
  contrapose! Hle
  apply sum_lt_sum_of_nonempty hs Hle

中文:
定理 存在_le_of_sum_le
  结论: {s : 有限集 α} (hs : s.非空) {f g : α -> 自然数∞}
  证明: by
  contrapose! Hle
  apply sum_lt_sum_of_nonempty hs Hle

Depends on / 依赖: contrapose, sum_lt_sum_of_nonempty
-/
theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α -> Nat∞}
    (Hle : ∑ i in s, f i <= ∑ i in s, g i) : exists i in s, f i <= g i := by
  contrapose! Hle
  apply sum_lt_sum_of_nonempty hs Hle

end Sum

/--
lemma `sum_iSup` / 引理 `sum_iSup`

English:
lemma sum_iSup
  statement: {α ι : Type*} {s : Finset α} {f : α -> ι -> Nat∞}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j => (hf i j).imp fun k hk => ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

中文:
引理 sum_iSup
  结论: {α ι : 类型} {s : 有限集 α} {f : α -> ι -> 自然数∞}
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j => (hf i j).imp fun k hk => ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

Depends on / 依赖: Finset, Finset.cons_induction, Finset.sum_cons, cons_induction, exacts, iSup_add_iSup, simp_rw, sum_cons
-/
lemma sum_iSup {α ι : Type*} {s : Finset α} {f : α -> ι -> Nat∞}
    (hf : forall i j, exists k, forall a, f a i <= f a k ∧ f a j <= f a k) :
    ∑ a in s, ⨆ i, f a i = ⨆ i, ∑ a in s, f a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j => (hf i j).imp fun k hk => ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

/--
lemma `sum_iSup_of_monotone` / 引理 `sum_iSup_of_monotone`

English:
lemma sum_iSup_of_monotone
  statement: {α ι : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
  proof: sum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

中文:
引理 sum_iSup_of_monotone
  结论: {α ι : 类型} [预序 ι] [IsDirectedOrder ι] {s : 有限集 α}
  证明: sum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

Depends on / 依赖: exists_ge_ge, sum_iSup
-/
lemma sum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
    {f : α -> ι -> Nat∞} (hf : forall a, Monotone (f a)) : (∑ a in s, iSup (f a)) = ⨆ n, ∑ a in s, f a n :=
  sum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

end ENat
