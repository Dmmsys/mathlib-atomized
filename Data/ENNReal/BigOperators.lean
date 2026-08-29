/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.WithTop
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.ENNReal.Inv

/-!
# Properties of big operators extended non-negative real numbers

In this file we prove elementary properties of sums and products on `ℝ≥0∞`, as well as how these
interact with the order structure on `ℝ≥0∞`.
-/

public section

open Set NNReal

namespace ENNReal

variable {a b c d : Real>=0∞} {r p q : Real>=0}

section OperationsAndInfty

variable {ι M : Type*} [Zero M]

@[simp, norm_cast]
/--
lemma `ofNNReal_finsetSum` / 引理 `ofNNReal_finsetSum`

English:
lemma ofNNReal_finsetSum
  given: (s : Finset ι) (f : ι -> Real>=0)
  statement: ↑(∑ i in s, f i) = ∑ i in s, ofNNReal (f i)
  proof: map_sum ofNNRealHom ..

@[deprecated (since := "2026-06-04")] alias coe_finsetSum := ofNNReal_finsetSum
@[deprecated (since := "2026-04-08")] alias coe_finset_sum := ofNNReal_finsetSum

@[simp, norm_cast]

中文:
引理 ofNN实数_finsetSum
  条件: (s : 有限集 ι) (f : ι -> 实数>=0)
  结论: ↑(∑ i in s, f i) = ∑ i in s, ofNN实数 (f i)
  证明: map_sum ofNNRealHom ..

@[deprecated (since := "2026-06-04")] alias coe_finsetSum := ofNNReal_finsetSum
@[deprecated (since := "2026-04-08")] alias coe_finset_sum := ofNNReal_finsetSum

@[simp, norm_cast]

Depends on / 依赖: map_sum, ofNNRealHom
-/
lemma ofNNReal_finsetSum (s : Finset ι) (f : ι -> Real>=0) : ↑(∑ i in s, f i) = ∑ i in s, ofNNReal (f i) :=
  map_sum ofNNRealHom ..

@[deprecated (since := "2026-06-04")] alias coe_finsetSum := ofNNReal_finsetSum
@[deprecated (since := "2026-04-08")] alias coe_finset_sum := ofNNReal_finsetSum

@[simp, norm_cast]
/--
lemma `ofNNReal_finsetProd` / 引理 `ofNNReal_finsetProd`

English:
lemma ofNNReal_finsetProd
  given: (s : Finset ι) (f : ι -> Real>=0)
  proof: map_prod ofNNRealHom f s

@[deprecated (since := "2026-06-04")] alias coe_finsetProd := ofNNReal_finsetProd
@[deprecated (since := "2026-04-08")] alias coe_finset_prod := ofNNReal_finsetProd

@[simp, norm_cast]

中文:
引理 ofNN实数_finsetProd
  条件: (s : 有限集 ι) (f : ι -> 实数>=0)
  证明: map_prod ofNNRealHom f s

@[deprecated (since := "2026-06-04")] alias coe_finsetProd := ofNNReal_finsetProd
@[deprecated (since := "2026-04-08")] alias coe_finset_prod := ofNNReal_finsetProd

@[simp, norm_cast]

Depends on / 依赖: map_prod, ofNNRealHom
-/
lemma ofNNReal_finsetProd (s : Finset ι) (f : ι -> Real>=0) :
    ↑(∏ i in s, f i) = ∏ i in s, ofNNReal (f i) := map_prod ofNNRealHom f s

@[deprecated (since := "2026-06-04")] alias coe_finsetProd := ofNNReal_finsetProd
@[deprecated (since := "2026-04-08")] alias coe_finset_prod := ofNNReal_finsetProd

@[simp, norm_cast]
/--
lemma `ofNNReal_finsuppSum` / 引理 `ofNNReal_finsuppSum`

English:
lemma ofNNReal_finsuppSum
  given: (f : ι ->₀ M) (g : ι -> M -> Real>=0)
  proof: map_finsuppSum ofNNRealHom ..

@[simp, norm_cast]

中文:
引理 ofNN实数_finsuppSum
  条件: (f : ι ->₀ M) (g : ι -> M -> 实数>=0)
  证明: map_finsuppSum ofNNRealHom ..

@[simp, norm_cast]

Depends on / 依赖: map_finsuppSum, ofNNRealHom
-/
lemma ofNNReal_finsuppSum (f : ι ->₀ M) (g : ι -> M -> Real>=0) :
    f.sum g = f.sum (fun i m => ofNNReal (g i m)) := map_finsuppSum ofNNRealHom ..

@[simp, norm_cast]
/--
lemma `ofNNReal_finsuppProd` / 引理 `ofNNReal_finsuppProd`

English:
lemma ofNNReal_finsuppProd
  given: (f : ι ->₀ M) (g : ι -> M -> Real>=0)
  proof: map_finsuppProd ofNNRealHom ..

@[simp]

中文:
引理 ofNN实数_finsuppProd
  条件: (f : ι ->₀ M) (g : ι -> M -> 实数>=0)
  证明: map_finsuppProd ofNNRealHom ..

@[simp]

Depends on / 依赖: map_finsuppProd, ofNNRealHom
-/
lemma ofNNReal_finsuppProd (f : ι ->₀ M) (g : ι -> M -> Real>=0) :
    f.prod g = f.prod (fun i m => ofNNReal (g i m)) := map_finsuppProd ofNNRealHom ..

@[simp]
/--
theorem `toNNReal_prod` / 定理 `toNNReal_prod`

English:
theorem toNNReal_prod
  given: (s : Finset ι) (f : ι -> Real>=0∞)
  proof: map_prod toNNRealHom _ _

@[simp]

中文:
定理 toNN实数_prod
  条件: (s : 有限集 ι) (f : ι -> 实数>=0∞)
  证明: map_prod toNNRealHom _ _

@[simp]

Depends on / 依赖: map_prod, toNNRealHom
-/
theorem toNNReal_prod (s : Finset ι) (f : ι -> Real>=0∞) :
    (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal :=
  map_prod toNNRealHom _ _

@[simp]
/--
theorem `toReal_prod` / 定理 `toReal_prod`

English:
theorem toReal_prod
  given: (s : Finset ι) (f : ι -> Real>=0∞)
  proof: map_prod toRealHom _ _

中文:
定理 to实数_prod
  条件: (s : 有限集 ι) (f : ι -> 实数>=0∞)
  证明: map_prod toRealHom _ _

Depends on / 依赖: map_prod, toRealHom
-/
theorem toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) :
    (∏ i in s, f i).toReal = ∏ i in s, (f i).toReal :=
  map_prod toRealHom _ _

/--
theorem `ofReal_prod_of_nonneg` / 定理 `ofReal_prod_of_nonneg`

English:
theorem ofReal_prod_of_nonneg
  given: {α : Type*} {s : Finset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i)
  proof: by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetProd, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf

中文:
定理 of实数_prod_of_nonneg
  条件: {α : 类型} {s : 有限集 α} {f : α -> 实数} (hf : 对任意 i, i in s -> 0 <= f i)
  证明: by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetProd, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_prod_of_nonneg, coe_inj, ofNNReal_finsetProd, ofReal, simp_rw, toNNReal_prod_of_nonneg
-/
theorem ofReal_prod_of_nonneg {α : Type*} {s : Finset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i) :
    ENNReal.ofReal (∏ i in s, f i) = ∏ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetProd, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf

/--
theorem `iInf_sum` / 定理 `iInf_sum`

English:
theorem iInf_sum
  statement: {ι α : Type*} {f : ι -> α -> Real>=0∞} {s : Finset α} [Nonempty ι]
  proof: by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

中文:
定理 iInf_sum
  结论: {ι α : 类型} {f : ι -> α -> 实数>=0∞} {s : 有限集 α} [非空 ι]
  证明: by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

Depends on / 依赖: Finset, Finset.cons, Finset.cons_induction_on, Finset.forall_mem_cons, Finset.sum_cons, Finset.sum_empty, Finset.sum_le_sum, add_le_add, ciInf_const, cons_induction_on, forall_mem_cons, iInf_add_iInf, sum_cons, sum_empty, sum_le_sum
-/
theorem iInf_sum {ι α : Type*} {f : ι -> α -> Real>=0∞} {s : Finset α} [Nonempty ι]
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

variable {α : Type*} {s : Finset α} {f : α -> Real>=0∞}

/--
lemma `prod_ne_top` / 引理 `prod_ne_top`

English:
lemma prod_ne_top
  given: (h : forall a in s, f a != ∞)
  statement: ∏ a in s, f a != ∞
  proof: WithTop.prod_ne_top h

中文:
引理 prod_ne_top
  条件: (h : 对任意 a in s, f a != ∞)
  结论: ∏ a in s, f a != ∞
  证明: WithTop.prod_ne_top h

Depends on / 依赖: WithTop, WithTop.prod_ne_top, prod_ne_top
-/
lemma prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in s, f a != ∞ := WithTop.prod_ne_top h

/--
lemma `prod_lt_top` / 引理 `prod_lt_top`

English:
lemma prod_lt_top
  given: (h : forall a in s, f a < ∞)
  statement: ∏ a in s, f a < ∞
  proof: WithTop.prod_lt_top h

中文:
引理 prod_lt_top
  条件: (h : 对任意 a in s, f a < ∞)
  结论: ∏ a in s, f a < ∞
  证明: WithTop.prod_lt_top h

Depends on / 依赖: WithTop, WithTop.prod_lt_top, prod_lt_top
-/
lemma prod_lt_top (h : forall a in s, f a < ∞) : ∏ a in s, f a < ∞ := WithTop.prod_lt_top h

/--
lemma `sum_eq_top` / 引理 `sum_eq_top`

English:
lemma sum_eq_top
  statement: ∑ x in s, f x = ∞ ↔ exists a in s, f a = ∞
  proof: WithTop.sum_eq_top

中文:
引理 sum_eq_top
  结论: ∑ x in s, f x = ∞ ↔ 存在 a in s, f a = ∞
  证明: WithTop.sum_eq_top
-/
@[simp] lemma sum_eq_top : ∑ x in s, f x = ∞ ↔ exists a in s, f a = ∞ := WithTop.sum_eq_top

/--
lemma `sum_ne_top` / 引理 `sum_ne_top`

English:
lemma sum_ne_top
  statement: ∑ a in s, f a != ∞ ↔ forall a in s, f a != ∞
  proof: WithTop.sum_ne_top

中文:
引理 sum_ne_top
  结论: ∑ a in s, f a != ∞ ↔ 对任意 a in s, f a != ∞
  证明: WithTop.sum_ne_top

Depends on / 依赖: WithTop, WithTop.sum_ne_top, sum_ne_top
-/
lemma sum_ne_top : ∑ a in s, f a != ∞ ↔ forall a in s, f a != ∞ := WithTop.sum_ne_top

/--
lemma `sum_lt_top` / 引理 `sum_lt_top`

English:
lemma sum_lt_top
  statement: ∑ a in s, f a < ∞ ↔ forall a in s, f a < ∞
  proof: WithTop.sum_lt_top

中文:
引理 sum_lt_top
  结论: ∑ a in s, f a < ∞ ↔ 对任意 a in s, f a < ∞
  证明: WithTop.sum_lt_top
-/
@[simp] lemma sum_lt_top : ∑ a in s, f a < ∞ ↔ forall a in s, f a < ∞ := WithTop.sum_lt_top

/--
theorem `lt_top_of_sum_ne_top` / 定理 `lt_top_of_sum_ne_top`

English:
theorem lt_top_of_sum_ne_top
  statement: {s : Finset α} {f : α -> Real>=0∞} (h : ∑ x in s, f x != ∞) {a : α}
  proof: sum_lt_top.1 h.lt_top a ha

中文:
定理 lt_top_of_sum_ne_top
  结论: {s : 有限集 α} {f : α -> 实数>=0∞} (h : ∑ x in s, f x != ∞) {a : α}
  证明: sum_lt_top.1 h.lt_top a ha

Depends on / 依赖: h.lt_top, lt_top, sum_lt_top
-/
theorem lt_top_of_sum_ne_top {s : Finset α} {f : α -> Real>=0∞} (h : ∑ x in s, f x != ∞) {a : α}
    (ha : a in s) : f a < ∞ :=
  sum_lt_top.1 h.lt_top a ha

/--
theorem `toNNReal_sum` / 定理 `toNNReal_sum`

English:
theorem toNNReal_sum
  given: {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a != ∞)
  proof: by
  rw [← coe_inj]; rw [coe_toNNReal]; rw [ofNNReal_finsetSum]; rw [sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

中文:
定理 toNN实数_sum
  条件: {s : 有限集 α} {f : α -> 实数>=0∞} (hf : 对任意 a in s, f a != ∞)
  证明: by
  rw [← coe_inj]; rw [coe_toNNReal]; rw [ofNNReal_finsetSum]; rw [sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

Depends on / 依赖: coe_inj, coe_toNNReal, ofNNReal_finsetSum, sum_congr, sum_ne_top
-/
theorem toNNReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a != ∞) :
    ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNReal.toNNReal (f a) := by
  rw [← coe_inj]; rw [coe_toNNReal]; rw [ofNNReal_finsetSum]; rw [sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

/--
theorem `toReal_sum` / 定理 `toReal_sum`

English:
theorem toReal_sum
  given: {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a != ∞)
  proof: by
  rw [ENNReal.toReal]; rw [toNNReal_sum hf]; rw [NNReal.coe_sum]
  rfl

中文:
定理 to实数_sum
  条件: {s : 有限集 α} {f : α -> 实数>=0∞} (hf : 对任意 a in s, f a != ∞)
  证明: by
  rw [ENNReal.toReal]; rw [toNNReal_sum hf]; rw [NNReal.coe_sum]
  rfl

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_sum, coe_sum, toNNReal_sum, toReal
-/
theorem toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : forall a in s, f a != ∞) :
    ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal]; rw [toNNReal_sum hf]; rw [NNReal.coe_sum]
  rfl

/--
theorem `ofReal_sum_of_nonneg` / 定理 `ofReal_sum_of_nonneg`

English:
theorem ofReal_sum_of_nonneg
  given: {s : Finset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i)
  proof: by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetSum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf

中文:
定理 of实数_sum_of_nonneg
  条件: {s : 有限集 α} {f : α -> 实数} (hf : 对任意 i, i in s -> 0 <= f i)
  证明: by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetSum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_sum_of_nonneg, coe_inj, ofNNReal_finsetSum, ofReal, simp_rw, toNNReal_sum_of_nonneg
-/
theorem ofReal_sum_of_nonneg {s : Finset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i) :
    ENNReal.ofReal (∑ i in s, f i) = ∑ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← ofNNReal_finsetSum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf

/--
theorem `sum_lt_sum_of_nonempty` / 定理 `sum_lt_sum_of_nonempty`

English:
theorem sum_lt_sum_of_nonempty
  statement: {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=0∞}
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)

中文:
定理 sum_lt_sum_of_nonempty
  结论: {s : 有限集 α} (hs : s.非空) {f g : α -> 实数>=0∞}
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)

Depends on / 依赖: ENNReal, ENNReal.add_lt_add, Finset, Finset.Nonempty.cons_induction, Finset.mem_singleton_self, Finset.sum_cons, Nonempty, add_lt_add, cons_induction, forall_mem_cons, mem_singleton_self, singleton, sum_cons
-/
theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=0∞}
    (Hlt : forall i in s, f i < g i) : ∑ i in s, f i < ∑ i in s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)

/--
theorem `exists_le_of_sum_le` / 定理 `exists_le_of_sum_le`

English:
theorem exists_le_of_sum_le
  statement: {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=0∞}
  proof: by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

中文:
定理 存在_le_of_sum_le
  结论: {s : 有限集 α} (hs : s.非空) {f g : α -> 实数>=0∞}
  证明: by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

Depends on / 依赖: ENNReal, ENNReal.sum_lt_sum_of_nonempty, contrapose, sum_lt_sum_of_nonempty
-/
theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α -> Real>=0∞}
    (Hle : ∑ i in s, f i <= ∑ i in s, g i) : exists i in s, f i <= g i := by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

end Sum

section Inv

variable {ι : Type*} {f g : ι -> Real>=0∞} {s : Finset ι}

/--
lemma `prod_inv_distrib` / 引理 `prod_inv_distrib`

English:
lemma prod_inv_distrib
  given: (hf : (s : Set ι).Pairwise fun i j => f i != 0 ∨ f j != ∞)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => ?_
  simp only [Finset.prod_cons, ← ih (hf.mono <| by simp)]
  refine ENNReal.mul_inv (not_or_of_imp fun hi₀ => prod_ne_top fun j hj => ?_)
    (not_or_of_imp fun hi₀ => Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  · exact imp_iff_not_or.2 (hf (by simp) (by simp [hj]) <| .symm <| ne_of_mem_of_not_mem hj hi) hi₀
  · exact imp_iff_not_or.2 (hf (by simp [hj]) (by simp) <| ne_of_mem_of_not_mem hj hi).symm hi₀

中文:
引理 prod_inv_distrib
  条件: (hf : (s : 集合 ι).两两 fun i j => f i != 0 ∨ f j != ∞)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => ?_
  simp only [Finset.prod_cons, ← ih (hf.mono <| by simp)]
  refine ENNReal.mul_inv (not_or_of_imp fun hi₀ => prod_ne_top fun j hj => ?_)
    (not_or_of_imp fun hi₀ => Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  · exact imp_iff_not_or.2 (hf (by simp) (by simp [hj]) <| .symm <| ne_of_mem_of_not_mem hj hi) hi₀
  · exact imp_iff_not_or.2 (hf (by simp [hj]) (by simp) <| ne_of_mem_of_not_mem hj hi).symm hi₀

Depends on / 依赖: ENNReal, ENNReal.mul_inv, Finset, Finset.cons_induction, Finset.prod_cons, Finset.prod_ne_zero_iff, cons_induction, hf.mono, imp_iff_not_or, mul_inv, ne_of_mem_of_not_mem, not_or_of_imp, prod_cons, prod_ne_top, prod_ne_zero_iff
-/
lemma prod_inv_distrib (hf : (s : Set ι).Pairwise fun i j => f i != 0 ∨ f j != ∞) :
    (∏ i in s, f i)⁻¹ = ∏ i in s, (f i)⁻¹ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => ?_
  simp only [Finset.prod_cons, ← ih (hf.mono <| by simp)]
  refine ENNReal.mul_inv (not_or_of_imp fun hi₀ => prod_ne_top fun j hj => ?_)
    (not_or_of_imp fun hi₀ => Finset.prod_ne_zero_iff.2 fun j hj => ?_)
  · exact imp_iff_not_or.2 (hf (by simp) (by simp [hj]) <| .symm <| ne_of_mem_of_not_mem hj hi) hi₀
  · exact imp_iff_not_or.2 (hf (by simp [hj]) (by simp) <| ne_of_mem_of_not_mem hj hi).symm hi₀

/--
lemma `prod_div_distrib` / 引理 `prod_div_distrib`

English:
lemma prod_div_distrib
  given: (hg : (s : Set ι).Pairwise fun i j => g i != 0 ∨ g j != ∞)
  proof: by
  simp only [div_eq_mul_inv, prod_inv_distrib hg, ← Finset.prod_mul_distrib]

中文:
引理 prod_div_distrib
  条件: (hg : (s : 集合 ι).两两 fun i j => g i != 0 ∨ g j != ∞)
  证明: by
  simp only [div_eq_mul_inv, prod_inv_distrib hg, ← Finset.prod_mul_distrib]

Depends on / 依赖: Finset, Finset.prod_mul_distrib, div_eq_mul_inv, prod_inv_distrib, prod_mul_distrib
-/
lemma prod_div_distrib (hg : (s : Set ι).Pairwise fun i j => g i != 0 ∨ g j != ∞) :
    (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i in s, g i) := by
  simp only [div_eq_mul_inv, prod_inv_distrib hg, ← Finset.prod_mul_distrib]

/--
lemma `prod_div_distrib_of_ne_top` / 引理 `prod_div_distrib_of_ne_top`

English:
lemma prod_div_distrib_of_ne_top
  given: (hg : forall i in s, g i != ∞)
  proof: prod_div_distrib (by grind [Set.Pairwise])

中文:
引理 prod_div_distrib_of_ne_top
  条件: (hg : 对任意 i in s, g i != ∞)
  证明: prod_div_distrib (by grind [Set.Pairwise])

Depends on / 依赖: Pairwise, Set.Pairwise, prod_div_distrib
-/
lemma prod_div_distrib_of_ne_top (hg : forall i in s, g i != ∞) :
    (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i in s, g i) :=
  prod_div_distrib (by grind [Set.Pairwise])

/--
lemma `prod_div_distrib_of_ne_zero` / 引理 `prod_div_distrib_of_ne_zero`

English:
lemma prod_div_distrib_of_ne_zero
  given: (hg : forall i in s, g i != 0)
  proof: prod_div_distrib (by grind [Set.Pairwise])

中文:
引理 prod_div_distrib_of_ne_zero
  条件: (hg : 对任意 i in s, g i != 0)
  证明: prod_div_distrib (by grind [Set.Pairwise])

Depends on / 依赖: Pairwise, Set.Pairwise, prod_div_distrib
-/
lemma prod_div_distrib_of_ne_zero (hg : forall i in s, g i != 0) :
    (∏ i in s, f i / g i) = (∏ i in s, f i) / (∏ i in s, g i) :=
  prod_div_distrib (by grind [Set.Pairwise])

/--
lemma `finsetSum_iSup` / 引理 `finsetSum_iSup`

English:
lemma finsetSum_iSup
  statement: {α : Type*} {s : Finset α} {f : α -> ι -> Real>=0∞}
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j => (hf i j).imp fun k hk => ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

中文:
引理 finsetSum_iSup
  结论: {α : 类型} {s : 有限集 α} {f : α -> ι -> 实数>=0∞}
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
lemma finsetSum_iSup {α : Type*} {s : Finset α} {f : α -> ι -> Real>=0∞}
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
lemma `finsetSum_iSup_of_monotone` / 引理 `finsetSum_iSup_of_monotone`

English:
lemma finsetSum_iSup_of_monotone
  statement: {α : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
  proof: finsetSum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

中文:
引理 finsetSum_iSup_of_monotone
  结论: {α : 类型} [预序 ι] [IsDirectedOrder ι] {s : 有限集 α}
  证明: finsetSum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

Depends on / 依赖: exists_ge_ge, finsetSum_iSup
-/
lemma finsetSum_iSup_of_monotone {α : Type*} [Preorder ι] [IsDirectedOrder ι] {s : Finset α}
    {f : α -> ι -> Real>=0∞} (hf : forall a, Monotone (f a)) : (∑ a in s, iSup (f a)) = ⨆ n, ∑ a in s, f a n :=
  finsetSum_iSup fun i j => (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a => ⟨hf a hi, hf a hj⟩

end Inv

end ENNReal
