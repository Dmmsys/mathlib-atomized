/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Interactions between `∑, ∏` and `(Add)Con`

-/

public section

namespace Con

/-- Multiplicative congruence relations preserve product indexed by a list. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a list. -/]
/--
theorem `list_prod` / 定理 `list_prod`

English:
theorem list_prod
  statement: {ι M : Type*} [MulOneClass M] (c : Con M) {l : List ι} {f g : ι -> M}
  proof: by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.prod_cons]
exact c.mul (h _ <| .head _) ih fun k hk => h _ (.tail _ hk)

@[to_additive (attr := simp, norm_cast)]

中文:
定理 list_prod
  结论: {ι M : 类型} [MulOneClass M] (c : Con M) {l : List ι} {f g : ι -> M}
  证明: by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.prod_cons]
exact c.mul (h _ <| .head _) ih fun k hk => h _ (.tail _ hk)

@[to_additive (attr := simp, norm_cast)]
-/
protected theorem list_prod {ι M : Type*} [MulOneClass M] (c : Con M) {l : List ι} {f g : ι -> M}
    (h : forall x in l, c (f x) (g x)) :
    c (l.map f).prod (l.map g).prod := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.prod_cons]
exact c.mul (h _ <| .head _) ih fun k hk => h _ (.tail _ hk)

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_listProd` / 定理 `coe_listProd`

English:
theorem coe_listProd
  statement: {ι M : Type*} [MulOneClass M] (c : Con M)
  proof: by
  induction l with simp [*]

中文:
定理 coe_listProd
  结论: {ι M : 类型} [MulOneClass M] (c : Con M)
  证明: by
  induction l with simp [*]
-/
protected theorem coe_listProd {ι M : Type*} [MulOneClass M] (c : Con M)
    (l : List ι) (f : ι -> M) :
    (↑(l.map f).prod : c.Quotient) = (l.map fun i => (f i : c.Quotient)).prod := by
  induction l with simp [*]

/-- Multiplicative congruence relations preserve product indexed by a multiset. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a multiset. -/]
/--
theorem `multiset_prod` / 定理 `multiset_prod`

English:
theorem multiset_prod
  statement: {ι M : Type*} [CommMonoid M] (c : Con M) {s : Multiset ι}
  proof: by
  rcases s; simpa using c.list_prod h

@[to_additive (attr := simp, norm_cast)]

中文:
定理 multiset_prod
  结论: {ι M : 类型} [CommMonoid M] (c : Con M) {s : Multiset ι}
  证明: by
  rcases s; simpa using c.list_prod h

@[to_additive (attr := simp, norm_cast)]
-/
protected theorem multiset_prod {ι M : Type*} [CommMonoid M] (c : Con M) {s : Multiset ι}
    {f g : ι -> M} (h : forall x in s, c (f x) (g x)) :
    c (s.map f).prod (s.map g).prod := by
  rcases s; simpa using c.list_prod h

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_multisetProd` / 定理 `coe_multisetProd`

English:
theorem coe_multisetProd
  statement: {ι M : Type*} [CommMonoid M] (c : Con M)
  proof: by
  simpa using map_multiset_prod c.mk' (s.map f)

中文:
定理 coe_multisetProd
  结论: {ι M : 类型} [CommMonoid M] (c : Con M)
  证明: by
  simpa using map_multiset_prod c.mk' (s.map f)
-/
protected theorem coe_multisetProd {ι M : Type*} [CommMonoid M] (c : Con M)
    (s : Multiset ι) (f : ι -> M) :
    (↑(s.map f).prod : c.Quotient) = (s.map fun i => (f i : c.Quotient)).prod := by
  simpa using map_multiset_prod c.mk' (s.map f)

/-- Multiplicative congruence relations preserve finite product. -/
@[to_additive /-- Additive congruence relations preserve finite sum. -/]
/--
theorem `finsetProd` / 定理 `finsetProd`

English:
theorem finsetProd
  statement: {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
  proof: c.multiset_prod h

@[to_additive (attr := simp, norm_cast)]

中文:
定理 finsetProd
  结论: {ι M : 类型} [CommMonoid M] (c : Con M) (s : Finset ι)
  证明: c.multiset_prod h

@[to_additive (attr := simp, norm_cast)]
-/
protected theorem finsetProd {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    {f g : ι -> M} (h : forall i in s, c (f i) (g i)) :
    c (s.prod f) (s.prod g) :=
  c.multiset_prod h

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_finsetProd` / 定理 `coe_finsetProd`

English:
theorem coe_finsetProd
  statement: {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
  proof: map_prod c.mk' f s

@[to_additive]

中文:
定理 coe_finsetProd
  结论: {ι M : 类型} [CommMonoid M] (c : Con M) (s : Finset ι)
  证明: map_prod c.mk' f s

@[to_additive]
-/
protected theorem coe_finsetProd {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    (f : ι -> M) :
    (↑(s.prod f) : c.Quotient) = s.prod fun i => (f i : c.Quotient) :=
  map_prod c.mk' f s

@[to_additive]
/--
theorem `finsuppProd` / 定理 `finsuppProd`

English:
theorem finsuppProd
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_finsuppProd]; rw [map_finsuppProd]
  classical
  exact Finsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := s

中文:
定理 finsuppProd
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_finsuppProd]; rw [map_finsuppProd]
  classical
  exact Finsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := s
-/
protected theorem finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [CommMonoid M] [Zero β]
    (c : Con M) (h : ι -> β -> M) (h' : ι -> β -> M)
    {f g : ι ->₀ β} (hf : forall i, c (h i 0) 1) (hf' : forall i, c (h' i 0) 1)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_finsuppProd]; rw [map_finsuppProd]
  classical
  exact Finsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_finsuppProd` / 定理 `coe_finsuppProd`

English:
theorem coe_finsuppProd
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: map_finsuppProd c.mk' f h

@[to_additive]

中文:
定理 coe_finsuppProd
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: map_finsuppProd c.mk' f h

@[to_additive]
-/
protected theorem coe_finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [CommMonoid M] [Zero β] (c : Con M) (h : ι -> β -> M) (f : ι ->₀ β) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  map_finsuppProd c.mk' f h

@[to_additive]
/--
theorem `dfinsuppProd` / 定理 `dfinsuppProd`

English:
theorem dfinsuppProd
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_dfinsuppProd]; rw [map_dfinsuppProd]
  exact DFinsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm

中文:
定理 dfinsuppProd
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_dfinsuppProd]; rw [map_dfinsuppProd]
  exact DFinsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm
-/
protected theorem dfinsuppProd {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [CommMonoid M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : Con M) (h : (i : ι) -> β i -> M) (h' : (i : ι) -> β i -> M)
    {f g : Π₀ i, β i} (hf : forall i, c (h i 0) 1) (hf' : forall i, c (h' i 0) 1)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  refine Quotient.exact (show c.mk' _ = c.mk' _ from ?_)
  rw [map_dfinsuppProd]; rw [map_dfinsuppProd]
  exact DFinsupp.prod_congr_of_eq_on_union
    (fun _ _ => Quotient.sound <| H _)
    (fun _ _ => Quotient.sound <| hf _) (fun _ _ => Quotient.sound <| hf' _)

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_dfinsuppProd` / 定理 `coe_dfinsuppProd`

English:
theorem coe_dfinsuppProd
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: map_dfinsuppProd c.mk' f h

中文:
定理 coe_dfinsuppProd
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: map_dfinsuppProd c.mk' f h
-/
protected theorem coe_dfinsuppProd {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [CommMonoid M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : Con M) (h : (i : ι) -> β i -> M) (f : Π₀ i, β i) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  map_dfinsuppProd c.mk' f h

/--
theorem `_root_.AddCon.dfinsuppSumAddHom` / 定理 `_root_.AddCon.dfinsuppSumAddHom`

English:
theorem _root_.AddCon.dfinsuppSumAddHom
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: by
  classical
  simp_rw [DFinsupp.sumAddHom_apply]
  exact c.dfinsuppSum _ _
    (bot_le (a := c) <| map_zero <| h ·) (bot_le (a := c) <| map_zero <| h' ·) H

@[simp, norm_cast]

中文:
定理 _root_.AddCon.dfinsuppSumAddHom
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: by
  classical
  simp_rw [DFinsupp.sumAddHom_apply]
  exact c.dfinsuppSum _ _
    (bot_le (a := c) <| map_zero <| h ·) (bot_le (a := c) <| map_zero <| h' ·) H

@[simp, norm_cast]
-/
protected theorem _root_.AddCon.dfinsuppSumAddHom {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [forall i, AddCommMonoid (β i)]
    (c : AddCon M) (h : (i : ι) -> β i ->+ M) (h' : (i : ι) -> β i ->+ M) {f g : Π₀ i, β i}
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') := by
  classical
  simp_rw [DFinsupp.sumAddHom_apply]
  exact c.dfinsuppSum _ _
    (bot_le (a := c) <| map_zero <| h ·) (bot_le (a := c) <| map_zero <| h' ·) H

@[simp, norm_cast]
/--
theorem `_root_.AddCon.coe_dfinsuppSumAddHom` / 定理 `_root_.AddCon.coe_dfinsuppSumAddHom`

English:
theorem _root_.AddCon.coe_dfinsuppSumAddHom
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: by
  classical
  simp_rw [← AddCon.coe_mk', DFinsupp.sumAddHom_apply, map_dfinsuppSum]
  rfl

@[deprecated (since := "2026-04-08")]
protected alias _root_.AddCon.finset_sum := AddCon.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := Con.finsetProd

中文:
定理 _root_.AddCon.coe_dfinsuppSumAddHom
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: by
  classical
  simp_rw [← AddCon.coe_mk', DFinsupp.sumAddHom_apply, map_dfinsuppSum]
  rfl

@[deprecated (since := "2026-04-08")]
protected alias _root_.AddCon.finset_sum := AddCon.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := Con.finsetProd
-/
protected theorem _root_.AddCon.coe_dfinsuppSumAddHom {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [forall i, AddCommMonoid (β i)]
    (c : AddCon M) (h : (i : ι) -> β i ->+ M) (f : Π₀ i, β i) :
    (↑(f.sumAddHom h) : c.Quotient) = f.sumAddHom fun i => (AddCon.mk' c).comp (h i) := by
  classical
  simp_rw [← AddCon.coe_mk', DFinsupp.sumAddHom_apply, map_dfinsuppSum]
  rfl

@[deprecated (since := "2026-04-08")]
protected alias _root_.AddCon.finset_sum := AddCon.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := Con.finsetProd

end Con
