/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.Congruence.BigOperators
public import Mathlib.RingTheory.Congruence.Defs

/-!
# Interactions between `∑, ∏` and `RingCon`

TODO: some of the typeclass assumptions in this file can be weakened if more instances are added
for `RingCon.Quotient`.
-/

public section

namespace RingCon

/-- Congruence relation of a ring preserves finite product indexed by a list. -/
/-
**RingCon.listProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : Monoid S] (t : Ri
ngCon S) (l : List ι) {f g : ι → S},   (∀ i ∈ l, t (f i) (g i)) → t (List.map f 
l).prod (List.map g l).prod
参数：t : RingCon S；l : List ι；∀ i ∈ l, t (f i) (g i)；List.map f l；List.map g l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.list_prod`：∀ {ι : Type u_1} {M : Type u_2} [inst : MulOneClass M] (c
 : Con M) {l : List ι} {f g : ι → M},   (∀ x ∈ l, c (f x) (g x)) → c (List.map f
 l)…

--- 原说明 ---
Congruence relation of a ring preserves finite product indexed by a list.
-/
protected lemma listProd {ι S : Type*} [Add S] [Monoid S]
    (t : RingCon S) (l : List ι) {f g : ι → S} (h : ∀ i ∈ l, t (f i) (g i)) :
    t (l.map f).prod (l.map g).prod :=
  t.toCon.list_prod h

@[simp, norm_cast]
/-
**RingCon.coe_listProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : Monoid S] (t : Ri
ngCon S) (l : List ι) (f : ι → S),   ↑(List.map f l).prod = (List.map (fun i => 
↑(f i)) l).prod
参数：t : RingCon S；l : List ι；f : ι → S；List.map f l；List.map (fun i => ↑(f i)) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.coe_listProd`：∀ {ι : Type u_1} {M : Type u_2} [inst : MulOneClass M]
 (c : Con M) (l : List ι) (f : ι → M),   ↑(List.map f l).prod = (List.map (fun i
 => ↑(…
-/
protected lemma coe_listProd {ι S : Type*} [Add S] [Monoid S] (t : RingCon S)
    (l : List ι) (f : ι → S) :
    (↑(l.map f).prod : t.Quotient) = (l.map fun i => (f i : t.Quotient)).prod :=
  t.toCon.coe_listProd l f

/-- Congruence relation of a ring preserves finite sum indexed by a list. -/
/-
**RingCon.listSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddMonoid S] [inst_1 : Mul S] (t :
 RingCon S) (l : List ι) {f g : ι → S},   (∀ i ∈ l, t (f i) (g i)) → t (List.map
 f l).sum (List.map g l).sum
参数：t : RingCon S；l : List ι；∀ i ∈ l, t (f i) (g i)；List.map f l；List.map g l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.list_sum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddZeroClass M]
 (c : AddCon M) {l : List ι} {f g : ι → M},   (∀ x ∈ l, c (f x) (g x)) → c (List
.map …

--- 原说明 ---
Congruence relation of a ring preserves finite sum indexed by a list.
-/
protected lemma listSum {ι S : Type*} [AddMonoid S] [Mul S]
    (t : RingCon S) (l : List ι) {f g : ι → S} (h : ∀ i ∈ l, t (f i) (g i)) :
    t (l.map f).sum (l.map g).sum :=
  t.toAddCon.list_sum h

@[simp, norm_cast]
/-
**RingCon.coe_listSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddMonoid S] [inst_1 : Mul S] (t :
 RingCon S) (l : List ι) (f : ι → S),   ↑(List.map f l).sum = (List.map (fun i =
> ↑(f i)) l).sum
参数：t : RingCon S；l : List ι；f : ι → S；List.map f l；List.map (fun i => ↑(f i)) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_listSum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddZeroClass
 M] (c : AddCon M) (l : List ι) (f : ι → M),   ↑(List.map f l).sum = (List.map (
fun i =>…
-/
protected lemma coe_listSum {ι S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
    (l : List ι) (f : ι → S) :
    (↑(l.map f).sum : t.Quotient) = (l.map fun i => (f i : t.Quotient)).sum :=
  t.toAddCon.coe_listSum l f

/-- Congruence relation of a ring preserves finite product indexed by a multiset. -/
/-
**RingCon.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : CommMonoid S] (t 
: RingCon S) (s : Multiset ι) {f g : ι → S},   (∀ i ∈ s, t (f i) (g i)) → t (Mul
tiset.map f s).prod (Multiset.map g s).prod
参数：t : RingCon S；s : Multiset ι；∀ i ∈ s, t (f i) (g i)；Multiset.map f s；Multiset
.map g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.multiset_prod`：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M]
 (c : Con M) {s : Multiset ι} {f g : ι → M},   (∀ x ∈ s, c (f x) (g x)) → c (Mul
tiset.m…

--- 原说明 ---
Congruence relation of a ring preserves finite product indexed by a multiset.
-/
protected lemma multisetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
    (s : Multiset ι) {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.map f).prod (s.map g).prod :=
  t.toCon.multiset_prod h

@[simp, norm_cast]
/-
**RingCon.coe_multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : CommMonoid S] (t 
: RingCon S) (s : Multiset ι) (f : ι → S),   ↑(Multiset.map f s).prod = (Multise
t.map (fun i => ↑(f i)) s).prod
参数：t : RingCon S；s : Multiset ι；f : ι → S；Multiset.map f s；Multiset.map (fun i =
> ↑(f i)) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.coe_multisetProd`：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid
 M] (c : Con M) (s : Multiset ι) (f : ι → M),   ↑(Multiset.map f s).prod = (Mult
iset.map (…
-/
protected lemma coe_multisetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
    (s : Multiset ι) (f : ι → S) :
    (↑(s.map f).prod : t.Quotient) = (s.map fun i => (f i : t.Quotient)).prod :=
  t.toCon.coe_multisetProd s f

/-- Congruence relation of a ring preserves finite sum indexed by a multiset. -/
/-
**RingCon.multisetSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMonoid S] [inst_1 : Mul S] 
(t : RingCon S) (s : Multiset ι)   {f g : ι → S}, (∀ i ∈ s, t (f i) (g i)) → t (
Multiset.map f s).sum (Multiset.map g s).sum
参数：t : RingCon S；s : Multiset ι；∀ i ∈ s, t (f i) (g i)；Multiset.map f s；Multiset
.map g s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.multiset_sum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMono
id M] (c : AddCon M) {s : Multiset ι} {f g : ι → M},   (∀ x ∈ s, c (f x) (g x)) 
→ c (Mult…

--- 原说明 ---
Congruence relation of a ring preserves finite sum indexed by a multiset.
-/
protected lemma multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.map f).sum (s.map g).sum :=
  t.toAddCon.multiset_sum h

@[simp, norm_cast]
/-
**RingCon.coe_multisetSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMonoid S] [inst_1 : Mul S] 
(t : RingCon S) (s : Multiset ι) (f : ι → S),   ↑(Multiset.map f s).sum = (Multi
set.map (fun i => ↑(f i)) s).sum
参数：t : RingCon S；s : Multiset ι；f : ι → S；Multiset.map f s；Multiset.map (fun i =
> ↑(f i)) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_multisetSum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommM
onoid M] (c : AddCon M) (s : Multiset ι) (f : ι → M),   ↑(Multiset.map f s).sum 
= (Multiset.…
-/
protected lemma coe_multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) (f : ι → S) :
    (↑(s.map f).sum : t.Quotient) = (s.map fun i => (f i : t.Quotient)).sum :=
  t.toAddCon.coe_multisetSum s f

/-- Congruence relation of a ring preserves finite product. -/
/-
**RingCon.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : CommMonoid S] (t 
: RingCon S) (s : Finset ι) {f g : ι → S},   (∀ i ∈ s, t (f i) (g i)) → t (s.pro
d f) (s.prod g)
参数：t : RingCon S；s : Finset ι；∀ i ∈ s, t (f i) (g i)；s.prod f；s.prod g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.finsetProd`：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M] (c
 : Con M) (s : Finset ι) {f g : ι → M},   (∀ i ∈ s, c (f i) (g i)) → c (s.prod f
) (s…

--- 原说明 ---
Congruence relation of a ring preserves finite product.
-/
protected lemma finsetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
    {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.prod f) (s.prod g) :=
  t.toCon.finsetProd s h

@[simp, norm_cast]
/-
**RingCon.coe_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : Add S] [inst_1 : CommMonoid S] (t 
: RingCon S) (s : Finset ι) (f : ι → S),   ↑(s.prod f) = ∏ i ∈ s, ↑(f i)
参数：t : RingCon S；s : Finset ι；f : ι → S；s.prod f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.coe_finsetProd`：∀ {ι : Type u_1} {M : Type u_2} [inst : CommMonoid M
] (c : Con M) (s : Finset ι) (f : ι → M),   ↑(s.prod f) = ∏ i ∈ s, ↑(f i)
-/
protected lemma coe_finsetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
    (f : ι → S) :
    (↑(s.prod f) : t.Quotient) = s.prod fun i => (f i : t.Quotient) :=
  t.toCon.coe_finsetProd s f

/-- Congruence relation of a ring preserves finite sum. -/
/-
**RingCon.finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMonoid S] [inst_1 : Mul S] 
(t : RingCon S) (s : Finset ι) {f g : ι → S},   (∀ i ∈ s, t (f i) (g i)) → t (s.
sum f) (s.sum g)
参数：t : RingCon S；s : Finset ι；∀ i ∈ s, t (f i) (g i)；s.sum f；s.sum g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.finsetSum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid 
M] (c : AddCon M) (s : Finset ι) {f g : ι → M},   (∀ i ∈ s, c (f i) (g i)) → c (
s.sum …

--- 原说明 ---
Congruence relation of a ring preserves finite sum.
-/
protected lemma finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.sum f) (s.sum g) :=
  t.toAddCon.finsetSum s h

@[simp, norm_cast]
/-
**RingCon.coe_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMonoid S] [inst_1 : Mul S] 
(t : RingCon S) (s : Finset ι) (f : ι → S),   ↑(s.sum f) = ∑ i ∈ s, ↑(f i)
参数：t : RingCon S；s : Finset ι；f : ι → S；s.sum f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_finsetSum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMon
oid M] (c : AddCon M) (s : Finset ι) (f : ι → M),   ↑(s.sum f) = ∑ i ∈ s, ↑(f i)
-/
protected lemma coe_finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    (f : ι → S) :
    (↑(s.sum f) : t.Quotient) = s.sum fun i => (f i : t.Quotient) :=
  t.toAddCon.coe_finsetSum s f
/-
**RingCon.finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : Add M] [inst_1 : Co
mmMonoid M] [inst_2 : Zero β] (c : RingCon M)   (h h' : ι → β → M) {f g : ι →₀ β
},   (∀ (i : ι), c (h i 0) 1) →     (∀ (i : ι), c (h' i 0) 1) → (∀ (i : ι), c (h
 i (f i)) (h' i (g i))) → c (f.prod h) (g.prod h')
参数：c : RingCon M；h h' : ι → β → M；∀ (i : ι), c (h i 0) 1；∀ (i : ι), c (h' i 0) 1
；∀ (i : ι), c (h i (f i)) (h' i (g i))；f.prod h；g.prod h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.finsuppProd`：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : 
CommMonoid M] [inst_1 : Zero β] (c : Con M) (h h' : ι → β → M)   {f g : ι →₀ β},
   (∀…
-/
protected lemma finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β]
    (c : RingCon M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, c (h i 0) 1) (hf' : ∀ i, c (h' i 0) 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.finsuppProd h h' hf hf' H

@[simp, norm_cast]
/-
**RingCon.coe_finsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : Add M] [inst_1 : Co
mmMonoid M] [inst_2 : Zero β] (c : RingCon M)   (h : ι → β → M) (f : ι →₀ β), ↑(
f.prod h) = f.prod fun i b => ↑(h i b)
参数：c : RingCon M；h : ι → β → M；f : ι →₀ β；f.prod h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.coe_finsuppProd`：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [ins
t : CommMonoid M] [inst_1 : Zero β] (c : Con M) (h : ι → β → M)   (f : ι →₀ β), 
↑(f.prod …
-/
protected lemma coe_finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β] (c : RingCon M) (h : ι → β → M) (f : ι →₀ β) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  c.toCon.coe_finsuppProd h f
/-
**RingCon.finsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [i
nst_1 : Mul M] [inst_2 : Zero β]   (c : RingCon M) (h h' : ι → β → M) {f g : ι →
₀ β},   (∀ (i : ι), c (h i 0) 0) →     (∀ (i : ι), c (h' i 0) 0) → (∀ (i : ι), c
 (h i (f i)) (h' i (g i))) → c (f.sum h) (g.sum h')
参数：c : RingCon M；h h' : ι → β → M；∀ (i : ι), c (h i 0) 0；∀ (i : ι), c (h' i 0) 0
；∀ (i : ι), c (h i (f i)) (h' i (g i))；f.sum h；g.sum h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.finsuppSum`：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst 
: AddCommMonoid M] [inst_1 : Zero β] (c : AddCon M)   (h h' : ι → β → M) {f g : 
ι →₀ β}…
-/
protected lemma finsuppSum {ι : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] [Mul M] [Zero β]
    (c : RingCon M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, c (h i 0) 0) (hf' : ∀ i, c (h' i 0) 0)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.finsuppSum h h' hf hf' H

@[simp, norm_cast]
/-
**RingCon.coe_finsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [inst : AddCommMonoid M] [i
nst_1 : Mul M] [inst_2 : Zero β]   (c : RingCon M) (h : ι → β → M) (f : ι →₀ β),
 ↑(f.sum h) = f.sum fun i b => ↑(h i b)
参数：c : RingCon M；h : ι → β → M；f : ι →₀ β；f.sum h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_finsuppSum`：∀ {ι : Type u_1} {β : Type u_2} {M : Type u_3} [i
nst : AddCommMonoid M] [inst_1 : Zero β] (c : AddCon M) (h : ι → β → M)   (f : ι
 →₀ β), ↑(f…
-/
protected lemma coe_finsuppSum {ι : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] [Mul M] [Zero β] (c : RingCon M) (h : ι → β → M) (f : ι →₀ β) :
    (↑(f.sum h) : c.Quotient) = f.sum fun i b => (h i b : c.Quotient) :=
  c.toAddCon.coe_finsuppSum h f
/-
**RingCon.dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : Add M] [inst_2 : CommMonoid M]   [inst_3 : (i : ι) → Zero (β i)] [inst
_4 : (i : ι) → (y : β i) → Decidable (y ≠ 0)] (c : RingCon M)   (h h' : (i : ι) 
→ β i → M) {f g : Π₀ (i : ι), β i},   (∀ (i : ι), c (h i 0) 1) →     (∀ (i : ι),
 c (h' i 0) 1) → (∀ (i : ι), c (h i (f i)) (h' i (g i))) → c (f.prod h) (g.prod 
h')
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : RingCon M；h h' : (i : ι) → β i → M；i : ι；∀ 
(i : ι), c (h i 0) 1；∀ (i : ι), c (h' i 0) 1；∀ (i : ι), c (h i (f i)) (h' i (g i
))；f.prod h；g.prod h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.dfinsuppProd`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [in
st : DecidableEq ι] [inst_1 : CommMonoid M]   [inst_2 : (i : ι) → Zero (β i)] [i
nst_3 …
-/
protected lemma dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [Add M] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, c (h i 0) 1) (hf' : ∀ i, c (h' i 0) 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.dfinsuppProd h h' hf hf' H

@[simp, norm_cast]
/-
**RingCon.coe_dfinsuppProd** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : Add M] [inst_2 : CommMonoid M]   [inst_3 : (i : ι) → Zero (β i)] [inst
_4 : (i : ι) → (y : β i) → Decidable (y ≠ 0)] (c : RingCon M)   (h : (i : ι) → β
 i → M) (f : Π₀ (i : ι), β i), ↑(f.prod h) = f.prod fun i b => ↑(h i b)
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : RingCon M；h : (i : ι) → β i → M；f : Π₀ (i :
 ι), β i；f.prod h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.coe_dfinsuppProd`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3}
 [inst : DecidableEq ι] [inst_1 : CommMonoid M]   [inst_2 : (i : ι) → Zero (β i)
] [inst_3 …
-/
protected lemma coe_dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [Add M] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (f : Π₀ i, β i) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  c.toCon.coe_dfinsuppProd h f
/-
**RingCon.dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : AddCommMonoid M] [inst_2 : Mul M]   [inst_3 : (i : ι) → Zero (β i)] [i
nst_4 : (i : ι) → (y : β i) → Decidable (y ≠ 0)] (c : RingCon M)   (h h' : (i : 
ι) → β i → M) {f g : Π₀ (i : ι), β i},   (∀ (i : ι), c (h i 0) 0) →     (∀ (i : 
ι), c (h' i 0) 0) → (∀ (i : ι), c (h i (f i)) (h' i (g i))) → c (f.sum h) (g.sum
 h')
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : RingCon M；h h' : (i : ι) → β i → M；i : ι；∀ 
(i : ι), c (h i 0) 0；∀ (i : ι), c (h' i 0) 0；∀ (i : ι), c (h i (f i)) (h' i (g i
))；f.sum h；g.sum h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.dfinsuppSum`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [
inst : DecidableEq ι] [inst_1 : AddCommMonoid M]   [inst_2 : (i : ι) → Zero (β i
)] [inst…
-/
protected lemma dfinsuppSum {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, c (h i 0) 0) (hf' : ∀ i, c (h' i 0) 0)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.dfinsuppSum h h' hf hf' H

@[simp, norm_cast]
/-
**RingCon.coe_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : AddCommMonoid M] [inst_2 : Mul M]   [inst_3 : (i : ι) → Zero (β i)] [i
nst_4 : (i : ι) → (y : β i) → Decidable (y ≠ 0)] (c : RingCon M)   (h : (i : ι) 
→ β i → M) (f : Π₀ (i : ι), β i), ↑(f.sum h) = f.sum fun i b => ↑(h i b)
参数：i : ι；β i；i : ι；y : β i；y ≠ 0；c : RingCon M；h : (i : ι) → β i → M；f : Π₀ (i :
 ι), β i；f.sum h；h i b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_dfinsuppSum`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_
3} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M]   [inst_2 : (i : ι) → Zero 
(β i)] [inst…
-/
protected lemma coe_dfinsuppSum {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (f : Π₀ i, β i) :
    (↑(f.sum h) : c.Quotient) = f.sum fun i b => (h i b : c.Quotient) :=
  c.toAddCon.coe_dfinsuppSum h f
/-
**RingCon.dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : AddCommMonoid M] [inst_2 : Mul M]   [inst_3 : (i : ι) → AddCommMonoid 
(β i)] (c : RingCon M) (h h' : (i : ι) → β i →+ M) {f g : Π₀ (i : ι), β i},   (∀
 (i : ι), c ((h i) (f i)) ((h' i) (g i))) → c ((DFinsupp.sumAddHom h) f) ((DFins
upp.sumAddHom h') g)
参数：i : ι；β i；c : RingCon M；h h' : (i : ι) → β i →+ M；i : ι；∀ (i : ι), c ((h i) (
f i)) ((h' i) (g i))；(DFinsupp.sumAddHom h) f；(DFinsupp.sumAddHom h') g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.dfinsuppSumAddHom`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type 
u_3} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M]   [inst_2 : (i : ι) → Add
CommMonoid (β …
-/
protected lemma dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, AddCommMonoid (β i)]
    (c : RingCon M) (h : (i : ι) → β i →+ M) (h' : (i : ι) → β i →+ M) {f g : Π₀ i, β i}
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') :=
  c.toAddCon.dfinsuppSumAddHom h h' H

@[simp, norm_cast]
/-
**RingCon.coe_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} {M : Type u_3} [inst : DecidableEq ι] 
[inst_1 : AddCommMonoid M] [inst_2 : Mul M]   [inst_3 : (i : ι) → AddCommMonoid 
(β i)] (c : RingCon M) (h : (i : ι) → β i →+ M) (f : Π₀ (i : ι), β i),   ↑((DFin
supp.sumAddHom h) f) = (DFinsupp.sumAddHom fun i => c.toAddCon.mk'.comp (h i)) f
参数：i : ι；β i；c : RingCon M；h : (i : ι) → β i →+ M；f : Π₀ (i : ι), β i；(DFinsupp.
sumAddHom h) f；DFinsupp.sumAddHom fun i => c.toAddCon.mk'.comp (h i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.coe_dfinsuppSumAddHom`：∀ {ι : Type u_1} {β : ι → Type u_2} {M : T
ype u_3} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M]   [inst_2 : (i : ι) →
 AddCommMonoid (β …
-/
protected lemma coe_dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, AddCommMonoid (β i)]
    (c : RingCon M) (h : (i : ι) → β i →+ M) (f : Π₀ i, β i) :
    (↑(f.sumAddHom h) : c.Quotient) = f.sumAddHom fun i => c.toAddCon.mk'.comp (h i) :=
  c.toAddCon.coe_dfinsuppSumAddHom h f

end RingCon

