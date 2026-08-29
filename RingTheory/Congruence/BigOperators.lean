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

/--
lemma `listProd` / 引理 `listProd`

English:
lemma listProd
  statement: {ι S : Type*} [Add S] [Monoid S]
  proof: t.toCon.list_prod h

@[simp, norm_cast]

中文:
引理 listProd
  结论: {ι S : 类型} [加法 S] [幺半群 S]
  证明: t.toCon.list_prod h

@[simp, norm_cast]
-/
protected lemma listProd {ι S : Type*} [Add S] [Monoid S]
    (t : RingCon S) (l : List ι) {f g : ι -> S} (h : forall i in l, t (f i) (g i)) :
    t (l.map f).prod (l.map g).prod :=
  t.toCon.list_prod h

@[simp, norm_cast]
/--
lemma `coe_listProd` / 引理 `coe_listProd`

English:
lemma coe_listProd
  statement: {ι S : Type*} [Add S] [Monoid S] (t : RingCon S)
  proof: t.toCon.coe_listProd l f

中文:
引理 coe_listProd
  结论: {ι S : 类型} [加法 S] [幺半群 S] (t : RingCon S)
  证明: t.toCon.coe_listProd l f
-/
protected lemma coe_listProd {ι S : Type*} [Add S] [Monoid S] (t : RingCon S)
    (l : List ι) (f : ι -> S) :
    (↑(l.map f).prod : t.Quotient) = (l.map fun i => (f i : t.Quotient)).prod :=
  t.toCon.coe_listProd l f

/--
lemma `listSum` / 引理 `listSum`

English:
lemma listSum
  statement: {ι S : Type*} [AddMonoid S] [Mul S]
  proof: t.toAddCon.list_sum h

@[simp, norm_cast]

中文:
引理 listSum
  结论: {ι S : 类型} [加法幺半群 S] [乘法 S]
  证明: t.toAddCon.list_sum h

@[simp, norm_cast]
-/
protected lemma listSum {ι S : Type*} [AddMonoid S] [Mul S]
    (t : RingCon S) (l : List ι) {f g : ι -> S} (h : forall i in l, t (f i) (g i)) :
    t (l.map f).sum (l.map g).sum :=
  t.toAddCon.list_sum h

@[simp, norm_cast]
/--
lemma `coe_listSum` / 引理 `coe_listSum`

English:
lemma coe_listSum
  statement: {ι S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.coe_listSum l f

中文:
引理 coe_listSum
  结论: {ι S : 类型} [加法幺半群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.coe_listSum l f
-/
protected lemma coe_listSum {ι S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
    (l : List ι) (f : ι -> S) :
    (↑(l.map f).sum : t.Quotient) = (l.map fun i => (f i : t.Quotient)).sum :=
  t.toAddCon.coe_listSum l f

/--
lemma `multisetProd` / 引理 `multisetProd`

English:
lemma multisetProd
  statement: {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
  proof: t.toCon.multiset_prod h

@[simp, norm_cast]

中文:
引理 multisetProd
  结论: {ι S : 类型} [加法 S] [交换幺半群 S] (t : RingCon S)
  证明: t.toCon.multiset_prod h

@[simp, norm_cast]
-/
protected lemma multisetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
    (s : Multiset ι) {f g : ι -> S} (h : forall i in s, t (f i) (g i)) :
    t (s.map f).prod (s.map g).prod :=
  t.toCon.multiset_prod h

@[simp, norm_cast]
/--
lemma `coe_multisetProd` / 引理 `coe_multisetProd`

English:
lemma coe_multisetProd
  statement: {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
  proof: t.toCon.coe_multisetProd s f

中文:
引理 coe_multisetProd
  结论: {ι S : 类型} [加法 S] [交换幺半群 S] (t : RingCon S)
  证明: t.toCon.coe_multisetProd s f
-/
protected lemma coe_multisetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
    (s : Multiset ι) (f : ι -> S) :
    (↑(s.map f).prod : t.Quotient) = (s.map fun i => (f i : t.Quotient)).prod :=
  t.toCon.coe_multisetProd s f

/--
lemma `multisetSum` / 引理 `multisetSum`

English:
lemma multisetSum
  statement: {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.multiset_sum h

@[simp, norm_cast]

中文:
引理 multisetSum
  结论: {ι S : 类型} [加法交换幺半群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.multiset_sum h

@[simp, norm_cast]
-/
protected lemma multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) {f g : ι -> S} (h : forall i in s, t (f i) (g i)) :
    t (s.map f).sum (s.map g).sum :=
  t.toAddCon.multiset_sum h

@[simp, norm_cast]
/--
lemma `coe_multisetSum` / 引理 `coe_multisetSum`

English:
lemma coe_multisetSum
  statement: {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.coe_multisetSum s f

中文:
引理 coe_multisetSum
  结论: {ι S : 类型} [加法交换幺半群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.coe_multisetSum s f
-/
protected lemma coe_multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) (f : ι -> S) :
    (↑(s.map f).sum : t.Quotient) = (s.map fun i => (f i : t.Quotient)).sum :=
  t.toAddCon.coe_multisetSum s f

/--
lemma `finsetProd` / 引理 `finsetProd`

English:
lemma finsetProd
  statement: {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
  proof: t.toCon.finsetProd s h

@[simp, norm_cast]

中文:
引理 finsetProd
  结论: {ι S : 类型} [加法 S] [交换幺半群 S] (t : RingCon S) (s : 有限集 ι)
  证明: t.toCon.finsetProd s h

@[simp, norm_cast]
-/
protected lemma finsetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
    {f g : ι -> S} (h : forall i in s, t (f i) (g i)) :
    t (s.prod f) (s.prod g) :=
  t.toCon.finsetProd s h

@[simp, norm_cast]
/--
lemma `coe_finsetProd` / 引理 `coe_finsetProd`

English:
lemma coe_finsetProd
  statement: {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
  proof: t.toCon.coe_finsetProd s f

中文:
引理 coe_finsetProd
  结论: {ι S : 类型} [加法 S] [交换幺半群 S] (t : RingCon S) (s : 有限集 ι)
  证明: t.toCon.coe_finsetProd s f
-/
protected lemma coe_finsetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
    (f : ι -> S) :
    (↑(s.prod f) : t.Quotient) = s.prod fun i => (f i : t.Quotient) :=
  t.toCon.coe_finsetProd s f

/--
lemma `finsetSum` / 引理 `finsetSum`

English:
lemma finsetSum
  statement: {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
  proof: t.toAddCon.finsetSum s h

@[simp, norm_cast]

中文:
引理 finsetSum
  结论: {ι S : 类型} [加法交换幺半群 S] [乘法 S] (t : RingCon S) (s : 有限集 ι)
  证明: t.toAddCon.finsetSum s h

@[simp, norm_cast]
-/
protected lemma finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    {f g : ι -> S} (h : forall i in s, t (f i) (g i)) :
    t (s.sum f) (s.sum g) :=
  t.toAddCon.finsetSum s h

@[simp, norm_cast]
/--
lemma `coe_finsetSum` / 引理 `coe_finsetSum`

English:
lemma coe_finsetSum
  statement: {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
  proof: t.toAddCon.coe_finsetSum s f

中文:
引理 coe_finsetSum
  结论: {ι S : 类型} [加法交换幺半群 S] [乘法 S] (t : RingCon S) (s : 有限集 ι)
  证明: t.toAddCon.coe_finsetSum s f
-/
protected lemma coe_finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    (f : ι -> S) :
    (↑(s.sum f) : t.Quotient) = s.sum fun i => (f i : t.Quotient) :=
  t.toAddCon.coe_finsetSum s f

/--
lemma `finsuppProd` / 引理 `finsuppProd`

English:
lemma finsuppProd
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: c.toCon.finsuppProd h h' hf hf' H

@[simp, norm_cast]

中文:
引理 finsuppProd
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: c.toCon.finsuppProd h h' hf hf' H

@[simp, norm_cast]
-/
protected lemma finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β]
    (c : RingCon M) (h : ι -> β -> M) (h' : ι -> β -> M)
    {f g : ι ->₀ β} (hf : forall i, c (h i 0) 1) (hf' : forall i, c (h' i 0) 1)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.finsuppProd h h' hf hf' H

@[simp, norm_cast]
/--
lemma `coe_finsuppProd` / 引理 `coe_finsuppProd`

English:
lemma coe_finsuppProd
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: c.toCon.coe_finsuppProd h f

中文:
引理 coe_finsuppProd
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: c.toCon.coe_finsuppProd h f
-/
protected lemma coe_finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β] (c : RingCon M) (h : ι -> β -> M) (f : ι ->₀ β) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  c.toCon.coe_finsuppProd h f

/--
lemma `finsuppSum` / 引理 `finsuppSum`

English:
lemma finsuppSum
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: c.toAddCon.finsuppSum h h' hf hf' H

@[simp, norm_cast]

中文:
引理 finsuppSum
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: c.toAddCon.finsuppSum h h' hf hf' H

@[simp, norm_cast]
-/
protected lemma finsuppSum {ι : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] [Mul M] [Zero β]
    (c : RingCon M) (h : ι -> β -> M) (h' : ι -> β -> M)
    {f g : ι ->₀ β} (hf : forall i, c (h i 0) 0) (hf' : forall i, c (h' i 0) 0)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.finsuppSum h h' hf hf' H

@[simp, norm_cast]
/--
lemma `coe_finsuppSum` / 引理 `coe_finsuppSum`

English:
lemma coe_finsuppSum
  statement: {ι : Type*} {β : Type*} {M : Type*}
  proof: c.toAddCon.coe_finsuppSum h f

中文:
引理 coe_finsuppSum
  结论: {ι : 类型} {β : 类型} {M : 类型}
  证明: c.toAddCon.coe_finsuppSum h f
-/
protected lemma coe_finsuppSum {ι : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] [Mul M] [Zero β] (c : RingCon M) (h : ι -> β -> M) (f : ι ->₀ β) :
    (↑(f.sum h) : c.Quotient) = f.sum fun i b => (h i b : c.Quotient) :=
  c.toAddCon.coe_finsuppSum h f

/--
lemma `dfinsuppProd` / 引理 `dfinsuppProd`

English:
lemma dfinsuppProd
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toCon.dfinsuppProd h h' hf hf' H

@[simp, norm_cast]

中文:
引理 dfinsuppProd
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toCon.dfinsuppProd h h' hf hf' H

@[simp, norm_cast]
-/
protected lemma dfinsuppProd {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [Add M] [CommMonoid M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : RingCon M) (h : (i : ι) -> β i -> M) (h' : (i : ι) -> β i -> M)
    {f g : Π₀ i, β i} (hf : forall i, c (h i 0) 1) (hf' : forall i, c (h' i 0) 1)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.dfinsuppProd h h' hf hf' H

@[simp, norm_cast]
/--
lemma `coe_dfinsuppProd` / 引理 `coe_dfinsuppProd`

English:
lemma coe_dfinsuppProd
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toCon.coe_dfinsuppProd h f

中文:
引理 coe_dfinsuppProd
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toCon.coe_dfinsuppProd h f
-/
protected lemma coe_dfinsuppProd {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [Add M] [CommMonoid M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : RingCon M) (h : (i : ι) -> β i -> M) (f : Π₀ i, β i) :
    (↑(f.prod h) : c.Quotient) = f.prod fun i b => (h i b : c.Quotient) :=
  c.toCon.coe_dfinsuppProd h f

/--
lemma `dfinsuppSum` / 引理 `dfinsuppSum`

English:
lemma dfinsuppSum
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toAddCon.dfinsuppSum h h' hf hf' H

@[simp, norm_cast]

中文:
引理 dfinsuppSum
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toAddCon.dfinsuppSum h h' hf hf' H

@[simp, norm_cast]
-/
protected lemma dfinsuppSum {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : RingCon M) (h : (i : ι) -> β i -> M) (h' : (i : ι) -> β i -> M)
    {f g : Π₀ i, β i} (hf : forall i, c (h i 0) 0) (hf' : forall i, c (h' i 0) 0)
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.dfinsuppSum h h' hf hf' H

@[simp, norm_cast]
/--
lemma `coe_dfinsuppSum` / 引理 `coe_dfinsuppSum`

English:
lemma coe_dfinsuppSum
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toAddCon.coe_dfinsuppSum h f

中文:
引理 coe_dfinsuppSum
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toAddCon.coe_dfinsuppSum h f
-/
protected lemma coe_dfinsuppSum {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [forall i, Zero (β i)] [forall i (y : β i), Decidable (y != 0)]
    (c : RingCon M) (h : (i : ι) -> β i -> M) (f : Π₀ i, β i) :
    (↑(f.sum h) : c.Quotient) = f.sum fun i b => (h i b : c.Quotient) :=
  c.toAddCon.coe_dfinsuppSum h f

/--
lemma `dfinsuppSumAddHom` / 引理 `dfinsuppSumAddHom`

English:
lemma dfinsuppSumAddHom
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toAddCon.dfinsuppSumAddHom h h' H

@[simp, norm_cast]

中文:
引理 dfinsuppSumAddHom
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toAddCon.dfinsuppSumAddHom h h' H

@[simp, norm_cast]
-/
protected lemma dfinsuppSumAddHom {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [forall i, AddCommMonoid (β i)]
    (c : RingCon M) (h : (i : ι) -> β i ->+ M) (h' : (i : ι) -> β i ->+ M) {f g : Π₀ i, β i}
    (H : forall i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') :=
  c.toAddCon.dfinsuppSumAddHom h h' H

@[simp, norm_cast]
/--
lemma `coe_dfinsuppSumAddHom` / 引理 `coe_dfinsuppSumAddHom`

English:
lemma coe_dfinsuppSumAddHom
  statement: {ι : Type*} {β : ι -> Type*} {M : Type*}
  proof: c.toAddCon.coe_dfinsuppSumAddHom h f

中文:
引理 coe_dfinsuppSumAddHom
  结论: {ι : 类型} {β : ι -> 类型} {M : 类型}
  证明: c.toAddCon.coe_dfinsuppSumAddHom h f
-/
protected lemma coe_dfinsuppSumAddHom {ι : Type*} {β : ι -> Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [forall i, AddCommMonoid (β i)]
    (c : RingCon M) (h : (i : ι) -> β i ->+ M) (f : Π₀ i, β i) :
    (↑(f.sumAddHom h) : c.Quotient) = f.sumAddHom fun i => c.toAddCon.mk'.comp (h i) :=
  c.toAddCon.coe_dfinsuppSumAddHom h f

end RingCon
