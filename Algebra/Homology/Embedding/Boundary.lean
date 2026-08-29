/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Boundary of an embedding of complex shapes

In the file `Mathlib/Algebra/Homology/Embedding/Basic.lean`, given `p : ℤ`, we have defined
an embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ` in `ComplexShape.up ℤ`
which sends `n : ℕ` to `p + n`. The (canonical) truncation (`≥ p`) of
`K : CochainComplex C ℤ` shall be defined as the extension to `ℤ`
(see `Mathlib/Algebra/Homology/Embedding/Extend.lean`) of
a certain cochain complex indexed by `ℕ`:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). In this case,
we see that the degree `0 : ℕ` needs a particular attention when
constructing the truncation.

In this file, more generally, for `e : Embedding c c'`, we define
a predicate `ι → Prop` named `e.BoundaryGE` which shall be relevant
when constructing the truncation `K.truncGE e` when `e.IsTruncGE`.
In the case of `embeddingUpIntGE p`, we show that `0 : ℕ` is the
only element in this lower boundary. Similarly, we define
`Embedding.BoundaryLE`.

-/

@[expose] public section

namespace ComplexShape

namespace Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

/--
Definition of `BoundaryGE` / `BoundaryGE` 的定义

English:
definition BoundaryGE
  signature: (j : ι)
  body: c'.Rel (c'.prev (e.f j)) (e.f j) ∧ forall i, ¬c'.Rel (e.f i) (e.f j)

中文:
定义 BoundaryGE
  签名: (j : ι)
  定义体: c'.Rel (c'.prev (e.f j)) (e.f j) ∧ forall i, ¬c'.Rel (e.f i) (e.f j)
-/
def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ forall i, ¬c'.Rel (e.f i) (e.f j)

/--
lemma `boundaryGE` / 引理 `boundaryGE`

English:
lemma boundaryGE
  given: {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : forall i, e.f i != i')
  proof: by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj]; rw [c'.prev_eq' hi]

中文:
引理 boundaryGE
  条件: {i' : ι'} {j : ι} (hj : c'.关系 i' (e.f j)) (hi' : 对任意 i, e.f i != i')
  证明: by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj]; rw [c'.prev_eq' hi]

Depends on / 依赖: prev_eq
-/
lemma boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : forall i, e.f i != i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj]; rw [c'.prev_eq' hi]

/--
lemma `not_boundaryGE_next` / 引理 `not_boundaryGE_next`

English:
lemma not_boundaryGE_next
  given: [e.IsRelIff] {j k : ι} (hk : c.Rel j k)
  proof: by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

中文:
引理 not_boundaryGE_next
  条件: [e.是RelIff] {j k : ι} (hk : c.关系 j k)
  证明: by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

Depends on / 依赖: BoundaryGE, e.rel_iff, not_and, not_forall, not_not, rel_iff
-/
lemma not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

/--
lemma `not_boundaryGE_next'` / 引理 `not_boundaryGE_next'`

English:
lemma not_boundaryGE_next'
  given: [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k)
  proof: by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

中文:
引理 not_boundaryGE_next'
  条件: [e.是RelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k)
  证明: by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

Depends on / 依赖: K.isZero_X_of_isStrictlySupported, K.stupidTruncXIso, c.Rel, c.next_eq_self, e.not_boundaryGE_next, isZero_X_of_isStrictlySupported, isZero_stupidTrunc_X, next_eq_self, not_boundaryGE_next, of_iso, stupidTruncXIso
-/
lemma not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

variable {e} in
/--
lemma `BoundaryGE.notMem` / 引理 `BoundaryGE.notMem`

English:
lemma BoundaryGE.notMem
  statement: {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
  proof: fun ha =>
  hj.2 a (by simpa only [ha] using hi')

中文:
引理 BoundaryGE.notMem
  结论: {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.关系 i' (e.f j))
  证明: fun ha =>
  hj.2 a (by simpa only [ha] using hi')
-/
lemma BoundaryGE.notMem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a != i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

/--
lemma `prev_f_of_not_boundaryGE` / 引理 `prev_f_of_not_boundaryGE`

English:
lemma prev_f_of_not_boundaryGE
  statement: [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
  proof: by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at 

中文:
引理 prev_f_of_not_boundaryGE
  结论: [e.是RelIff] {i j : ι} (hij : c.prev j = i)
  证明: by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at 

Depends on / 依赖: BoundaryGE, c.Rel, c.prev_eq, c.prev_eq_self, e.rel_iff, not_and, not_forall, not_not, prev_eq, prev_eq_self, rel_iff
-/
lemma prev_f_of_not_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
    (hj : ¬ e.BoundaryGE j) :
    c'.prev (e.f j) = e.f i := by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj hj'
    rw [e.rel_iff] at hi
    rw [c.prev_eq' hi] at hij
    exact hij' (by simpa only [hij] using hi)

variable {e} in
/--
lemma `BoundaryGE.false_of_isTruncLE` / 引理 `BoundaryGE.false_of_isTruncLE`

English:
lemma BoundaryGE.false_of_isTruncLE
  given: {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE]
  statement: False
  proof: by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

中文:
引理 BoundaryGE.false_of_isTruncLE
  条件: {j : ι} (hj : e.BoundaryGE j) [e.是TruncLE]
  结论: 假
  证明: by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

Depends on / 依赖: e.mem_prev, mem_prev
-/
lemma BoundaryGE.false_of_isTruncLE {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

/--
Definition of `BoundaryLE` / `BoundaryLE` 的定义

English:
definition BoundaryLE
  signature: (j : ι)
  body: c'.Rel (e.f j) (c'.next (e.f j)) ∧ forall k, ¬c'.Rel (e.f j) (e.f k)

中文:
定义 BoundaryLE
  签名: (j : ι)
  定义体: c'.Rel (e.f j) (c'.next (e.f j)) ∧ forall k, ¬c'.Rel (e.f j) (e.f k)
-/
def BoundaryLE (j : ι) : Prop :=
  c'.Rel (e.f j) (c'.next (e.f j)) ∧ forall k, ¬c'.Rel (e.f j) (e.f k)

/--
lemma `boundaryLE` / 引理 `boundaryLE`

English:
lemma boundaryLE
  given: {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : forall i, e.f i != k')
  proof: by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj]; rw [c'.next_eq' hk]

中文:
引理 boundaryLE
  条件: {k' : ι'} {j : ι} (hj : c'.关系 (e.f j) k') (hk' : 对任意 i, e.f i != k')
  证明: by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj]; rw [c'.next_eq' hk]

Depends on / 依赖: next_eq
-/
lemma boundaryLE {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : forall i, e.f i != k') :
    e.BoundaryLE j := by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj]; rw [c'.next_eq' hk]

/--
lemma `not_boundaryLE_prev` / 引理 `not_boundaryLE_prev`

English:
lemma not_boundaryLE_prev
  given: [e.IsRelIff] {i j : ι} (hi : c.Rel i j)
  proof: by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

中文:
引理 not_boundaryLE_prev
  条件: [e.是RelIff] {i j : ι} (hi : c.关系 i j)
  证明: by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

Depends on / 依赖: BoundaryLE, e.rel_iff, not_and, not_forall, not_not, rel_iff
-/
lemma not_boundaryLE_prev [e.IsRelIff] {i j : ι} (hi : c.Rel i j) :
    ¬ e.BoundaryLE i := by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

/--
lemma `not_boundaryLE_prev'` / 引理 `not_boundaryLE_prev'`

English:
lemma not_boundaryLE_prev'
  given: [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i)
  proof: by
  by_cases hij : c.Rel i j
  · exact e.not_boundaryLE_prev hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

中文:
引理 not_boundaryLE_prev'
  条件: [e.是RelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i)
  证明: by
  by_cases hij : c.Rel i j
  · exact e.not_boundaryLE_prev hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

Depends on / 依赖: c.Rel, c.prev_eq_self, e.not_boundaryLE_prev, not_boundaryLE_prev, prev_eq_self
-/
lemma not_boundaryLE_prev' [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i) :
    ¬ e.BoundaryLE i := by
  by_cases hij : c.Rel i j
  · exact e.not_boundaryLE_prev hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

variable {e} in
/--
lemma `BoundaryLE.notMem` / 引理 `BoundaryLE.notMem`

English:
lemma BoundaryLE.notMem
  statement: {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
  proof: fun ha =>
  hj.2 a (by simpa only [ha] using hk')

中文:
引理 BoundaryLE.notMem
  结论: {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.关系 (e.f j) k')
  证明: fun ha =>
  hj.2 a (by simpa only [ha] using hk')
-/
lemma BoundaryLE.notMem {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
    (a : ι) : e.f a != k' := fun ha =>
  hj.2 a (by simpa only [ha] using hk')

/--
lemma `next_f_of_not_boundaryLE` / 引理 `next_f_of_not_boundaryLE`

English:
lemma next_f_of_not_boundaryLE
  statement: [e.IsRelIff] {j k : ι} (hjk : c.next j = k)
  proof: by
  by_cases hjk' : c.Rel j k
  · exact c'.next_eq' (by simpa only [e.rel_iff] using hjk')
  · obtain rfl : j = k := by
      simpa only [c.next_eq_self j (by simpa only [hjk] using hjk')] using hjk
    apply c'.next_eq_self
    intro hj'
    simp only [BoundaryLE, not_and, not_forall, not_not] at 

中文:
引理 next_f_of_not_boundaryLE
  结论: [e.是RelIff] {j k : ι} (hjk : c.next j = k)
  证明: by
  by_cases hjk' : c.Rel j k
  · exact c'.next_eq' (by simpa only [e.rel_iff] using hjk')
  · obtain rfl : j = k := by
      simpa only [c.next_eq_self j (by simpa only [hjk] using hjk')] using hjk
    apply c'.next_eq_self
    intro hj'
    simp only [BoundaryLE, not_and, not_forall, not_not] at 

Depends on / 依赖: BoundaryLE, c.Rel, c.next_eq, c.next_eq_self, e.rel_iff, next_eq, next_eq_self, not_and, not_forall, not_not, rel_iff
-/
lemma next_f_of_not_boundaryLE [e.IsRelIff] {j k : ι} (hjk : c.next j = k)
    (hj : ¬ e.BoundaryLE j) :
    c'.next (e.f j) = e.f k := by
  by_cases hjk' : c.Rel j k
  · exact c'.next_eq' (by simpa only [e.rel_iff] using hjk')
  · obtain rfl : j = k := by
      simpa only [c.next_eq_self j (by simpa only [hjk] using hjk')] using hjk
    apply c'.next_eq_self
    intro hj'
    simp only [BoundaryLE, not_and, not_forall, not_not] at hj
    obtain ⟨k, hk⟩ := hj hj'
    rw [e.rel_iff] at hk
    rw [c.next_eq' hk] at hjk
    exact hjk' (by simpa only [hjk] using hk)

/--
lemma `next_f` / 引理 `next_f`

English:
lemma next_f
  given: [e.IsTruncGE] {j k : ι} (hjk : c.next j = k)
  statement: c'.next (e.f j) = e.f k
  proof: by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk']; rw [e.rel_iff] at hj
    rw [← hk']; rw [← c.next_eq' hj]; rw [hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [

中文:
引理 next_f
  条件: [e.是TruncGE] {j k : ι} (hjk : c.next j = k)
  结论: c'.next (e.f j) = e.f k
  证明: by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk']; rw [e.rel_iff] at hj
    rw [← hk']; rw [← c.next_eq' hj]; rw [hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [

Depends on / 依赖: c.next_eq, c.next_eq_self, e.mem_next, e.rel_iff, mem_next, next_eq, next_eq_self, rel_iff
-/
lemma next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.f k := by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk']; rw [e.rel_iff] at hj
    rw [← hk']; rw [← c.next_eq' hj]; rw [hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [c'.next_eq' hj'] using hj'

/--
lemma `prev_f` / 引理 `prev_f`

English:
lemma prev_f
  given: [e.IsTruncLE] {i j : ι} (hij : c.prev j = i)
  statement: c'.prev (e.f j) = e.f i
  proof: e.op.next_f hij

中文:
引理 prev_f
  条件: [e.是TruncLE] {i j : ι} (hij : c.prev j = i)
  结论: c'.prev (e.f j) = e.f i
  证明: e.op.next_f hij

Depends on / 依赖: e.op.next_f, next_f
-/
lemma prev_f [e.IsTruncLE] {i j : ι} (hij : c.prev j = i) : c'.prev (e.f j) = e.f i :=
  e.op.next_f hij

variable {e} in
/--
lemma `BoundaryLE.false_of_isTruncGE` / 引理 `BoundaryLE.false_of_isTruncGE`

English:
lemma BoundaryLE.false_of_isTruncGE
  given: {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE]
  statement: False
  proof: by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)

中文:
引理 BoundaryLE.false_of_isTruncGE
  条件: {j : ι} (hj : e.BoundaryLE j) [e.是TruncGE]
  结论: 假
  证明: by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)

Depends on / 依赖: e.mem_next, mem_next
-/
lemma BoundaryLE.false_of_isTruncGE {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE] : False := by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)

/--
lemma `op_boundaryLE_iff` / 引理 `op_boundaryLE_iff`

English:
lemma op_boundaryLE_iff
  given: {j : ι}
  statement: e.op.BoundaryLE j ↔ e.BoundaryGE j
  proof: by rfl

中文:
引理 op_boundaryLE_iff
  条件: {j : ι}
  结论: e.op.BoundaryLE j ↔ e.BoundaryGE j
  证明: by rfl

Depends on / 依赖: eqToIso, truncGE
-/
@[simp] lemma op_boundaryLE_iff {j : ι} : e.op.BoundaryLE j ↔ e.BoundaryGE j := by rfl
/--
lemma `op_boundaryGE_iff` / 引理 `op_boundaryGE_iff`

English:
lemma op_boundaryGE_iff
  given: {j : ι}
  statement: e.op.BoundaryGE j ↔ e.BoundaryLE j
  proof: by rfl

中文:
引理 op_boundaryGE_iff
  条件: {j : ι}
  结论: e.op.BoundaryGE j ↔ e.BoundaryLE j
  证明: by rfl

Depends on / 依赖: XIsoOpcycles, eqToIso, truncGE
-/
@[simp] lemma op_boundaryGE_iff {j : ι} : e.op.BoundaryGE j ↔ e.BoundaryLE j := by rfl

end Embedding

set_option backward.defeqAttrib.useBackward true in
/--
lemma `boundaryGE_embeddingUpIntGE_iff` / 引理 `boundaryGE_embeddingUpIntGE_iff`

English:
lemma boundaryGE_embeddingUpIntGE_iff
  given: (p : Int) (n : Nat)
  proof: by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

中文:
引理 boundaryGE_embeddingUp整数GE_iff
  条件: (p : 整数) (n : 自然数)
  证明: by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

Depends on / 依赖: dif_neg, dif_pos, truncGE
-/
lemma boundaryGE_embeddingUpIntGE_iff (p : Int) (n : Nat) :
    (embeddingUpIntGE p).BoundaryGE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

set_option backward.defeqAttrib.useBackward true in
/--
lemma `boundaryLE_embeddingUpIntLE_iff` / 引理 `boundaryLE_embeddingUpIntLE_iff`

English:
lemma boundaryLE_embeddingUpIntLE_iff
  given: (p : Int) (n : Nat)
  proof: by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

中文:
引理 boundaryLE_embeddingUp整数LE_iff
  条件: (p : 整数) (n : 自然数)
  证明: by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

Depends on / 依赖: XIsoOpcycles, dif_pos, truncGE
-/
lemma boundaryLE_embeddingUpIntLE_iff (p : Int) (n : Nat) :
    (embeddingUpIntLE p).BoundaryLE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

end ComplexShape
