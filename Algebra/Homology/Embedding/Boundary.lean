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

/-- The lower boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `i' : ι'` not in the image of `e.f`
such that `c'.Rel i' (e.f j)`. -/
/-
**ComplexShape.Embedding.BoundaryGE** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：BoundaryGE (j : ι) : Prop
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `i' : ι'` not in the image of `e.f`
such that `c'.Rel i' (e.f j)`.
-/
def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ ∀ i, ¬c'.Rel (e.f i) (e.f j)
/-
**ComplexShape.Embedding.boundaryGE** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : forall i, e.f
 i != i') : e.BoundaryGE j
参数：hj : c'.Rel i' (e.f j)；hi' : forall i, e.f i != i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : ∀ i, e.f i ≠ i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj, c'.prev_eq' hi]
/-
**ComplexShape.Embedding.not_boundaryGE_next** 是 Mathlib 中的一个引理，位于命名空间 `ComplexS
hape.Embedding`。
形式化陈述：not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) : ¬ e.Boundary
GE k
参数：hk : c.Rel j k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ComplexShape.Embedding.rel_iff`：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Re
l (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
-/
lemma not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩
/-
**ComplexShape.Embedding.not_boundaryGE_next'** 是 Mathlib 中的一个引理，位于命名空间 `Complex
Shape.Embedding`。
形式化陈述：not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : 
c.next j = k) : ¬ e.BoundaryGE k
参数：hj : ¬ e.BoundaryGE j；hk : c.next j = k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.not_boundaryGE_next`：not_boundaryGE_next [e.IsRel
Iff] {j k : ι} (hk : c.Rel j k) : ¬ e.BoundaryGE k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ComplexShape.next_eq_self`：next_eq_self (c : ComplexShape ι) (j : ι) (hj
 : ¬c.Rel j (c.next j)) : c.next j = j
-/
lemma not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

variable {e} in
/-
**ComplexShape.Embedding.BoundaryGE.notMem** 是 Mathlib 中的一个定理，位于命名空间 `ComplexSha
pe.Embedding.BoundaryGE`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {e : c.Embedding c'} {j : ι},   e.BoundaryGE j → ∀ {i' : ι'}, c'.Rel i' (e.f 
j) → ∀ (a : ι), e.f a ≠ i'
参数：e.f j；a : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma BoundaryGE.notMem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')
/-
**ComplexShape.Embedding.prev_f_of_not_boundaryGE** 是 Mathlib 中的一个引理，位于命名空间 `Com
plexShape.Embedding`。
形式化陈述：prev_f_of_not_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i) (hj :
 ¬ e.BoundaryGE j) : c'.prev (e.f j) = e.f i
参数：hij : c.prev j = i；hj : ¬ e.BoundaryGE j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用引理 `ComplexShape.Embedding.rel_iff`：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Re
l (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
· 使用定理 `ComplexShape.prev_eq_self`：∀ {ι : Type u_1} (c : ComplexShape ι) (j : ι)
, ¬c.Rel (c.prev j) j → c.prev j = j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
/-
**ComplexShape.Embedding.BoundaryGE.false_of_isTruncLE** 是 Mathlib 中的一个定理，位于命名空间
 `ComplexShape.Embedding.BoundaryGE`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {e : c.Embedding c'} {j : ι},   e.BoundaryGE j → ∀ [e.IsTruncLE], False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.mem_prev`：mem_prev [e.IsTruncLE] {i' : ι'} {j : ι
} (h : c'.Rel i' (e.f j)) : exists i, e.f i = i'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma BoundaryGE.false_of_isTruncLE {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

/-- The upper boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `k' : ι'` not in the image of `e.f`
such that `c'.Rel (e.f j) k'`. -/
/-
**ComplexShape.Embedding.BoundaryLE** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：BoundaryLE (j : ι) : Prop
参数：j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `k' : ι'` not in the image of `e.f`
such that `c'.Rel (e.f j) k'`.
-/
def BoundaryLE (j : ι) : Prop :=
  c'.Rel (e.f j) (c'.next (e.f j)) ∧ ∀ k, ¬c'.Rel (e.f j) (e.f k)
/-
**ComplexShape.Embedding.boundaryLE** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：boundaryLE {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : forall i, e.f
 i != k') : e.BoundaryLE j
参数：hj : c'.Rel (e.f j) k'；hk' : forall i, e.f i != k'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma boundaryLE {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : ∀ i, e.f i ≠ k') :
    e.BoundaryLE j := by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj, c'.next_eq' hk]
/-
**ComplexShape.Embedding.not_boundaryLE_prev** 是 Mathlib 中的一个引理，位于命名空间 `ComplexS
hape.Embedding`。
形式化陈述：not_boundaryLE_prev [e.IsRelIff] {i j : ι} (hi : c.Rel i j) : ¬ e.Boundary
LE i
参数：hi : c.Rel i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ComplexShape.Embedding.rel_iff`：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Re
l (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
-/
lemma not_boundaryLE_prev [e.IsRelIff] {i j : ι} (hi : c.Rel i j) :
    ¬ e.BoundaryLE i := by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩
/-
**ComplexShape.Embedding.not_boundaryLE_prev'** 是 Mathlib 中的一个引理，位于命名空间 `Complex
Shape.Embedding`。
形式化陈述：not_boundaryLE_prev' [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : 
c.prev j = i) : ¬ e.BoundaryLE i
参数：hj : ¬ e.BoundaryLE j；hk : c.prev j = i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.not_boundaryLE_prev`：not_boundaryLE_prev [e.IsRel
Iff] {i j : ι} (hi : c.Rel i j) : ¬ e.BoundaryLE i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ComplexShape.prev_eq_self`：∀ {ι : Type u_1} (c : ComplexShape ι) (j : ι)
, ¬c.Rel (c.prev j) j → c.prev j = j
-/
lemma not_boundaryLE_prev' [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i) :
    ¬ e.BoundaryLE i := by
  by_cases hij : c.Rel i j
  · exact e.not_boundaryLE_prev hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

variable {e} in
/-
**ComplexShape.Embedding.BoundaryLE.notMem** 是 Mathlib 中的一个定理，位于命名空间 `ComplexSha
pe.Embedding.BoundaryLE`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {e : c.Embedding c'} {j : ι},   e.BoundaryLE j → ∀ {k' : ι'}, c'.Rel (e.f j) 
k' → ∀ (a : ι), e.f a ≠ k'
参数：e.f j；a : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma BoundaryLE.notMem {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
    (a : ι) : e.f a ≠ k' := fun ha =>
  hj.2 a (by simpa only [ha] using hk')
/-
**ComplexShape.Embedding.next_f_of_not_boundaryLE** 是 Mathlib 中的一个引理，位于命名空间 `Com
plexShape.Embedding`。
形式化陈述：next_f_of_not_boundaryLE [e.IsRelIff] {j k : ι} (hjk : c.next j = k) (hj :
 ¬ e.BoundaryLE j) : c'.next (e.f j) = e.f k
参数：hjk : c.next j = k；hj : ¬ e.BoundaryLE j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用引理 `ComplexShape.Embedding.rel_iff`：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Re
l (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
· 使用引理 `ComplexShape.next_eq_self`：next_eq_self (c : ComplexShape ι) (j : ι) (hj
 : ¬c.Rel j (c.next j)) : c.next j = j
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
/-
**ComplexShape.Embedding.next_f** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embeddin
g`。
形式化陈述：next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.
f k
参数：hjk : c.next j = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.mem_next`：mem_next [e.IsTruncGE] {j : ι} {k' : ι'
} (h : c'.Rel (e.f j) k') : exists k, e.f k = k'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用引理 `ComplexShape.Embedding.rel_iff`：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Re
l (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
· 使用定理 `ComplexShape.Embedding.IsTruncGE.toIsRelIff`：∀ {ι : Type u_1} {ι' : Type
 u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e
.IsTruncGE],   e.IsRelIff
· 使用引理 `ComplexShape.next_eq_self`：next_eq_self (c : ComplexShape ι) (j : ι) (hj
 : ¬c.Rel j (c.next j)) : c.next j = j
-/
lemma next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.f k := by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk', e.rel_iff] at hj
    rw [← hk', ← c.next_eq' hj, hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [c'.next_eq' hj'] using hj'
/-
**ComplexShape.Embedding.prev_f** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embeddin
g`。
形式化陈述：prev_f [e.IsTruncLE] {i j : ι} (hij : c.prev j = i) : c'.prev (e.f j) = e.
f i
参数：hij : c.prev j = i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.next_f`：next_f [e.IsTruncGE] {j k : ι} (hjk : c.n
ext j = k) : c'.next (e.f j) = e.f k
· 使用定理 `ComplexShape.Embedding.instIsTruncGEOpOfIsTruncLE`：∀ {ι : Type u_1} {ι' 
: Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') [e.
IsTruncLE],   e.op.IsTruncGE
-/
lemma prev_f [e.IsTruncLE] {i j : ι} (hij : c.prev j = i) : c'.prev (e.f j) = e.f i :=
  e.op.next_f hij

variable {e} in
/-
**ComplexShape.Embedding.BoundaryLE.false_of_isTruncGE** 是 Mathlib 中的一个定理，位于命名空间
 `ComplexShape.Embedding.BoundaryLE`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} {e : c.Embedding c'} {j : ι},   e.BoundaryLE j → ∀ [e.IsTruncGE], False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.mem_next`：mem_next [e.IsTruncGE] {j : ι} {k' : ι'
} (h : c'.Rel (e.f j) k') : exists k, e.f k = k'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma BoundaryLE.false_of_isTruncGE {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE] : False := by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)
/-
**ComplexShape.Embedding.op_boundaryLE_iff** 是 Mathlib 中的一个定理，位于命名空间 `ComplexSha
pe.Embedding`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} (e : c.Embedding c') {j : ι},   e.op.BoundaryLE j ↔ e.BoundaryGE j
参数：e : c.Embedding c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma op_boundaryLE_iff {j : ι} : e.op.BoundaryLE j ↔ e.BoundaryGE j := by rfl
/-
**ComplexShape.Embedding.op_boundaryGE_iff** 是 Mathlib 中的一个定理，位于命名空间 `ComplexSha
pe.Embedding`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} (e : c.Embedding c') {j : ι},   e.op.BoundaryGE j ↔ e.BoundaryLE j
参数：e : c.Embedding c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma op_boundaryGE_iff {j : ι} : e.op.BoundaryGE j ↔ e.BoundaryLE j := by rfl

end Embedding

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.boundaryGE_embeddingUpIntGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `Comple
xShape`。
形式化陈述：boundaryGE_embeddingUpIntGE_iff (p : Int) (n : Nat) : (embeddingUpIntGE p)
.BoundaryGE n ↔ n = 0
参数：p : Int；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CochainComplex.prev`：prev (α : Type*) [AddGroup α] [One α] (i : α) : (Co
mplexShape.up α).prev i = i - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma boundaryGE_embeddingUpIntGE_iff (p : ℤ) (n : ℕ) :
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
/-
**ComplexShape.boundaryLE_embeddingUpIntLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `Comple
xShape`。
形式化陈述：boundaryLE_embeddingUpIntLE_iff (p : Int) (n : Nat) : (embeddingUpIntLE p)
.BoundaryLE n ↔ n = 0
参数：p : Int；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma boundaryLE_embeddingUpIntLE_iff (p : ℤ) (n : ℕ) :
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

