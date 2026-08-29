/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Push

/-! # Embeddings of complex shapes

Given two complex shapes `c : ComplexShape ι` and `c' : ComplexShape ι'`,
an embedding from `c` to `c'` (`e : c.Embedding c'`) consists of the data
of an injective map `f : ι → ι'` such that for all `i₁ i₂ : ι`,
`c.Rel i₁ i₂` implies `c'.Rel (e.f i₁) (e.f i₂)`.
We define a type class `e.IsRelIff` to express that this implication is an equivalence.
Other type classes `e.IsTruncLE` and `e.IsTruncGE` are introduced in order to
formalize truncation functors.

This notion first appeared in the Liquid Tensor Experiment, and was developed there
mostly by Johan Commelin, Adam Topaz and Joël Riou. It shall be used in order to
relate the categories `CochainComplex C ℕ` and `ChainComplex C ℕ` to `CochainComplex C ℤ`.
It shall also be used in the construction of the canonical t-structure on the derived
category of an abelian category (TODO).

## Description of the API

- The extension functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`
  (extending by the zero object outside of the image of `e.f`) is defined in
  the file `Embedding.Extend`;
- assuming `e.IsRelIff`, the restriction functor
  `e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`
  is defined in the file `Embedding.Restriction`;
- the stupid truncation functor
  `e.stupidTruncFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  which is the composition of the two previous functors is defined in the file
  `Embedding.StupidTrunc`.
- assuming `e.IsTruncGE`, we have truncation functors
  `e.truncGE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncGEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
  (see the file `Embedding.TruncGE`), and a natural
  transformation `e.πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);
- assuming `e.IsTruncLE`, we have truncation functors
  `e.truncLE'Functor C : HomologicalComplex C c' ⥤ HomologicalComplex C c` and
  `e.truncLEFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c'`, and a natural
  transformation `e.ιTruncLENatTrans : e.truncGEFunctor C ⟶ 𝟭 _` which is a quasi-isomorphism
  in degrees in the image of `e.f` (TODO);

-/

@[expose] public section

assert_not_exists Nat.instAddMonoidWithOne Nat.instMulZeroClass

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

namespace ComplexShape

/--
Definition of `Embedding` / `Embedding` 的定义

English:
structure Embedding
  parameters: where
  axioms and operations (3):
    - f : ι -> ι'
    - injective_f : Function.Injective f
    - rel({i₁ i₂ : ι} (h : c.Rel i₁ i₂)) : c'.Rel (f i₁) (f i₂)

中文:
结构 嵌入
  参数: where
  公理与运算 (3 个):
    - f : ι -> ι'
    - injective_f : 函数.单射 f
    - rel({i₁ i₂ : ι} (h : c.关系 i₁ i₂)) : c'.关系 (f i₁) (f i₂)
-/
structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι -> ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

/-- The opposite embedding in `Embedding c.symm c'.symm` of `e : Embedding c c'`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : Embedding c.symm c'.symm where
  body: e.f
  injective_f := e.injective_f
  rel h := e.rel h

中文:
定义 op
  签名: : 嵌入 c.symm c'.symm where
  定义体: e.f
  injective_f := e.injective_f
  rel h := e.rel h
-/
def op : Embedding c.symm c'.symm where
  f := e.f
  injective_f := e.injective_f
  rel h := e.rel h

/--
Definition of `IsRelIff` / `IsRelIff` 的定义

English:
class IsRelIff
  parameters: : Prop where
  axioms and operations (1):
    - rel'((i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂))) : c.Rel i₁ i₂

中文:
类 是RelIff
  参数: : 命题 where
  公理与运算 (1 个):
    - rel'((i₁ i₂ : ι) (h : c'.关系 (e.f i₁) (e.f i₂))) : c.关系 i₁ i₂
-/
class IsRelIff : Prop where
  rel' (i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂)) : c.Rel i₁ i₂

/--
lemma `rel_iff` / 引理 `rel_iff`

English:
lemma rel_iff
  given: [e.IsRelIff] (i₁ i₂ : ι)
  statement: c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
  proof: by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

中文:
引理 rel_iff
  条件: [e.是RelIff] (i₁ i₂ : ι)
  结论: c'.关系 (e.f i₁) (e.f i₂) ↔ c.关系 i₁ i₂
  证明: by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

Depends on / 依赖: IsRelIff, IsRelIff.rel, e.rel
-/
lemma rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e.IsRelIff]
  signature: : e.op.IsRelIff where
  body: (e.rel_iff i₂ i₁).1 h

中文:
实例 [e.是RelIff]
  签名: : e.op.是RelIff where
  定义体: (e.rel_iff i₂ i₁).1 h

Depends on / 依赖: e.rel_iff, rel_iff
-/
instance [e.IsRelIff] : e.op.IsRelIff where
  rel' i₁ i₂ h := (e.rel_iff i₂ i₁).1 h

section

variable (c c')
variable (f : ι -> ι') (hf : Function.Injective f)
    (iff : forall (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂))

/-- Constructor for embeddings between complex shapes when we have an equivalence
`∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂)`. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: : Embedding c c' where
  body: f
  injective_f := hf
  rel h := (iff _ _).1 h

中文:
定义 mk'
  签名: : 嵌入 c c' where
  定义体: f
  injective_f := hf
  rel h := (iff _ _).1 h
-/
def mk' : Embedding c c' where
  f := f
  injective_f := hf
  rel h := (iff _ _).1 h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (mk' c c' f hf iff).IsRelIff
  body: (iff _ _).2 h

中文:
实例 :
  签名: (mk' c c' f hf iff).是RelIff
  定义体: (iff _ _).2 h
-/
instance : (mk' c c' f hf iff).IsRelIff where
  rel' _ _ h := (iff _ _).2 h

end

/--
Definition of `IsTruncGE` / `IsTruncGE` 的定义

English:
class IsTruncGE
  parameters: : Prop extends e.IsRelIff where
  extends: e.IsRelIff
  axioms and operations (1):
    - mem_next({j : ι} {k' : ι'} (h : c'.Rel (e.f j) k')) : exists k, e.f k = k'

中文:
类 是TruncGE
  参数: : 命题 extends e.是RelIff where
  继承: e.是RelIff
  公理与运算 (1 个):
    - mem_next({j : ι} {k' : ι'} (h : c'.关系 (e.f j) k')) : 存在 k, e.f k = k'
-/
class IsTruncGE : Prop extends e.IsRelIff where
  mem_next {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') :
    exists k, e.f k = k'

/--
lemma `mem_next` / 引理 `mem_next`

English:
lemma mem_next
  given: [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k')
  statement: exists k, e.f k = k'
  proof: IsTruncGE.mem_next h

中文:
引理 mem_next
  条件: [e.是TruncGE] {j : ι} {k' : ι'} (h : c'.关系 (e.f j) k')
  结论: 存在 k, e.f k = k'
  证明: IsTruncGE.mem_next h

Depends on / 依赖: IsTruncGE, IsTruncGE.mem_next, mem_next
-/
lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : exists k, e.f k = k' :=
  IsTruncGE.mem_next h

/--
Definition of `IsTruncLE` / `IsTruncLE` 的定义

English:
class IsTruncLE
  parameters: : Prop extends e.IsRelIff where
  extends: e.IsRelIff
  axioms and operations (1):
    - mem_prev({i' : ι'} {j : ι} (h : c'.Rel i' (e.f j))) : exists i, e.f i = i'

中文:
类 是TruncLE
  参数: : 命题 extends e.是RelIff where
  继承: e.是RelIff
  公理与运算 (1 个):
    - mem_prev({i' : ι'} {j : ι} (h : c'.关系 i' (e.f j))) : 存在 i, e.f i = i'
-/
class IsTruncLE : Prop extends e.IsRelIff where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    exists i, e.f i = i'

/--
lemma `mem_prev` / 引理 `mem_prev`

English:
lemma mem_prev
  given: [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j))
  statement: exists i, e.f i = i'
  proof: IsTruncLE.mem_prev h

中文:
引理 mem_prev
  条件: [e.是TruncLE] {i' : ι'} {j : ι} (h : c'.关系 i' (e.f j))
  结论: 存在 i, e.f i = i'
  证明: IsTruncLE.mem_prev h

Depends on / 依赖: IsTruncLE, IsTruncLE.mem_prev, mem_prev
-/
lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : exists i, e.f i = i' :=
  IsTruncLE.mem_prev h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e.IsTruncGE]
  signature: : e.op.IsTruncLE where
  body: e.mem_next h

中文:
实例 [e.是TruncGE]
  签名: : e.op.是TruncLE where
  定义体: e.mem_next h

Depends on / 依赖: e.mem_next, mem_next
-/
instance [e.IsTruncGE] : e.op.IsTruncLE where
  mem_prev h := e.mem_next h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [e.IsTruncLE]
  signature: : e.op.IsTruncGE where
  body: e.mem_prev h

中文:
实例 [e.是TruncLE]
  签名: : e.op.是TruncGE where
  定义体: e.mem_prev h

Depends on / 依赖: e.mem_prev, mem_prev
-/
instance [e.IsTruncLE] : e.op.IsTruncGE where
  mem_next h := e.mem_prev h

open scoped Classical in
/--
Definition of `r` / `r` 的定义

English:
definition r
  signature: (i' : ι')
  body: if h : exists (i : ι), e.f i = i'
  then some h.choose
  else none

中文:
定义 r
  签名: (i' : ι')
  定义体: if h : exists (i : ι), e.f i = i'
  then some h.choose
  else none

Depends on / 依赖: h.choose
-/
noncomputable def r (i' : ι') : Option ι :=
  if h : exists (i : ι), e.f i = i'
  then some h.choose
  else none

/--
lemma `r_eq_some` / 引理 `r_eq_some`

English:
lemma r_eq_some
  given: {i : ι} {i' : ι'} (hi : e.f i = i')
  proof: by
  have h : exists (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i]; rw [hi⟩]; rw [this]

中文:
引理 r_eq_some
  条件: {i : ι} {i' : ι'} (hi : e.f i = i')
  证明: by
  have h : exists (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i]; rw [hi⟩]; rw [this]

Depends on / 依赖: choose_spec, dif_pos, e.injective_f, h.choose, h.choose_spec.trans, hi.symm, injective_f
-/
lemma r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : exists (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i]; rw [hi⟩]; rw [this]

/--
lemma `r_eq_none` / 引理 `r_eq_none`

English:
lemma r_eq_none
  given: (i' : ι') (hi : forall i, e.f i != i')
  proof: dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

中文:
引理 r_eq_none
  条件: (i' : ι') (hi : 对任意 i, e.f i != i')
  证明: dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

Depends on / 依赖: dif_neg
-/
lemma r_eq_none (i' : ι') (hi : forall i, e.f i != i') :
    e.r i' = none :=
  dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')

/--
lemma `r_f` / 引理 `r_f`

English:
lemma r_f
  given: (i : ι)
  statement: e.r (e.f i) = some i
  proof: r_eq_some _ rfl

中文:
引理 r_f
  条件: (i : ι)
  结论: e.r (e.f i) = some i
  证明: r_eq_some _ rfl
-/
@[simp] lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl

/--
lemma `f_eq_of_r_eq_some` / 引理 `f_eq_of_r_eq_some`

English:
lemma f_eq_of_r_eq_some
  given: {i : ι} {i' : ι'} (hi : e.r i' = some i)
  proof: by
  by_cases h : exists (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

中文:
引理 f_eq_of_r_eq_some
  条件: {i : ι} {i' : ι'} (hi : e.r i' = some i)
  证明: by
  by_cases h : exists (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

Depends on / 依赖: e.r_eq_none, hi.symm, r_eq_none
-/
lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : exists (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [e.r_eq_none i' (by simpa using h)] at hi

end Embedding

section

variable {A : Type*} [AddCommSemigroup A] [IsRightCancelAdd A] [One A]

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `up' a` to itself via (· + b). -/
@[simps!]
/--
Definition of `embeddingUp'Add` / `embeddingUp'Add` 的定义

English:
definition embeddingUp'Add
  signature: (a b : A)
  body: Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

中文:
定义 embeddingUp'加法
  签名: (a b : A)
  定义体: Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

Depends on / 依赖: Embedding, Embedding.mk, add_right_cancel_iff, add_right_comm, implies_true, simp_rw
-/
def embeddingUp'Add (a b : A) : Embedding (up' a) (up' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

set_option backward.isDefEq.respectTransparency false in
instance (a b : A) : (embeddingUp'Add a b).IsRelIff := by dsimp [embeddingUp'Add]; infer_instance

instance (a b : A) : (embeddingUp'Add a b).IsTruncGE where
  mem_next {j _} h := ⟨j + a, (add_right_comm _ _ _).trans h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down' a` to itself via (· + b). -/
@[simps!]
/--
Definition of `embeddingDown'Add` / `embeddingDown'Add` 的定义

English:
definition embeddingDown'Add
  signature: (a b : A)
  body: Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

中文:
定义 embeddingDown'加法
  签名: (a b : A)
  定义体: Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

Depends on / 依赖: Embedding, Embedding.mk, add_right_cancel_iff, add_right_comm, implies_true, simp_rw
-/
def embeddingDown'Add (a b : A) : Embedding (down' a) (down' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

set_option backward.isDefEq.respectTransparency false in
instance (a b : A) : (embeddingDown'Add a b).IsRelIff := by
  dsimp [embeddingDown'Add]; infer_instance

instance (a b : A) : (embeddingDown'Add a b).IsTruncLE where
  mem_prev {_ x} h := ⟨x + a, (add_right_comm _ _ _).trans h⟩

end

set_option backward.defeqAttrib.useBackward true in
/-- The obvious embedding from `up ℕ` to `up ℤ`. -/
@[simps!]
/--
Definition of `embeddingUpNat` / `embeddingUpNat` 的定义

English:
definition embeddingUpNat
  signature: : Embedding (up Nat) (up Int)
  body: Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

中文:
定义 embeddingUp自然数
  签名: : 嵌入 (up 自然数) (up 整数)
  定义体: Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

Depends on / 依赖: Embedding, Embedding.mk
-/
def embeddingUpNat : Embedding (up Nat) (up Int) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingUpNat.IsRelIff
  body: by dsimp [embeddingUpNat]; infer_instance

中文:
实例 :
  签名: embeddingUp自然数.是RelIff
  定义体: by dsimp [embeddingUpNat]; infer_instance

Depends on / 依赖: embeddingUpNat, infer_instance
-/
instance : embeddingUpNat.IsRelIff := by dsimp [embeddingUpNat]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingUpNat.IsTruncGE
  body: ⟨j + 1, h⟩

中文:
实例 :
  签名: embeddingUp自然数.是TruncGE
  定义体: ⟨j + 1, h⟩
-/
instance : embeddingUpNat.IsTruncGE where
  mem_next {j _} h := ⟨j + 1, h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`. -/
@[simps!]
/--
Definition of `embeddingDownNat` / `embeddingDownNat` 的定义

English:
definition embeddingDownNat
  signature: : Embedding (down Nat) (up Int)
  body: Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

中文:
定义 embeddingDown自然数
  签名: : 嵌入 (down 自然数) (up 整数)
  定义体: Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

Depends on / 依赖: Embedding, Embedding.mk
-/
def embeddingDownNat : Embedding (down Nat) (up Int) :=
  Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingDownNat.IsRelIff
  body: by dsimp [embeddingDownNat]; infer_instance

中文:
实例 :
  签名: embeddingDown自然数.是RelIff
  定义体: by dsimp [embeddingDownNat]; infer_instance

Depends on / 依赖: embeddingDownNat, infer_instance
-/
instance : embeddingDownNat.IsRelIff := by dsimp [embeddingDownNat]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingDownNat.IsTruncLE
  body: ⟨j + 1, by dsimp at h ⊢; lia⟩

中文:
实例 :
  签名: embeddingDown自然数.是TruncLE
  定义体: ⟨j + 1, by dsimp at h ⊢; lia⟩
-/
instance : embeddingDownNat.IsTruncLE where
  mem_prev {i j} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

variable (p : Int)

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `up ℕ` to `up ℤ` which sends `n : ℕ` to `p + n`. -/
@[simps!]
/--
Definition of `embeddingUpIntGE` / `embeddingUpIntGE` 的定义

English:
definition embeddingUpIntGE
  signature: : Embedding (up Nat) (up Int)
  body: Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

中文:
定义 embeddingUp整数GE
  签名: : 嵌入 (up 自然数) (up 整数)
  定义体: Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

Depends on / 依赖: Embedding, Embedding.mk
-/
def embeddingUpIntGE : Embedding (up Nat) (up Int) :=
  Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embeddingUpIntGE p).IsRelIff
  body: by dsimp [embeddingUpIntGE]; infer_instance

中文:
实例 :
  签名: (embeddingUp整数GE p).是RelIff
  定义体: by dsimp [embeddingUpIntGE]; infer_instance

Depends on / 依赖: embeddingUpIntGE, infer_instance
-/
instance : (embeddingUpIntGE p).IsRelIff := by dsimp [embeddingUpIntGE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embeddingUpIntGE p).IsTruncGE
  body: ⟨j + 1, by dsimp at h ⊢; lia⟩

中文:
实例 :
  签名: (embeddingUp整数GE p).是TruncGE
  定义体: ⟨j + 1, by dsimp at h ⊢; lia⟩
-/
instance : (embeddingUpIntGE p).IsTruncGE where
  mem_next {j _} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` which sends `n : ℕ` to `p - n`. -/
@[simps!]
/--
Definition of `embeddingUpIntLE` / `embeddingUpIntLE` 的定义

English:
definition embeddingUpIntLE
  signature: : Embedding (down Nat) (up Int)
  body: Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

中文:
定义 embeddingUp整数LE
  签名: : 嵌入 (down 自然数) (up 整数)
  定义体: Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

Depends on / 依赖: Embedding, Embedding.mk
-/
def embeddingUpIntLE : Embedding (down Nat) (up Int) :=
  Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embeddingUpIntLE p).IsRelIff
  body: by dsimp [embeddingUpIntLE]; infer_instance

中文:
实例 :
  签名: (embeddingUp整数LE p).是RelIff
  定义体: by dsimp [embeddingUpIntLE]; infer_instance

Depends on / 依赖: embeddingUpIntLE, infer_instance
-/
instance : (embeddingUpIntLE p).IsRelIff := by dsimp [embeddingUpIntLE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (embeddingUpIntLE p).IsTruncLE
  body: ⟨k + 1, by dsimp at h ⊢; lia⟩

中文:
实例 :
  签名: (embeddingUp整数LE p).是TruncLE
  定义体: ⟨k + 1, by dsimp at h ⊢; lia⟩
-/
instance : (embeddingUpIntLE p).IsTruncLE where
  mem_prev {_ k} h := ⟨k + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `notMem_range_embeddingUpIntLE_iff` / 引理 `notMem_range_embeddingUpIntLE_iff`

English:
lemma notMem_range_embeddingUpIntLE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

中文:
引理 notMem_range_embeddingUp整数LE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

Depends on / 依赖: intros, natAbs
-/
lemma notMem_range_embeddingUpIntLE_iff (n : Int) :
    (forall (i : Nat), (embeddingUpIntLE p).f i != n) ↔ p < n := by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

set_option backward.defeqAttrib.useBackward true in
/--
lemma `notMem_range_embeddingUpIntGE_iff` / 引理 `notMem_range_embeddingUpIntGE_iff`

English:
lemma notMem_range_embeddingUpIntGE_iff
  given: (n : Int)
  proof: by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

中文:
引理 notMem_range_embeddingUp整数GE_iff
  条件: (n : 整数)
  证明: by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

Depends on / 依赖: intros, natAbs
-/
lemma notMem_range_embeddingUpIntGE_iff (n : Int) :
    (forall (i : Nat), (embeddingUpIntGE p).f i != n) ↔ n < p := by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

end ComplexShape
