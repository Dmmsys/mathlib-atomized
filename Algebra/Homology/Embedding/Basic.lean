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

/-- An embedding of a complex shape `c : ComplexShape ι` into a complex shape
`c' : ComplexShape ι'` consists of an injective map `f : ι → ι'` which satisfies
a compatibility with respect to the relations `c.Rel` and `c'.Rel`. -/
/-
**ComplexShape.Embedding** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape`。
形式化陈述：{ι : Type u_1} → {ι' : Type u_2} → ComplexShape ι → ComplexShape ι' → Type
 (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of a complex shape `c : ComplexShape ι` into a complex shape
`c' : ComplexShape ι'` consists of an injective map `f : ι → ι'` which satisfies
a compatibility with respect to the relations `c.Rel` and `c'.Rel`.
-/
structure Embedding where
  /-- the map between the underlying types of indices -/
  f : ι → ι'
  injective_f : Function.Injective f
  rel {i₁ i₂ : ι} (h : c.Rel i₁ i₂) : c'.Rel (f i₁) (f i₂)

namespace Embedding

variable {c c'}
variable (e : Embedding c c')

/-- The opposite embedding in `Embedding c.symm c'.symm` of `e : Embedding c c'`. -/
@[simps]
/-
**ComplexShape.Embedding.op** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedding`。
形式化陈述：op : Embedding c.symm c'.symm where f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…

--- 原说明 ---
The opposite embedding in `Embedding c.symm c'.symm` of `e : Embedding c c'`.
-/
def op : Embedding c.symm c'.symm where
  f := e.f
  injective_f := e.injective_f
  rel h := e.rel h

/-- An embedding of complex shapes `e` satisfies `e.IsRelIff` if the implication
`e.rel` is an equivalence. -/
/-
**ComplexShape.Embedding.IsRelIff** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape.Embe
dding`。
形式化陈述：{ι : Type u_1} → {ι' : Type u_2} → {c : ComplexShape ι} → {c' : ComplexSha
pe ι'} → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of complex shapes `e` satisfies `e.IsRelIff` if the implication
`e.rel` is an equivalence.
-/
class IsRelIff : Prop where
  rel' (i₁ i₂ : ι) (h : c'.Rel (e.f i₁) (e.f i₂)) : c.Rel i₁ i₂
/-
**ComplexShape.Embedding.rel_iff** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embeddi
ng`。
形式化陈述：rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂
参数：i₁ i₂ : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsRelIff.rel'`：∀ {ι : Type u_1} {ι' : Type u_2} {
c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e.IsRelI
ff]   (i₁ i₂ : ι), c'.Rel …
· 使用定理 `ComplexShape.Embedding.rel`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (self : c.Embedding c') {i₁ i₂ : ι},   c.Rel i₁
 i₂ → c'.Rel (se…
-/
lemma rel_iff [e.IsRelIff] (i₁ i₂ : ι) : c'.Rel (e.f i₁) (e.f i₂) ↔ c.Rel i₁ i₂ := by
  constructor
  · apply IsRelIff.rel'
  · exact e.rel
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e.IsRelIff] : e.op.IsRelIff where
  rel' i₁ i₂ h := (e.rel_iff i₂ i₁).1 h

section

variable (c c')
variable (f : ι → ι') (hf : Function.Injective f)
    (iff : ∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂))

/-- Constructor for embeddings between complex shapes when we have an equivalence
`∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂)`. -/
@[simps]
/-
**ComplexShape.Embedding.mk'** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedding`。
形式化陈述：mk' : Embedding c c' where f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for embeddings between complex shapes when we have an equivalence
`∀ (i₁ i₂ : ι), c.Rel i₁ i₂ ↔ c'.Rel (f i₁) (f i₂)`.
-/
def mk' : Embedding c c' where
  f := f
  injective_f := hf
  rel h := (iff _ _).1 h
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (mk' c c' f hf iff).IsRelIff where
  rel' _ _ h := (iff _ _).2 h

end

/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.next`. -/
/-
**ComplexShape.Embedding.IsTruncGE** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape.Emb
edding`。
形式化陈述：{ι : Type u_1} → {ι' : Type u_2} → {c : ComplexShape ι} → {c' : ComplexSha
pe ι'} → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.next`.
-/
class IsTruncGE : Prop extends e.IsRelIff where
  mem_next {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') :
    ∃ k, e.f k = k'
/-
**ComplexShape.Embedding.mem_next** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embedd
ing`。
形式化陈述：mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : exists 
k, e.f k = k'
参数：h : c'.Rel (e.f j) k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncGE.mem_next`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e.I
sTruncGE]   {j : ι} {k' : ι'}, …
-/
lemma mem_next [e.IsTruncGE] {j : ι} {k' : ι'} (h : c'.Rel (e.f j) k') : ∃ k, e.f k = k' :=
  IsTruncGE.mem_next h

/-- The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.prev`. -/
/-
**ComplexShape.Embedding.IsTruncLE** 是 Mathlib 中的一个归纳类型，位于命名空间 `ComplexShape.Emb
edding`。
形式化陈述：{ι : Type u_1} → {ι' : Type u_2} → {c : ComplexShape ι} → {c' : ComplexSha
pe ι'} → c.Embedding c' → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that the image of the map `e.f` of an embedding of
complex shapes `e : Embedding c c'` is stable by `c'.prev`.
-/
class IsTruncLE : Prop extends e.IsRelIff where
  mem_prev {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) :
    ∃ i, e.f i = i'
/-
**ComplexShape.Embedding.mem_prev** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embedd
ing`。
形式化陈述：mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : exists 
i, e.f i = i'
参数：h : c'.Rel i' (e.f j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.IsTruncLE.mem_prev`：∀ {ι : Type u_1} {ι' : Type u
_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {e : c.Embedding c'} [self : e.I
sTruncLE]   {i' : ι'} {j : ι}, …
-/
lemma mem_prev [e.IsTruncLE] {i' : ι'} {j : ι} (h : c'.Rel i' (e.f j)) : ∃ i, e.f i = i' :=
  IsTruncLE.mem_prev h
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e.IsTruncGE] : e.op.IsTruncLE where
  mem_prev h := e.mem_next h
/-
**ComplexShape.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e.IsTruncLE] : e.op.IsTruncGE where
  mem_next h := e.mem_prev h

open scoped Classical in
/-- The map `ι' → Option ι` which sends `e.f i` to `some i` and the other elements to `none`. -/
/-
**ComplexShape.Embedding.r** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape.Embedding`。
形式化陈述：r (i' : ι') : Option ι
参数：i' : ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ι' → Option ι` which sends `e.f i` to `some i` and the other elements t
o `none`.
-/
noncomputable def r (i' : ι') : Option ι :=
  if h : ∃ (i : ι), e.f i = i'
  then some h.choose
  else none
/-
**ComplexShape.Embedding.r_eq_some** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embed
ding`。
形式化陈述：r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') : e.r i' = some i
参数：hi : e.f i = i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.Embedding.injective_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c 
: ComplexShape ι} {c' : ComplexShape ι'} (self : c.Embedding c'),   Function.Inj
ective self.f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma r_eq_some {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.r i' = some i := by
  have h : ∃ (i : ι), e.f i = i' := ⟨i, hi⟩
  have : h.choose = i := e.injective_f (h.choose_spec.trans (hi.symm))
  dsimp [r]
  rw [dif_pos ⟨i, hi⟩, this]
/-
**ComplexShape.Embedding.r_eq_none** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape.Embed
ding`。
形式化陈述：r_eq_none (i' : ι') (hi : forall i, e.f i != i') : e.r i' = none
参数：i' : ι'；hi : forall i, e.f i != i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
lemma r_eq_none (i' : ι') (hi : ∀ i, e.f i ≠ i') :
    e.r i' = none :=
  dif_neg (by
    rintro ⟨i, hi'⟩
    exact hi i hi')
/-
**ComplexShape.Embedding.r_f** 是 Mathlib 中的一个定理，位于命名空间 `ComplexShape.Embedding`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι
'} (e : c.Embedding c') (i : ι),   e.r (e.f i) = some i
参数：e : c.Embedding c'；i : ι；e.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.Embedding.r_eq_some`：r_eq_some {i : ι} {i' : ι'} (hi : e.f 
i = i') : e.r i' = some i
-/
@[simp] lemma r_f (i : ι) : e.r (e.f i) = some i := r_eq_some _ rfl
/-
**ComplexShape.Embedding.f_eq_of_r_eq_some** 是 Mathlib 中的一个引理，位于命名空间 `ComplexSha
pe.Embedding`。
形式化陈述：f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) : e.f i = i'
参数：hi : e.r i' = some i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ComplexShape.Embedding.r_f`：∀ {ι : Type u_1} {ι' : Type u_2} {c : Comple
xShape ι} {c' : ComplexShape ι'} (e : c.Embedding c') (i : ι),   e.r (e.f i) = s
ome i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ComplexShape.Embedding.r_eq_none`：r_eq_none (i' : ι') (hi : forall i, e.
f i != i') : e.r i' = none
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
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
/-
**ComplexShape.embeddingUp'Add** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：{A : Type u_3} →   [inst : AddCommSemigroup A] →     [inst_1 : IsRightCanc
elAdd A] → (a : A) → A → (ComplexShape.up' a).Embedding (ComplexShape.up' a)
参数：a : A；ComplexShape.up' a；ComplexShape.up' a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from `up' a` to itself via (· + b).
-/
def embeddingUp'Add (a b : A) : Embedding (up' a) (up' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : A) : (embeddingUp'Add a b).IsRelIff := by dsimp [embeddingUp'Add]; infer_instance
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : A) : (embeddingUp'Add a b).IsTruncGE where
  mem_next {j _} h := ⟨j + a, (add_right_comm _ _ _).trans h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down' a` to itself via (· + b). -/
@[simps!]
/-
**ComplexShape.embeddingDown'Add** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：{A : Type u_3} →   [inst : AddCommSemigroup A] →     [inst_1 : IsRightCanc
elAdd A] → (a : A) → A → (ComplexShape.down' a).Embedding (ComplexShape.down' a)
参数：a : A；ComplexShape.down' a；ComplexShape.down' a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from `down' a` to itself via (· + b).
-/
def embeddingDown'Add (a b : A) : Embedding (down' a) (down' a) :=
  Embedding.mk' _ _ (· + b)
    (fun _ _ h => by simpa using h)
    (by dsimp; simp_rw [add_right_comm _ b a, add_right_cancel_iff, implies_true])

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : A) : (embeddingDown'Add a b).IsRelIff := by
  dsimp [embeddingDown'Add]; infer_instance
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : A) : (embeddingDown'Add a b).IsTruncLE where
  mem_prev {_ x} h := ⟨x + a, (add_right_comm _ _ _).trans h⟩

end

set_option backward.defeqAttrib.useBackward true in
/-- The obvious embedding from `up ℕ` to `up ℤ`. -/
@[simps!]
/-
**ComplexShape.embeddingUpNat** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingUpNat : Embedding (up Nat) (up Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious embedding from `up ℕ` to `up ℤ`.
-/
def embeddingUpNat : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingUpNat.IsRelIff := by dsimp [embeddingUpNat]; infer_instance
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingUpNat.IsTruncGE where
  mem_next {j _} h := ⟨j + 1, h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`. -/
@[simps!]
/-
**ComplexShape.embeddingDownNat** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingDownNat : Embedding (down Nat) (up Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from `down ℕ` to `up ℤ` with sends `n` to `-n`.
-/
def embeddingDownNat : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => -n)
    (fun _ _ h => by simpa using h)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingDownNat.IsRelIff := by dsimp [embeddingDownNat]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : embeddingDownNat.IsTruncLE where
  mem_prev {i j} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

variable (p : ℤ)

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `up ℕ` to `up ℤ` which sends `n : ℕ` to `p + n`. -/
@[simps!]
/-
**ComplexShape.embeddingUpIntGE** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingUpIntGE : Embedding (up Nat) (up Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from `up ℕ` to `up ℤ` which sends `n : ℕ` to `p + n`.
-/
def embeddingUpIntGE : Embedding (up ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p + n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embeddingUpIntGE p).IsRelIff := by dsimp [embeddingUpIntGE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embeddingUpIntGE p).IsTruncGE where
  mem_next {j _} h := ⟨j + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
/-- The embedding from `down ℕ` to `up ℤ` which sends `n : ℕ` to `p - n`. -/
@[simps!]
/-
**ComplexShape.embeddingUpIntLE** 是 Mathlib 中的一个定义，位于命名空间 `ComplexShape`。
形式化陈述：embeddingUpIntLE : Embedding (down Nat) (up Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from `down ℕ` to `up ℤ` which sends `n : ℕ` to `p - n`.
-/
def embeddingUpIntLE : Embedding (down ℕ) (up ℤ) :=
  Embedding.mk' _ _ (fun n => p - n)
    (fun _ _ h => by dsimp at h; lia)
    (by dsimp; lia)

set_option backward.isDefEq.respectTransparency false in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embeddingUpIntLE p).IsRelIff := by dsimp [embeddingUpIntLE]; infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.** 是 Mathlib 中的一个实例，位于命名空间 `ComplexShape`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (embeddingUpIntLE p).IsTruncLE where
  mem_prev {_ k} h := ⟨k + 1, by dsimp at h ⊢; lia⟩

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.notMem_range_embeddingUpIntLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `Comp
lexShape`。
形式化陈述：notMem_range_embeddingUpIntLE_iff (n : Int) : (forall (i : Nat), (embeddin
gUpIntLE p).f i != n) ↔ p < n
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma notMem_range_embeddingUpIntLE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntLE p).f i ≠ n) ↔ p < n := by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

set_option backward.defeqAttrib.useBackward true in
/-
**ComplexShape.notMem_range_embeddingUpIntGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `Comp
lexShape`。
形式化陈述：notMem_range_embeddingUpIntGE_iff (n : Int) : (forall (i : Nat), (embeddin
gUpIntGE p).f i != n) ↔ n < p
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma notMem_range_embeddingUpIntGE_iff (n : ℤ) :
    (∀ (i : ℕ), (embeddingUpIntGE p).f i ≠ n) ↔ n < p := by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

end ComplexShape

