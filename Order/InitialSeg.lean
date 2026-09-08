/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Hom.Lex
public import Mathlib.Order.RelIso.Set
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.WellFounded

/-!
# Initial and principal segments

This file defines initial and principal segment embeddings. Though these definitions make sense for
arbitrary relations, they're intended for use with well orders.

An initial segment is simply a lower set, i.e. if `x` belongs to the range, then any `y < x` also
belongs to the range. A principal segment is a set of the form `Set.Iio x` for some `x`.

An initial segment embedding `r ≼i s` is an order embedding `r ↪ s` such that its range is an
initial segment. Likewise, a principal segment embedding `r ≺i s` has a principal segment for a
range.

## Main definitions

* `InitialSeg r s`: Type of initial segment embeddings of `r` into `s`, denoted by `r ≼i s`.
* `PrincipalSeg r s`: Type of principal segment embeddings of `r` into `s`, denoted by `r ≺i s`.

The lemmas `Ordinal.type_le_iff` and `Ordinal.type_lt_iff` tell us that `≼i` corresponds to the `≤`
relation on ordinals, while `≺i` corresponds to the `<` relation. This prompts us to think of
`PrincipalSeg` as a "strict" version of `InitialSeg`.

## Notation

These notations belong to the `InitialSeg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
* `α ≤i β` is an abbreviation for `(· < ·) ≼i (· < ·)`.
* `α <i β` is an abbreviation for `(· < ·) ≺i (· < ·)`.
-/

@[expose] public section

/-! ### Initial segment embeddings -/

universe u

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

open Function

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose `Set.range` is a lower set. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
/-
**InitialSeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_4} → {β : Type u_5} → (α → α → Prop) → (β → β → Prop) → Type (
max u_4 u_5)
参数：α → α → Prop；β → β → Prop；max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is a
n order
embedding whose `Set.range` is a lower set. That is, whenever `b < f a` in `β` t
hen `b` is in the
range of `f`.
-/
structure InitialSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The order embedding is an initial segment -/
  mem_range_of_rel' : ∀ a b, s b (toRelEmbedding a) → b ∈ Set.range toRelEmbedding

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≼i " => InitialSeg

/-- An `InitialSeg` between the `<` relations of two types. -/
notation3:25 α:24 " ≤i " β:25 => @InitialSeg α β (· < ·) (· < ·)

namespace InitialSeg

/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (r ≼i s) α β where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmbeddingLike (r ≼i s) α β where
  injective' f := f.inj'
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RelHomClass (r ≼i s) r s where
  map_rel f := f.map_rel_iff.2

/-- An initial segment embedding between the `<` relations of two partial orders is an order
embedding. -/
/-
**InitialSeg.toOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α <=i β) : α ↪o β
参数：f : α <=i β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial segment embedding between the `<` relations of two partial orders is 
an order
embedding.
-/
def toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α ≤i β) : α ↪o β :=
  f.orderEmbeddingOfLTEmbedding

@[simp]
/-
**InitialSeg.toOrderEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：toOrderEmbedding_apply [PartialOrder α] [PartialOrder β] (f : α <=i β) (x 
: α) : f.toOrderEmbedding x = f x
参数：f : α <=i β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderEmbedding_apply [PartialOrder α] [PartialOrder β] (f : α ≤i β) (x : α) :
    f.toOrderEmbedding x = f x :=
  rfl

@[simp]
/-
**InitialSeg.coe_toOrderEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：coe_toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α <=i β) : (f.
toOrderEmbedding : α -> β) = f
参数：f : α <=i β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α ≤i β) :
    (f.toOrderEmbedding : α → β) = f :=
  rfl
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] [PartialOrder β] : OrderHomClass (α ≤i β) α β where
  map_rel f := f.toOrderEmbedding.map_rel_iff.2
/-
**InitialSeg.ext** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {f g
 : InitialSeg r s},   (∀ (x : α), f x = g x) → f = g
参数：∀ (x : α), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] lemma ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/-
**InitialSeg.coe_coe_fn** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α -> β) = f
参数：f : r ≼i s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f :=
  rfl
/-
**InitialSeg.mem_range_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：mem_range_of_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) -> b in Set.rang
e f
参数：f : r ≼i s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_rel'`：∀ {α : Type u_4} {β : Type u_5} {r : α → α
 → Prop} {s : β → β → Prop} (self : InitialSeg r s) (a : α) (b : β),   s b (self
.toRelEmbedding a)…
-/
theorem mem_range_of_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) → b ∈ Set.range f :=
  f.mem_range_of_rel' _ _
/-
**InitialSeg.map_rel_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f b) ↔ r a b
参数：f : r ≼i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → 
Prop} {s : β → β → Prop} (self : r ↪r s) {a b : α},   s (self.toEmbedding a) (se
lf.toEmbedding …
-/
theorem map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'
/-
**InitialSeg.inj** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：inj (f : r ≼i s) {a b : α} : f a = f b ↔ a = b
参数：f : r ≼i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.inj`：inj (f : r ↪r s) {a b} : f a = f b ↔ a = b
-/
theorem inj (f : r ≼i s) {a b : α} : f a = f b ↔ a = b :=
  f.toRelEmbedding.inj
/-
**InitialSeg.exists_eq_iff_rel** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：exists_eq_iff_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ exists a', f 
a' = b ∧ r a' a
参数：f : r ≼i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InitialSeg.map_rel_iff`：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f 
b) ↔ r a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem exists_eq_iff_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨_, e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

/-- A relation isomorphism is an initial segment embedding -/
@[simps!]
/-
**InitialSeg._root_.RelIso.toInitialSeg** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation isomorphism is an initial segment embedding
-/
def _root_.RelIso.toInitialSeg (f : r ≃r s) : r ≼i s :=
  ⟨f, by simp⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl]
/-
**InitialSeg.refl** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → InitialSeg r r
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function shows that `≼i` is reflexive
-/
protected def refl (r : α → α → Prop) : r ≼i r :=
  (RelIso.refl r).toInitialSeg
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
/-
**InitialSeg.trans** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} →       {r : α → α 
→ Prop} → {s : β → β → Prop} → {t : γ → γ → Prop} → InitialSeg r s → InitialSeg 
s t → InitialSeg r t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of functions shows that `≼i` is transitive
-/
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp only [RelEmbedding.coe_trans, coe_coe_fn, comp_apply] at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩

@[simp]
/-
**InitialSeg.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：refl_apply (x : α) : InitialSeg.refl r x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl

@[simp]
/-
**InitialSeg.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a)
参数：f : r ≼i s；g : s ≼i t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl
/-
**InitialSeg.subsingleton_of_trichotomous_of_irrefl** 是 Mathlib 中的一个实例，位于命名空间 `I
nitialSeg`。
形式化陈述：subsingleton_of_trichotomous_of_irrefl [Std.Trichotomous s] [Std.Irrefl s]
 [IsWellFounded α r] : Subsingleton (r ≼i s) where allEq f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.ext`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} {f g : InitialSeg r s},   (∀ (x : α), f x = g x) → f = g
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a
· 使用定理 `extensional_of_trichotomous_of_irrefl`：extensional_of_trichotomous_of_ir
refl (r : α -> α -> Prop) [Std.Trichotomous r] [Std.Irrefl r] {a b : α} (H : for
all x, r x a ↔ r x b) : a =…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.exists_eq_iff_rel`：exists_eq_iff_rel (f : r ≼i s) {a : α} {b 
: β} : s b (f a) ↔ exists a', f a' = b ∧ r a' a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance subsingleton_of_trichotomous_of_irrefl [Std.Trichotomous s] [Std.Irrefl s]
    [IsWellFounded α r] : Subsingleton (r ≼i s) where
  allEq f g := by
    ext a
    refine IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => ?_
    rw [f.exists_eq_iff_rel, g.exists_eq_iff_rel]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl

/-- Given a well order `s`, there is at most one initial segment embedding of `r` into `s`. -/
/-
**InitialSeg.** 是 Mathlib 中的一个实例，位于命名空间 `InitialSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a well order `s`, there is at most one initial segment embedding of `r` in
to `s`.
-/
instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => have := a.isWellFounded; Subsingleton.elim a⟩
/-
**InitialSeg.eq** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [IsW
ellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
参数：f g : InitialSeg r s；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `InitialSeg.instSubsingletonOfIsWellOrder`：∀ {α : Type u_1} {β : Type u_2
} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder β s], Subsingleton (Initial
Seg r s)
-/
protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]
/-
**InitialSeg.eq_relIso** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：eq_relIso [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a
参数：f : r ≼i s；g : r ≃r s；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
-/
theorem eq_relIso [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a :=
  InitialSeg.eq g.toInitialSeg f a

/-- If we have order embeddings between `α` and `β` whose ranges are initial segments, and `β` is a
well order, then `α` and `β` are order-isomorphic. -/
/-
**InitialSeg.antisymm** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s
参数：f : r ≼i s；g : s ≼i r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have order embeddings between `α` and `β` whose ranges are initial segment
s, and `β` is a
well order, then `α` and `β` are order-isomorphic.
-/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  have := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, (f.trans g).eq (InitialSeg.refl _), (g.trans f).eq (InitialSeg.refl _)⟩, f.map_rel_iff'⟩

@[simp]
/-
**InitialSeg.antisymm_toFun** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g
 : α -> β) = f
参数：f : r ≼i s；g : s ≼i r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f :=
  rfl

@[simp]
/-
**InitialSeg.antisymm_symm** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r
) : (antisymm f g).symm = antisymm g f
参数：f : r ≼i s；g : s ≼i r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.coe_fn_injective`：coe_fn_injective : Injective fun f : r ≃r s => 
(f : α -> β)
-/
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl

/-- An initial segment embedding is either an isomorphism, or a principal segment embedding.

See also `InitialSeg.ltOrEq`. -/
/-
**InitialSeg.eq_or_principal** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：eq_or_principal [IsWellOrder β s] (f : r ≼i s) : Surjective f ∨ exists b, 
forall x, x in Set.range f ↔ s x b
参数：f : r ≼i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `IsWellFounded.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, r y x -> motive y) -> motive x) : motive a
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `trichotomous`：trichotomous [Std.Trichotomous r] : forall a b : α, a ≺ b 
∨ a = b ∨ b ≺ a
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
An initial segment embedding is either an isomorphism, or a principal segment em
bedding.

See also `InitialSeg.ltOrEq`.
-/
theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ ∃ b, ∀ x, x ∈ Set.range f ↔ s x b := by
  apply or_iff_not_imp_right.2
  intro h b
  push Not at h
  apply IsWellFounded.induction s b
  intro x IH
  obtain ⟨y, ⟨hy, hs⟩ | ⟨hy, hs⟩⟩ := h x
  · obtain (rfl | h) := (trichotomous y x).resolve_left hs
    · exact hy
    · obtain ⟨z, rfl⟩ := hy
      exact f.mem_range_of_rel h
  · obtain ⟨z, rfl⟩ := IH y hs
    cases hy (Set.mem_range_self z)

/-- Restrict the codomain of an initial segment -/
/-
**InitialSeg.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：codRestrict (p : Set β) (f : r ≼i s) (H : forall a, f a in p) : r ≼i Subre
l s (· in p)
参数：p : Set β；f : r ≼i s；H : forall a, f a in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of an initial segment
-/
def codRestrict (p : Set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i Subrel s (· ∈ p) :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.mem_range_of_rel h
    ⟨a', by subst e; rfl⟩⟩

@[simp]
/-
**InitialSeg.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a
⟩
参数：p；f : r ≼i s；H a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- Initial segment embedding from an empty type. -/
/-
**InitialSeg.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：ofIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : r ≼i s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Initial segment embedding from an empty type.
-/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
/-
**InitialSeg.leAdd** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：leAdd (r : α -> α -> Prop) (s : β -> β -> Prop) : r ≼i Sum.Lex r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl.inj`：∀ {α : Type u} {β : Type v} {val val_1 : α}, Sum.inl val = 
Sum.inl val_1 → val = val_1
· 使用定理 `Sum.lex_inl_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {a₁ a₂ : α},   Sum.Lex r s (Sum.inl a₁) (Sum.inl a₂) ↔ r a₁ a₂

--- 原说明 ---
Initial segment embedding of an order `r` into the disjoint union of `r` and `s`
.
-/
def leAdd (r : α → α → Prop) (s : β → β → Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩

@[simp]
/-
**InitialSeg.leAdd_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：leAdd_apply (r : α -> α -> Prop) (s : β -> β -> Prop) (a) : leAdd r s a = 
Sum.inl a
参数：r : α -> α -> Prop；s : β -> β -> Prop；a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leAdd_apply (r : α → α → Prop) (s : β → β → Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl
/-
**InitialSeg.acc** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 InitialSeg r s) (a : α),   Acc r a ↔ Acc s (f a)
参数：f : InitialSeg r s；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InitialSeg.map_rel_iff`：map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f 
b) ↔ r a b
· 使用定理 `RelEmbedding.acc`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (f : r ↪r s) (a : α), Acc s (f a) → Acc r a
-/
protected theorem acc (f : r ≼i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  ⟨by
    refine fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => ?_
    obtain ⟨a', rfl⟩ := f.mem_range_of_rel hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩

end InitialSeg

/-! ### Principal segments -/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an initial
segment embedding whose range is `Set.Iio x` for some element `x`. If `β` is a well order, this is
equivalent to the embedding not being surjective. -/
/-
**PrincipalSeg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_4} → {β : Type u_5} → (α → α → Prop) → (β → β → Prop) → Type (
max u_4 u_5)
参数：α → α → Prop；β → β → Prop；max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is a
n initial
segment embedding whose range is `Set.Iio x` for some element `x`. If `β` is a w
ell order, this is
equivalent to the embedding not being surjective.
-/
structure PrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The supremum of the principal segment -/
  top : β
  /-- The range of the order embedding is the set of elements `b` such that `s b top` -/
  mem_range_iff_rel' : ∀ b, b ∈ Set.range toRelEmbedding ↔ s b top

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≺i " => PrincipalSeg

/-- A `PrincipalSeg` between the `<` relations of two types. -/
notation3:25 α:24 " <i " β:25 => @PrincipalSeg α β (· < ·) (· < ·)

open scoped InitialSeg

namespace PrincipalSeg

/-
**PrincipalSeg.** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩
/-
**PrincipalSeg.** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (r ≺i s) fun _ => α → β :=
  ⟨fun f => f⟩
/-
**PrincipalSeg.toRelEmbedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`
。
形式化陈述：toRelEmbedding_injective [Std.Irrefl s] [Std.Trichotomous s] : Function.In
jective (@toRelEmbedding α β r s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extensional_of_trichotomous_of_irrefl`：extensional_of_trichotomous_of_ir
refl (r : α -> α -> Prop) [Std.Trichotomous r] [Std.Irrefl r] {a b : α} (H : for
all x, r x a ↔ r x b) : a =…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toRelEmbedding_injective [Std.Irrefl s] [Std.Trichotomous s] :
    Function.Injective (@toRelEmbedding α β r s) := by
  rintro ⟨f, a, hf⟩ ⟨g, b, hg⟩ rfl
  congr
  refine extensional_of_trichotomous_of_irrefl s fun x ↦ ?_
  rw [← hf, hg]

@[simp]
/-
**PrincipalSeg.toRelEmbedding_inj** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：toRelEmbedding_inj [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} : f.
toRelEmbedding = g.toRelEmbedding ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PrincipalSeg.toRelEmbedding_injective`：toRelEmbedding_injective [Std.Irr
efl s] [Std.Trichotomous s] : Function.Injective (@toRelEmbedding α β r s)
-/
theorem toRelEmbedding_inj [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} :
    f.toRelEmbedding = g.toRelEmbedding ↔ f = g :=
  toRelEmbedding_injective.eq_iff

@[ext]
/-
**PrincipalSeg.ext** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：ext [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : forall x, f x 
= g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrincipalSeg.toRelEmbedding_inj`：toRelEmbedding_inj [Std.Irrefl s] [Std.
Trichotomous s] {f g : r ≺i s} : f.toRelEmbedding = g.toRelEmbedding ↔ f = g
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
-/
theorem ext [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : ∀ x, f x = g x) : f = g := by
  rw [← toRelEmbedding_inj]
  ext
  exact h _

@[simp]
/-
**PrincipalSeg.coe_fn_mk** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α -> β) =
 f
参数：f : r ↪r s；t o。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α → β) = f :=
  rfl
/-
**PrincipalSeg.mem_range_iff_rel** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：mem_range_iff_rel (f : r ≺i s) : forall {b : β}, b in Set.range f ↔ s b f.
top
参数：f : r ≺i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_iff_rel'`：∀ {α : Type u_4} {β : Type u_5} {r : α 
→ α → Prop} {s : β → β → Prop} (self : PrincipalSeg r s) (b : β),   b ∈ Set.rang
e ⇑self.toRelEmbeddin…
-/
theorem mem_range_iff_rel (f : r ≺i s) : ∀ {b : β}, b ∈ Set.range f ↔ s b f.top :=
  f.mem_range_iff_rel' _
/-
**PrincipalSeg.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：range_eq (f : r ≺i s) : Set.range f = {b | s b f.top}
参数：f : r ≺i s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `PrincipalSeg.mem_range_iff_rel`：mem_range_iff_rel (f : r ≺i s) : forall 
{b : β}, b in Set.range f ↔ s b f.top
-/
theorem range_eq (f : r ≺i s) : Set.range f = {b | s b f.top} :=
  Set.ext_iff.2 fun _ ↦ mem_range_iff_rel f
/-
**PrincipalSeg.lt_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
参数：f : r ≺i s；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrincipalSeg.mem_range_iff_rel`：mem_range_iff_rel (f : r ≺i s) : forall 
{b : β}, b in Set.range f ↔ s b f.top
-/
theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.mem_range_iff_rel.1 ⟨_, rfl⟩
/-
**PrincipalSeg.mem_range_of_rel_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：mem_range_of_rel_top (f : r ≺i s) {b : β} (h : s b f.top) : b in Set.range
 f
参数：f : r ≺i s；h : s b f.top。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrincipalSeg.mem_range_iff_rel`：mem_range_iff_rel (f : r ≺i s) : forall 
{b : β}, b in Set.range f ↔ s b f.top
-/
theorem mem_range_of_rel_top (f : r ≺i s) {b : β} (h : s b f.top) : b ∈ Set.range f :=
  f.mem_range_iff_rel.2 h
/-
**PrincipalSeg.mem_range_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：mem_range_of_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)
) : b in Set.range f
参数：f : r ≺i s；h : s b (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_of_rel_top`：mem_range_of_rel_top (f : r ≺i s) {b 
: β} (h : s b f.top) : b in Set.range f
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
-/
theorem mem_range_of_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) :
    b ∈ Set.range f :=
  f.mem_range_of_rel_top <| _root_.trans h <| f.lt_top _
/-
**PrincipalSeg.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：surjOn (f : r ≺i s) : Set.SurjOn f Set.univ { b | s b f.top }
参数：f : r ≺i s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `PrincipalSeg.mem_range_of_rel_top`：mem_range_of_rel_top (f : r ≺i s) {b 
: β} (h : s b f.top) : b in Set.range f
-/
theorem surjOn (f : r ≺i s) : Set.SurjOn f Set.univ { b | s b f.top } := by
  intro b h
  simpa using mem_range_of_rel_top _ h

/-- A principal segment embedding is in particular an initial segment embedding. -/
/-
**PrincipalSeg.hasCoeInitialSeg** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalSeg`。
形式化陈述：hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f

--- 原说明 ---
A principal segment embedding is in particular an initial segment embedding.
-/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.mem_range_of_rel⟩⟩
/-
**PrincipalSeg.coe_coe_fn'** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α -> β) = f
参数：f : r ≺i s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
-/
theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f :=
  rfl
/-
**PrincipalSeg._root_.InitialSeg.eq_principalSeg** 是 Mathlib 中的一个定理，位于命名空间 `Prin
cipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.InitialSeg.eq_principalSeg [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  InitialSeg.eq g f a
/-
**PrincipalSeg.exists_eq_iff_rel** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：exists_eq_iff_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔
 exists a', f a' = b ∧ r a' a
参数：f : r ≺i s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.exists_eq_iff_rel`：exists_eq_iff_rel (f : r ≼i s) {a : α} {b 
: β} : s b (f a) ↔ exists a', f a' = b ∧ r a' a
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
-/
theorem exists_eq_iff_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} :
    s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
  @InitialSeg.exists_eq_iff_rel α β r s f a b

/-- A principal segment is the same as a non-surjective initial segment. -/
/-
**PrincipalSeg._root_.InitialSeg.toPrincipalSeg** 是 Mathlib 中的一个定义，位于命名空间 `Princ
ipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A principal segment is the same as a non-surjective initial segment.
-/
noncomputable def _root_.InitialSeg.toPrincipalSeg [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) : r ≺i s :=
  ⟨f, _, Classical.choose_spec (f.eq_or_principal.resolve_left hf)⟩

@[simp]
/-
**PrincipalSeg._root_.InitialSeg.toPrincipalSeg_apply** 是 Mathlib 中的一个定理，位于命名空间 
`PrincipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.InitialSeg.toPrincipalSeg_apply [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) (x : α) : f.toPrincipalSeg hf x = f x :=
  rfl
/-
**PrincipalSeg.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：irrefl {r : α -> α -> Prop} [IsWellOrder α r] (f : r ≺i r) : False
参数：f : r ≺i r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.eq`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β
 → β → Prop} [IsWellOrder β s] (f g : InitialSeg r s) (a : α),   f a = g a
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransOfIsWellOrder`：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder
 α r], IsTrans α r
-/
theorem irrefl {r : α → α → Prop} [IsWellOrder α r] (f : r ≺i r) : False := by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq f (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h
/-
**PrincipalSeg.** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

/-- Composition of a principal segment embedding with an initial segment embedding, as a principal
segment embedding -/
/-
**PrincipalSeg.transInitial** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：transInitial (f : r ≺i s) (g : s ≼i t) : r ≺i t
参数：f : r ≺i s；g : s ≼i t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a principal segment embedding with an initial segment embedding, 
as a principal
segment embedding
-/
def transInitial (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp [g.exists_eq_iff_rel, ← PrincipalSeg.mem_range_iff_rel, exists_comm, ← exists_and_left]⟩

@[simp]
/-
**PrincipalSeg.transInitial_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：transInitial_apply (f : r ≺i s) (g : s ≼i t) (a : α) : f.transInitial g a 
= g (f a)
参数：f : r ≺i s；g : s ≼i t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transInitial_apply (f : r ≺i s) (g : s ≼i t) (a : α) : f.transInitial g a = g (f a) :=
  rfl

@[simp]
/-
**PrincipalSeg.transInitial_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：transInitial_top (f : r ≺i s) (g : s ≼i t) : (f.transInitial g).top = g f.
top
参数：f : r ≺i s；g : s ≼i t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transInitial_top (f : r ≺i s) (g : s ≼i t) : (f.transInitial g).top = g f.top :=
  rfl

/-- Composition of two principal segment embeddings as a principal segment embedding -/
@[trans]
/-
**PrincipalSeg.trans** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} →       {r : α → α 
→ Prop} →         {s : β → β → Prop} → {t : γ → γ → Prop} → [IsTrans γ t] → Prin
cipalSeg r s → PrincipalSeg s t → PrincipalSeg r t
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f

--- 原说明 ---
Composition of two principal segment embeddings as a principal segment embedding
-/
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  transInitial f g

@[simp]
/-
**PrincipalSeg.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : f.trans g a 
= g (f a)
参数：f : r ≺i s；g : s ≺i t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
/-
**PrincipalSeg.trans_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.
top
参数：f : r ≺i s；g : s ≺i t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl

/-- Composition of an order isomorphism with a principal segment embedding, as a principal
segment embedding -/
/-
**PrincipalSeg.relIsoTrans** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：relIsoTrans (f : r ≃r s) (g : s ≺i t) : r ≺i t
参数：f : r ≃r s；g : s ≺i t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of an order isomorphism with a principal segment embedding, as a pri
ncipal
segment embedding
-/
def relIsoTrans (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c => by simp [g.mem_range_iff_rel]⟩

@[simp]
/-
**PrincipalSeg.relIsoTrans_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：relIsoTrans_apply (f : r ≃r s) (g : s ≺i t) (a : α) : relIsoTrans f g a = 
g (f a)
参数：f : r ≃r s；g : s ≺i t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relIsoTrans_apply (f : r ≃r s) (g : s ≺i t) (a : α) : relIsoTrans f g a = g (f a) :=
  rfl

@[simp]
/-
**PrincipalSeg.relIsoTrans_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：relIsoTrans_top (f : r ≃r s) (g : s ≺i t) : (relIsoTrans f g).top = g.top
参数：f : r ≃r s；g : s ≺i t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relIsoTrans_top (f : r ≃r s) (g : s ≺i t) : (relIsoTrans f g).top = g.top :=
  rfl

/-- Composition of a principal segment embedding with a relation isomorphism, as a principal segment
embedding -/
/-
**PrincipalSeg.transRelIso** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：transRelIso (f : r ≺i s) (g : s ≃r t) : r ≺i t
参数：f : r ≺i s；g : s ≃r t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a principal segment embedding with a relation isomorphism, as a p
rincipal segment
embedding
-/
def transRelIso (f : r ≺i s) (g : s ≃r t) : r ≺i t :=
  transInitial f g.toInitialSeg

@[simp]
/-
**PrincipalSeg.transRelIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：transRelIso_apply (f : r ≺i s) (g : s ≃r t) (a : α) : transRelIso f g a = 
g (f a)
参数：f : r ≺i s；g : s ≃r t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transRelIso_apply (f : r ≺i s) (g : s ≃r t) (a : α) : transRelIso f g a = g (f a) :=
  rfl

@[simp]
/-
**PrincipalSeg.transRelIso_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：transRelIso_top (f : r ≺i s) (g : s ≃r t) : (transRelIso f g).top = g f.to
p
参数：f : r ≺i s；g : s ≃r t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transRelIso_top (f : r ≺i s) (g : s ≃r t) : (transRelIso f g).top = g f.top :=
  rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
/-
**PrincipalSeg.** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalSeg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a well order `s`, there is a most one principal segment embedding of `r` i
nto `s`.
-/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) where
  allEq f g := ext ((f : r ≼i s).eq g)
/-
**PrincipalSeg.eq** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [IsW
ellOrder β s] (f g : PrincipalSeg r s)   (a : α), f.toRelEmbedding a = g.toRelEm
bedding a
参数：f g : PrincipalSeg r s；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PrincipalSeg.instSubsingletonOfIsWellOrder`：∀ {α : Type u_1} {β : Type u
_2} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder β s], Subsingleton (Princ
ipalSeg r s)
-/
protected theorem eq [IsWellOrder β s] (f g : r ≺i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]
/-
**PrincipalSeg.top_eq** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = 
g.top
参数：e : r ≃r s；f : r ≺i t；g : s ≺i t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PrincipalSeg.instSubsingletonOfIsWellOrder`：∀ {α : Type u_1} {β : Type u
_2} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder β s], Subsingleton (Princ
ipalSeg r s)
-/
theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.relIsoTrans e g)]; rfl
/-
**PrincipalSeg.top_rel_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：top_rel_top {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop}
 [IsWellOrder γ t] (f : r ≺i s) (g : s ≺i t) (h : r ≺i t) : t h.top g.top
参数：f : r ≺i s；g : s ≺i t；h : r ≺i t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransOfIsWellOrder`：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder
 α r], IsTrans α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PrincipalSeg.instSubsingletonOfIsWellOrder`：∀ {α : Type u_1} {β : Type u
_2} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder β s], Subsingleton (Princ
ipalSeg r s)
· 使用定理 `PrincipalSeg.lt_top`：lt_top (f : r ≺i s) (a : α) : s (f a) f.top
-/
theorem top_rel_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} [IsWellOrder γ t]
    (f : r ≺i s) (g : s ≺i t) (h : r ≺i t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

/-- Any element of a well order yields a principal segment. -/
@[simps!]
/-
**PrincipalSeg.ofElement** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：ofElement {α : Type*} (r : α -> α -> Prop) (a : α) : Subrel r (r · a) ≺i r
参数：r : α -> α -> Prop；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any element of a well order yields a principal segment.
-/
def ofElement {α : Type*} (r : α → α → Prop) (a : α) : Subrel r (r · a) ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun ⟨⟨_, h⟩, rfl⟩ => h, fun h => ⟨⟨_, h⟩, rfl⟩⟩⟩

@[simp]
/-
**PrincipalSeg.ofElement_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：ofElement_apply {α : Type*} (r : α -> α -> Prop) (a : α) (b) : ofElement r
 a b = b.1
参数：r : α -> α -> Prop；a : α；b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofElement_apply {α : Type*} (r : α → α → Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl

/-- For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic to `r`. -/
@[simps! symm_apply]
/-
**PrincipalSeg.subrelIso** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：subrelIso (f : r ≺i s) : Subrel s (s · f.top) ≃r r
参数：f : r ≺i s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic 
to `r`.
-/
noncomputable def subrelIso (f : r ≺i s) : Subrel s (s · f.top) ≃r r :=
  RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
    (Equiv.subtypeEquivProp <| funext fun _ ↦ propext f.mem_range_iff_rel), f.map_rel_iff⟩

@[simp]
/-
**PrincipalSeg.apply_subrelIso** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：apply_subrelIso (f : r ≺i s) (b : {b // s b f.top}) : f (f.subrelIso b) = 
b
参数：f : r ≺i s；b : {b // s b f.top}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_ofInjective_symm`：apply_ofInjective_symm {α β} {f : α -> β} 
(hf : Injective f) (b : range f) : f ((ofInjective f hf).symm b) = b
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem apply_subrelIso (f : r ≺i s) (b : {b // s b f.top}) : f (f.subrelIso b) = b :=
  Equiv.apply_ofInjective_symm f.injective _

@[simp]
/-
**PrincipalSeg.subrelIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：subrelIso_apply (f : r ≺i s) (a : α) : f.subrelIso ⟨f a, f.lt_top a⟩ = a
参数：f : r ≺i s；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ofInjective_symm_apply`：ofInjective_symm_apply {α β} {f : α -> β} 
(hf : Injective f) (a : α) : (ofInjective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem subrelIso_apply (f : r ≺i s) (a : α) : f.subrelIso ⟨f a, f.lt_top a⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/-- Restrict the codomain of a principal segment embedding. -/
/-
**PrincipalSeg.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：codRestrict (p : Set β) (f : r ≺i s) (H : forall a, f a in p) (H₂ : f.top 
in p) : r ≺i Subrel s (· in p)
参数：p : Set β；f : r ≺i s；H : forall a, f a in p；H₂ : f.top in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a principal segment embedding.
-/
def codRestrict (p : Set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) :
    r ≺i Subrel s (· ∈ p) :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ => by simp [← f.mem_range_iff_rel]⟩

@[simp]
/-
**PrincipalSeg.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f 
a, H a⟩
参数：p；f : r ≺i s；H H₂ a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl

@[simp]
/-
**PrincipalSeg.codRestrict_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.
top, H₂⟩
参数：p；f : r ≺i s；H H₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl

/-- Principal segment from an empty type into a type with a minimal element. -/
/-
**PrincipalSeg.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalSeg`。
形式化陈述：ofIsEmpty (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s b' b
) : r ≺i s
参数：r : α -> α -> Prop；H : forall b', ¬s b' b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Principal segment from an empty type into a type with a minimal element.
-/
def ofIsEmpty (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    mem_range_iff_rel' := by simp [H] }

@[simp]
/-
**PrincipalSeg.ofIsEmpty_top** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：ofIsEmpty_top (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s 
b' b) : (ofIsEmpty r H).top = b
参数：r : α -> α -> Prop；H : forall b', ¬s b' b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofIsEmpty_top (r : α → α → Prop) [IsEmpty α] {b : β} (H : ∀ b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl

/-- Principal segment from the empty relation on `PEmpty` to the empty relation on `PUnit`. -/
/-
**PrincipalSeg.pemptyToPUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `PrincipalSeg`。
形式化陈述：pemptyToPUnit : @emptyRelation PEmpty ≺i @emptyRelation PUnit
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `not_false`：¬False

--- 原说明 ---
Principal segment from the empty relation on `PEmpty` to the empty relation on `
PUnit`.
-/
abbrev pemptyToPUnit : @emptyRelation PEmpty ≺i @emptyRelation PUnit :=
  (@ofIsEmpty _ _ emptyRelation _ _ PUnit.unit) fun _ => not_false

@[deprecated (since := "2026-02-08")] alias pemptyToPunit := pemptyToPUnit
/-
**PrincipalSeg.acc** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [IsT
rans β s] (f : PrincipalSeg r s) (a : α),   Acc r a ↔ Acc s (f.toRelEmbedding a)
参数：f : PrincipalSeg r s；a : α；f.toRelEmbedding a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.acc`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : InitialSeg r s) (a : α),   Acc r a ↔ Acc s (f a)
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
-/
protected theorem acc [IsTrans β s] (f : r ≺i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  (f : r ≼i s).acc a

end PrincipalSeg

/-
**wellFounded_iff_principalSeg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_iff_principalSeg {β : Type u} {s : β -> β -> Prop} [IsTrans β 
s] : WellFounded s ↔ forall (α : Type u) (r : α -> α -> Prop) (_ : r ≺i s), Well
Founded r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `wellFounded_iff_wellFounded_subrel`：wellFounded_iff_wellFounded_subrel {
r : α -> α -> Prop} [IsTrans α r] : WellFounded r ↔ forall b, WellFounded (Subre
l r (r · b)) where mp h …
-/
theorem wellFounded_iff_principalSeg {β : Type u} {s : β → β → Prop} [IsTrans β s] :
    WellFounded s ↔ ∀ (α : Type u) (r : α → α → Prop) (_ : r ≺i s), WellFounded r :=
  ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩

/-! ### Properties of initial and principal segments -/

namespace InitialSeg

open scoped Classical in
/-- Every initial segment embedding into a well order can be turned into an isomorphism if
surjective, or into a principal segment embedding if not. -/
/-
**InitialSeg.principalSumRelIso** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：principalSumRelIso [IsWellOrder β s] (f : r ≼i s) : (r ≺i s) oplus (r ≃r s
)
参数：f : r ≼i s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every initial segment embedding into a well order can be turned into an isomorph
ism if
surjective, or into a principal segment embedding if not.
-/
noncomputable def principalSumRelIso [IsWellOrder β s] (f : r ≼i s) : (r ≺i s) ⊕ (r ≃r s) :=
  if h : Surjective f
    then Sum.inr (RelIso.ofSurjective f h)
    else Sum.inl (f.toPrincipalSeg h)

/-- Composition of an initial segment embedding and a principal segment embedding as a principal
segment embedding -/
/-
**InitialSeg.transPrincipal** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`。
形式化陈述：transPrincipal [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
 r ≺i t
参数：f : r ≼i s；g : s ≺i t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of an initial segment embedding and a principal segment embedding as
 a principal
segment embedding
-/
noncomputable def transPrincipal [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.principalSumRelIso with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.relIsoTrans f' g

@[simp]
/-
**InitialSeg.transPrincipal_apply** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：transPrincipal_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺
i t) (a : α) : f.transPrincipal g a = g (f a)
参数：f : r ≼i s；g : s ≺i t；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.transPrincipal.eq_1`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}   [inst : IsWell
Order β s] [inst_1 :…
· 使用定理 `PrincipalSeg.trans_apply`：trans_apply [IsTrans γ t] (f : r ≺i s) (g : s 
≺i t) (a : α) : f.trans g a = g (f a)
· 使用定理 `InitialSeg.eq_principalSeg`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {s : β → β → Prop} [IsWellOrder β s] (f : InitialSeg r s)   (g : Principa
lSeg r s) (a : α…
· 使用定理 `PrincipalSeg.relIsoTrans_apply`：relIsoTrans_apply (f : r ≃r s) (g : s ≺i
 t) (a : α) : relIsoTrans f g a = g (f a)
· 使用定理 `InitialSeg.eq_relIso`：eq_relIso [IsWellOrder β s] (f : r ≼i s) (g : r ≃r
 s) (a : α) : g a = f a
-/
theorem transPrincipal_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    f.transPrincipal g a = g (f a) := by
  rw [InitialSeg.transPrincipal]
  obtain f' | f' := f.principalSumRelIso
  · rw [PrincipalSeg.trans_apply, f.eq_principalSeg]
  · rw [PrincipalSeg.relIsoTrans_apply, f.eq_relIso]

/-- An initial segment can be extended to an isomorphism by joining a second well order to the
domain. -/
/-
**InitialSeg.exists_sum_relIso** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：exists_sum_relIso {β : Type u} {s : β -> β -> Prop} [IsWellOrder β s] (f :
 r ≼i s) : exists (γ : Type u) (t : γ -> γ -> Prop), IsWellOrder γ t ∧ Nonempty 
(Sum.Lex r t ≃r s)
参数：f : r ≼i s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrel.instIsWellOrderSubtype`：∀ {α : Type u_1} (r : α → α → Prop) [IsWe
llOrder α r] (p : α → Prop), IsWellOrder (Subtype p) (Subrel r p)
· 使用定理 `instIsTransOfIsWellOrder`：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder
 α r], IsTrans α r
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `instIsWellOrderOfIsEmpty`：∀ {α : Type u} [IsEmpty α] (r : α → α → Prop),
 IsWellOrder α r

--- 原说明 ---
An initial segment can be extended to an isomorphism by joining a second well or
der to the
domain.
-/
theorem exists_sum_relIso {β : Type u} {s : β → β → Prop} [IsWellOrder β s] (f : r ≼i s) :
    ∃ (γ : Type u) (t : γ → γ → Prop), IsWellOrder γ t ∧ Nonempty (Sum.Lex r t ≃r s) := by
  classical
  obtain f | f := f.principalSumRelIso
  · exact ⟨_, _, inferInstance,
      ⟨(RelIso.sumLexCongr f.subrelIso.symm (.refl _)).trans <| .sumLexComplLeft ..⟩⟩
  · exact ⟨PEmpty, nofun, inferInstance, ⟨(RelIso.sumLexEmpty r _).trans f⟩⟩

end InitialSeg

/-- The function in `collapse`. -/
/-
**collapseF** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function in `collapse`.
-/
private noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : Π a, { b // ¬s (f a) b } :=
  (RelEmbedding.isWellFounded f).fix _ fun a IH =>
    have H : f a ∈ { b | ∀ a h, s (IH a h).1 b } :=
      fun b h => trans_trichotomous_left (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ H⟩
/-
**collapseF_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem collapseF_lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    ∀ {a'}, r a' a → s (collapseF f a') (collapseF f a) := by
  change _ ∈ { b | ∀ a', r a' a → s (collapseF f a') b }
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _
/-
**collapseF_not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem collapseF_not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : ∀ a', r a' a → s (collapseF f a') b) : ¬s b (collapseF f a) := by
  rw [collapseF, IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ {b | ∀ a', r a' a → s (collapseF f a') b} h

/-- Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That is, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been used yet.

This construction is guaranteed to work as long as there exists some relation embedding `r ↪r s`. -/
@[no_expose]
/-
**RelEmbedding.collapse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelEmbedding.collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s
参数：f : r ↪r s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
· 使用定理 `IsWellOrder.toTrichotomous`：∀ {α : Type u} {r : α → α → Prop} [self : Is
WellOrder α r], Std.Trichotomous r
· 使用定理 `_private.Mathlib.Order.InitialSeg.0.collapseF_lt`：∀ {α : Type u_1} {β : 
Type u_2} {r : α → α → Prop} {s : β → β → Prop} [inst : IsWellOrder β s] (f : r 
↪r s) {a a' : α},   r a' a → s ↑(colla…

--- 原说明 ---
Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That i
s, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been
 used yet.

This construction is guaranteed to work as long as there exists some relation em
bedding `r ↪r s`.
-/
noncomputable def RelEmbedding.collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h ↦ by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h ↦ ?_) lt).elim
      by_contra hn
      exact hm' _ hn h
    · rfl
    · exact (hm gt).elim⟩

/-- For any two well orders, one is an initial segment of the other. -/
/-
**InitialSeg.total** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InitialSeg.total (r s) [IsWellOrder α r] [IsWellOrder β s] : (r ≼i s) oplu
s (s ≼i r)
参数：r s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.instIsWellOrderLex`：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Pro
p) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s],   IsWellOrder (α ⊕ β)
 (Sum.Lex r …

--- 原说明 ---
For any two well orders, one is an initial segment of the other.
-/
noncomputable def InitialSeg.total (r s) [IsWellOrder α r] [IsWellOrder β s] :
    (r ≼i s) ⊕ (s ≼i r) :=
  match (leAdd r s).principalSumRelIso,
    (RelEmbedding.sumLexInr r s).collapse.principalSumRelIso with
  | Sum.inl f, Sum.inr g => Sum.inl <| f.transRelIso g.symm
  | Sum.inr f, Sum.inl g => Sum.inr <| g.transRelIso f.symm
  | Sum.inr f, Sum.inr g => Sum.inl <| (f.trans g.symm).toInitialSeg
  | Sum.inl f, Sum.inl g => Classical.choice <| by
      obtain h | h | h := trichotomous_of (Sum.Lex r s) f.top g.top
      · exact ⟨Sum.inl <| (f.codRestrict {x | Sum.Lex r s x g.top}
          (fun a => _root_.trans (f.lt_top a) h) h).transRelIso g.subrelIso⟩
      · let f := f.subrelIso
        rw [h] at f
        exact ⟨Sum.inl <| (f.symm.trans g.subrelIso).toInitialSeg⟩
      · exact ⟨Sum.inr <| (g.codRestrict {x | Sum.Lex r s x f.top}
          (fun a => _root_.trans (g.lt_top a) h) h).transRelIso f.subrelIso⟩

/-! ### Initial or principal segments with `<` -/

namespace InitialSeg

/-- An order isomorphism is an initial segment -/
@[simps!]
/-
**InitialSeg._root_.OrderIso.toInitialSeg** 是 Mathlib 中的一个定义，位于命名空间 `InitialSeg`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism is an initial segment
-/
def _root_.OrderIso.toInitialSeg [Preorder α] [Preorder β] (f : α ≃o β) : α ≤i β :=
  f.toRelIsoLT.toInitialSeg

variable [PartialOrder β] {a a' : α} {b : β}
/-
**InitialSeg.mem_range_of_le** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：mem_range_of_le [LT α] (f : α <=i β) (h : b <= f a) : b in Set.range f
参数：f : α <=i β；h : b <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
-/
theorem mem_range_of_le [LT α] (f : α ≤i β) (h : b ≤ f a) : b ∈ Set.range f := by
  obtain rfl | hb := h.eq_or_lt
  exacts [⟨a, rfl⟩, f.mem_range_of_rel hb]
/-
**InitialSeg.isLowerSet_range** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：isLowerSet_range [LT α] (f : α <=i β) : IsLowerSet (Set.range f)
参数：f : α <=i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
-/
theorem isLowerSet_range [LT α] (f : α ≤i β) : IsLowerSet (Set.range f) := by
  rintro _ b h ⟨a, rfl⟩
  exact mem_range_of_le f h

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/-
**InitialSeg.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：le_iff_le [PartialOrder α] (f : α <=i β) : f a <= f a' ↔ a <= a'
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem le_iff_le [PartialOrder α] (f : α ≤i β) : f a ≤ f a' ↔ a ≤ a' :=
  f.toOrderEmbedding.le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/-
**InitialSeg.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：lt_iff_lt [PartialOrder α] (f : α <=i β) : f a < f a' ↔ a < a'
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem lt_iff_lt [PartialOrder α] (f : α ≤i β) : f a < f a' ↔ a < a' :=
  f.toOrderEmbedding.lt_iff_lt
/-
**InitialSeg.monotone** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：monotone [PartialOrder α] (f : α <=i β) : Monotone f
参数：f : α <=i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem monotone [PartialOrder α] (f : α ≤i β) : Monotone f :=
  f.toOrderEmbedding.monotone
/-
**InitialSeg.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：strictMono [PartialOrder α] (f : α <=i β) : StrictMono f
参数：f : α <=i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
theorem strictMono [PartialOrder α] (f : α ≤i β) : StrictMono f :=
  f.toOrderEmbedding.strictMono

@[simp]
/-
**InitialSeg.isMin_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：isMin_apply_iff [PartialOrder α] (f : α <=i β) : IsMin (f a) ↔ IsMin a
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isMin_of_apply`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {a : α},   StrictMono f → IsMin (f a) → IsM
in a
· 使用定理 `InitialSeg.strictMono`：strictMono [PartialOrder α] (f : α <=i β) : Stric
tMono f
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.le_iff_le`：le_iff_le [PartialOrder α] (f : α <=i β) : f a <= 
f a' ↔ a <= a'
-/
theorem isMin_apply_iff [PartialOrder α] (f : α ≤i β) : IsMin (f a) ↔ IsMin a := by
  refine ⟨StrictMono.isMin_of_apply f.strictMono, fun h b hb ↦ ?_⟩
  obtain ⟨x, rfl⟩ := f.mem_range_of_le hb
  rw [f.le_iff_le] at hb ⊢
  exact h hb

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]
/-
**InitialSeg.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <=i β) : f ⊥ = ⊥
参数：f : α <=i β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `InitialSeg.map_isMin`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrd
er β] {a : α} [inst_1 : PartialOrder α] (f : α ≤i β),   IsMin a → IsMin (f a)
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α ≤i β) : f ⊥ = ⊥ :=
  (map_isMin f isMin_bot).eq_bot
/-
**InitialSeg.image_Iio** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：image_Iio [PartialOrder α] (f : α <=i β) (a : α) : f '' Set.Iio a = Set.Ii
o (f a)
参数：f : α <=i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.image_Iio`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] (e : α ↪o β),   IsLowerSet (Set.range ⇑e) → ∀ (a : α
), ⇑e '' Set.I…
· 使用定理 `InitialSeg.isLowerSet_range`：isLowerSet_range [LT α] (f : α <=i β) : IsL
owerSet (Set.range f)
-/
theorem image_Iio [PartialOrder α] (f : α ≤i β) (a : α) : f '' Set.Iio a = Set.Iio (f a) :=
  f.toOrderEmbedding.image_Iio f.isLowerSet_range a
/-
**InitialSeg.le_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：le_apply_iff [PartialOrder α] (f : α <=i β) : b <= f a ↔ exists c <= a, f 
c = b
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.le_iff_le`：le_iff_le [PartialOrder α] (f : α <=i β) : f a <= 
f a' ↔ a <= a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InitialSeg.monotone`：monotone [PartialOrder α] (f : α <=i β) : Monotone 
f
-/
theorem le_apply_iff [PartialOrder α] (f : α ≤i β) : b ≤ f a ↔ ∃ c ≤ a, f c = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_le h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.le_iff_le] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.monotone hc
/-
**InitialSeg.lt_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `InitialSeg`。
形式化陈述：lt_apply_iff [PartialOrder α] (f : α <=i β) : b < f a ↔ exists a' < a, f a
' = b
参数：f : α <=i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_rel`：mem_range_of_rel (f : r ≼i s) {a : α} {b : 
β} : s b (f a) -> b in Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InitialSeg.lt_iff_lt`：lt_iff_lt [PartialOrder α] (f : α <=i β) : f a < f
 a' ↔ a < a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InitialSeg.strictMono`：strictMono [PartialOrder α] (f : α <=i β) : Stric
tMono f
-/
theorem lt_apply_iff [PartialOrder α] (f : α ≤i β) : b < f a ↔ ∃ a' < a, f a' = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_rel h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.lt_iff_lt] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.strictMono hc

end InitialSeg

namespace PrincipalSeg

variable [PartialOrder β] {a a' : α} {b : β}

/-
**PrincipalSeg.mem_range_of_le** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：mem_range_of_le [LT α] (f : α <i β) (h : b <= f a) : b in Set.range f
参数：f : α <i β；h : b <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.mem_range_of_le`：mem_range_of_le [LT α] (f : α <=i β) (h : b 
<= f a) : b in Set.range f
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem mem_range_of_le [LT α] (f : α <i β) (h : b ≤ f a) : b ∈ Set.range f :=
  (f : α ≤i β).mem_range_of_le h
/-
**PrincipalSeg.range_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：range_eq_Iio [LT α] (f : α <i β) : Set.range f = Set.Iio f.top
参数：f : α <i β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalSeg.range_eq`：range_eq (f : r ≺i s) : Set.range f = {b | s b f.
top}
-/
theorem range_eq_Iio [LT α] (f : α <i β) : Set.range f = Set.Iio f.top :=
  f.range_eq
/-
**PrincipalSeg.isLowerSet_range** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：isLowerSet_range [LT α] (f : α <i β) : IsLowerSet (Set.range f)
参数：f : α <i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isLowerSet_range`：isLowerSet_range [LT α] (f : α <=i β) : IsL
owerSet (Set.range f)
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isLowerSet_range [LT α] (f : α <i β) : IsLowerSet (Set.range f) :=
  (f : α ≤i β).isLowerSet_range

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/-
**PrincipalSeg.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：le_iff_le [PartialOrder α] (f : α <i β) : f a <= f a' ↔ a <= a'
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.le_iff_le`：le_iff_le [PartialOrder α] (f : α <=i β) : f a <= 
f a' ↔ a <= a'
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem le_iff_le [PartialOrder α] (f : α <i β) : f a ≤ f a' ↔ a ≤ a' :=
  (f : α ≤i β).le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/-
**PrincipalSeg.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：lt_iff_lt [PartialOrder α] (f : α <i β) : f a < f a' ↔ a < a'
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.lt_iff_lt`：lt_iff_lt [PartialOrder α] (f : α <=i β) : f a < f
 a' ↔ a < a'
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem lt_iff_lt [PartialOrder α] (f : α <i β) : f a < f a' ↔ a < a' :=
  (f : α ≤i β).lt_iff_lt
/-
**PrincipalSeg.monotone** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：monotone [PartialOrder α] (f : α <i β) : Monotone f
参数：f : α <i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.monotone`：monotone [PartialOrder α] (f : α <=i β) : Monotone 
f
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem monotone [PartialOrder α] (f : α <i β) : Monotone f :=
  (f : α ≤i β).monotone
/-
**PrincipalSeg.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：strictMono [PartialOrder α] (f : α <i β) : StrictMono f
参数：f : α <i β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.strictMono`：strictMono [PartialOrder α] (f : α <=i β) : Stric
tMono f
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem strictMono [PartialOrder α] (f : α <i β) : StrictMono f :=
  (f : α ≤i β).strictMono

@[simp]
/-
**PrincipalSeg.isMin_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：isMin_apply_iff [PartialOrder α] (f : α <i β) : IsMin (f a) ↔ IsMin a
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.isMin_apply_iff`：isMin_apply_iff [PartialOrder α] (f : α <=i 
β) : IsMin (f a) ↔ IsMin a
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem isMin_apply_iff [PartialOrder α] (f : α <i β) : IsMin (f a) ↔ IsMin a :=
  (f : α ≤i β).isMin_apply_iff

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]
/-
**PrincipalSeg.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <i β) : f ⊥ = ⊥
参数：f : α <i β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.map_bot`：map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (
f : α <=i β) : f ⊥ = ⊥
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <i β) : f ⊥ = ⊥ :=
  (f : α ≤i β).map_bot
/-
**PrincipalSeg.image_Iio** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：image_Iio [PartialOrder α] (f : α <i β) (a : α) : f '' Set.Iio a = Set.Iio
 (f a)
参数：f : α <i β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.image_Iio`：image_Iio [PartialOrder α] (f : α <=i β) (a : α) :
 f '' Set.Iio a = Set.Iio (f a)
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem image_Iio [PartialOrder α] (f : α <i β) (a : α) : f '' Set.Iio a = Set.Iio (f a) :=
  (f : α ≤i β).image_Iio a
/-
**PrincipalSeg.le_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：le_apply_iff [PartialOrder α] (f : α <i β) : b <= f a ↔ exists c <= a, f c
 = b
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.le_apply_iff`：le_apply_iff [PartialOrder α] (f : α <=i β) : b
 <= f a ↔ exists c <= a, f c = b
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem le_apply_iff [PartialOrder α] (f : α <i β) : b ≤ f a ↔ ∃ c ≤ a, f c = b :=
  (f : α ≤i β).le_apply_iff
/-
**PrincipalSeg.lt_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalSeg`。
形式化陈述：lt_apply_iff [PartialOrder α] (f : α <i β) : b < f a ↔ exists a' < a, f a'
 = b
参数：f : α <i β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InitialSeg.lt_apply_iff`：lt_apply_iff [PartialOrder α] (f : α <=i β) : b
 < f a ↔ exists a' < a, f a' = b
· 使用定理 `PrincipalSeg.mem_range_of_rel`：mem_range_of_rel [IsTrans β s] (f : r ≺i 
s) {a : α} {b : β} (h : s b (f a)) : b in Set.range f
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
-/
theorem lt_apply_iff [PartialOrder α] (f : α <i β) : b < f a ↔ ∃ a' < a, f a' = b :=
  (f : α ≤i β).lt_apply_iff

end PrincipalSeg

