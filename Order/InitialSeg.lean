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

variable {α β γ : Type*} {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop}

open Function

/--
Definition of `InitialSeg` / `InitialSeg` 的定义

English:
structure InitialSeg
  parameters: {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)
  extends: r ↪r s
  axioms and operations (1):
    - mem_range_of_rel' : forall a b, s b (toRelEmbedding a) -> b in Set.range toRelEmbedding

中文:
结构 InitialSeg
  参数: {α β : 类型} (r : α -> α -> 命题) (s : β -> β -> 命题)
  继承: r ↪r s
  公理与运算 (1 个):
    - mem_range_of_rel' : 对任意 a b, s b (toRelEmbedding a) -> b in Set.range toRelEmbedding
-/
structure InitialSeg {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop) extends r ↪r s where
  /-- The order embedding is an initial segment -/
  mem_range_of_rel' : forall a b, s b (toRelEmbedding a) -> b in Set.range toRelEmbedding

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≼i " => InitialSeg

/-- An `InitialSeg` between the `<` relations of two types. -/
notation3:25 α:24 " <=i " β:25 => @InitialSeg α β (· < ·) (· < ·)

namespace InitialSeg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (r ≼i s) (r ↪r s)
  body: ⟨InitialSeg.toRelEmbedding⟩

中文:
实例 :
  签名: Coe (r ≼i s) (r ↪r s)
  定义体: ⟨InitialSeg.toRelEmbedding⟩

Depends on / 依赖: InitialSeg, InitialSeg.toRelEmbedding, toRelEmbedding
-/
instance : Coe (r ≼i s) (r ↪r s) :=
  ⟨InitialSeg.toRelEmbedding⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (r ≼i s) α β
  body: f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x

中文:
实例 :
  签名: FunLike (r ≼i s) α β
  定义体: f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x

Depends on / 依赖: f.toFun
-/
instance : FunLike (r ≼i s) α β where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmbeddingLike (r ≼i s) α β
  body: f.inj'

中文:
实例 :
  签名: EmbeddingLike (r ≼i s) α β
  定义体: f.inj'

Depends on / 依赖: f.inj
-/
instance : EmbeddingLike (r ≼i s) α β where
  injective' f := f.inj'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RelHomClass (r ≼i s) r s
  body: f.map_rel_iff.2

中文:
实例 :
  签名: RelHomClass (r ≼i s) r s
  定义体: f.map_rel_iff.2

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
instance : RelHomClass (r ≼i s) r s where
  map_rel f := f.map_rel_iff.2

/--
Definition of `toOrderEmbedding` / `toOrderEmbedding` 的定义

English:
definition toOrderEmbedding
  signature: [PartialOrder α] [PartialOrder β] (f : α <=i β)
  body: f.orderEmbeddingOfLTEmbedding

@[simp]

中文:
定义 toOrderEmbedding
  签名: [PartialOrder α] [PartialOrder β] (f : α <=i β)
  定义体: f.orderEmbeddingOfLTEmbedding

@[simp]

Depends on / 依赖: f.orderEmbeddingOfLTEmbedding, orderEmbeddingOfLTEmbedding
-/
def toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α <=i β) : α ↪o β :=
  f.orderEmbeddingOfLTEmbedding

@[simp]
/--
theorem `toOrderEmbedding_apply` / 定理 `toOrderEmbedding_apply`

English:
theorem toOrderEmbedding_apply
  given: [PartialOrder α] [PartialOrder β] (f : α <=i β) (x : α)
  proof: rfl

@[simp]

中文:
定理 toOrderEmbedding_apply
  条件: [PartialOrder α] [PartialOrder β] (f : α <=i β) (x : α)
  证明: rfl

@[simp]
-/
theorem toOrderEmbedding_apply [PartialOrder α] [PartialOrder β] (f : α <=i β) (x : α) :
    f.toOrderEmbedding x = f x :=
  rfl

@[simp]
/--
theorem `coe_toOrderEmbedding` / 定理 `coe_toOrderEmbedding`

English:
theorem coe_toOrderEmbedding
  given: [PartialOrder α] [PartialOrder β] (f : α <=i β)
  proof: rfl

中文:
定理 coe_toOrderEmbedding
  条件: [PartialOrder α] [PartialOrder β] (f : α <=i β)
  证明: rfl
-/
theorem coe_toOrderEmbedding [PartialOrder α] [PartialOrder β] (f : α <=i β) :
    (f.toOrderEmbedding : α -> β) = f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] [PartialOrder β] : OrderHomClass (α <=i β) α β where
  body: f.toOrderEmbedding.map_rel_iff.2

中文:
实例 [PartialOrder
  签名: α] [PartialOrder β] : OrderHomClass (α <=i β) α β where
  定义体: f.toOrderEmbedding.map_rel_iff.2

Depends on / 依赖: f.toOrderEmbedding.map_rel_iff, map_rel_iff, toOrderEmbedding
-/
instance [PartialOrder α] [PartialOrder β] : OrderHomClass (α <=i β) α β where
  map_rel f := f.toOrderEmbedding.map_rel_iff.2

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : r ≼i s} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[simp]

中文:
引理 ext
  条件: {f g : r ≼i s} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[simp]
-/
@[ext] lemma ext {f g : r ≼i s} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/--
theorem `coe_coe_fn` / 定理 `coe_coe_fn`

English:
theorem coe_coe_fn
  given: (f : r ≼i s)
  statement: ((f : r ↪r s) : α -> β) = f
  proof: rfl

中文:
定理 coe_coe_fn
  条件: (f : r ≼i s)
  结论: ((f : r ↪r s) : α -> β) = f
  证明: rfl
-/
theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α -> β) = f :=
  rfl

/--
theorem `mem_range_of_rel` / 定理 `mem_range_of_rel`

English:
theorem mem_range_of_rel
  given: (f : r ≼i s) {a : α} {b : β}
  statement: s b (f a) -> b in Set.range f
  proof: f.mem_range_of_rel' _ _

中文:
定理 mem_range_of_rel
  条件: (f : r ≼i s) {a : α} {b : β}
  结论: s b (f a) -> b in Set.range f
  证明: f.mem_range_of_rel' _ _

Depends on / 依赖: f.mem_range_of_rel, mem_range_of_rel
-/
theorem mem_range_of_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) -> b in Set.range f :=
  f.mem_range_of_rel' _ _

/--
theorem `map_rel_iff` / 定理 `map_rel_iff`

English:
theorem map_rel_iff
  given: {a b : α} (f : r ≼i s)
  statement: s (f a) (f b) ↔ r a b
  proof: f.map_rel_iff'

中文:
定理 map_rel_iff
  条件: {a b : α} (f : r ≼i s)
  结论: s (f a) (f b) ↔ r a b
  证明: f.map_rel_iff'

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
theorem map_rel_iff {a b : α} (f : r ≼i s) : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

/--
theorem `inj` / 定理 `inj`

English:
theorem inj
  given: (f : r ≼i s) {a b : α}
  statement: f a = f b ↔ a = b
  proof: f.toRelEmbedding.inj

中文:
定理 inj
  条件: (f : r ≼i s) {a b : α}
  结论: f a = f b ↔ a = b
  证明: f.toRelEmbedding.inj

Depends on / 依赖: f.toRelEmbedding.inj, toRelEmbedding
-/
theorem inj (f : r ≼i s) {a b : α} : f a = f b ↔ a = b :=
  f.toRelEmbedding.inj

/--
theorem `exists_eq_iff_rel` / 定理 `exists_eq_iff_rel`

English:
theorem exists_eq_iff_rel
  given: (f : r ≼i s) {a : α} {b : β}
  statement: s b (f a) ↔ exists a', f a' = b ∧ r a' a
  proof: ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨_, e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

中文:
定理 exists_eq_iff_rel
  条件: (f : r ≼i s) {a : α} {b : β}
  结论: s b (f a) ↔ 存在 a', f a' = b ∧ r a' a
  证明: ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨_, e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

Depends on / 依赖: f.map_rel_iff, f.mem_range_of_rel, map_rel_iff, mem_range_of_rel
-/
theorem exists_eq_iff_rel (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ exists a', f a' = b ∧ r a' a :=
  ⟨fun h => by
    rcases f.mem_range_of_rel h with ⟨a', rfl⟩
    exact ⟨a', rfl, f.map_rel_iff.1 h⟩,
    fun ⟨_, e, h⟩ => e ▸ f.map_rel_iff.2 h⟩

/-- A relation isomorphism is an initial segment embedding -/
@[simps!]
/--
Definition of `_root_.RelIso.toInitialSeg` / `_root_.RelIso.toInitialSeg` 的定义

English:
definition _root_.RelIso.toInitialSeg
  signature: (f : r ≃r s)
  body: ⟨f, by simp⟩

中文:
定义 _root_.RelIso.toInitialSeg
  签名: (f : r ≃r s)
  定义体: ⟨f, by simp⟩
-/
def _root_.RelIso.toInitialSeg (f : r ≃r s) : r ≼i s :=
  ⟨f, by simp⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (r : α -> α -> Prop)
  body: (RelIso.refl r).toInitialSeg

中文:
定义 refl
  签名: (r : α -> α -> 命题)
  定义体: (RelIso.refl r).toInitialSeg
-/
protected def refl (r : α -> α -> Prop) : r ≼i r :=
  (RelIso.refl r).toInitialSeg

instance (r : α -> α -> Prop) : Inhabited (r ≼i r) :=
  ⟨InitialSeg.refl r⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : r ≼i s) (g : s ≼i t)
  body: ⟨f.1.trans g.1, fun a c h => by
    simp only [RelEmbedding.coe_trans, coe_coe_fn, comp_apply] at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩

@[simp]

中文:
定义 trans
  签名: (f : r ≼i s) (g : s ≼i t)
  定义体: ⟨f.1.trans g.1, fun a c h => by
    simp only [RelEmbedding.coe_trans, coe_coe_fn, comp_apply] at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩

@[simp]
-/
protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
  ⟨f.1.trans g.1, fun a c h => by
    simp only [RelEmbedding.coe_trans, coe_coe_fn, comp_apply] at h ⊢
    rcases g.2 _ _ h with ⟨b, rfl⟩; have h := g.map_rel_iff.1 h
    rcases f.2 _ _ h with ⟨a', rfl⟩; exact ⟨a', rfl⟩⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : α)
  statement: InitialSeg.refl r x = x
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (x : α)
  结论: InitialSeg.refl r x = x
  证明: rfl

@[simp]
-/
theorem refl_apply (x : α) : InitialSeg.refl r x = x :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (f : r ≼i s) (g : s ≼i t) (a : α)
  statement: (f.trans g) a = g (f a)
  proof: rfl

中文:
定理 trans_apply
  条件: (f : r ≼i s) (g : s ≼i t) (a : α)
  结论: (f.trans g) a = g (f a)
  证明: rfl
-/
theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) :=
  rfl

/--
Instance `subsingleton_of_trichotomous_of_irrefl` / 实例 `subsingleton_of_trichotomous_of_irrefl`

English:
instance subsingleton_of_trichotomous_of_irrefl
  signature: [Std.Trichotomous s] [Std.Irrefl s]
  body: by
    ext a
    refine IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => ?_
    rw [f.exists_eq_iff_rel]; rw [g.exists_eq_iff_rel]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl

中文:
实例 subsingleton_of_trichotomous_of_irrefl
  签名: [Std.Trichotomous s] [Std.Irrefl s]
  定义体: by
    ext a
    refine IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => ?_
    rw [f.exists_eq_iff_rel]; rw [g.exists_eq_iff_rel]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, IsWellFounded, IsWellFounded.induction, and_congr_left, exists_congr, exists_eq_iff_rel, extensional_of_trichotomous_of_irrefl, f.exists_eq_iff_rel, g.exists_eq_iff_rel
-/
instance subsingleton_of_trichotomous_of_irrefl [Std.Trichotomous s] [Std.Irrefl s]
    [IsWellFounded α r] : Subsingleton (r ≼i s) where
  allEq f g := by
    ext a
    refine IsWellFounded.induction r a fun b IH =>
      extensional_of_trichotomous_of_irrefl s fun x => ?_
    rw [f.exists_eq_iff_rel]; rw [g.exists_eq_iff_rel]
    exact exists_congr fun x => and_congr_left fun hx => IH _ hx ▸ Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWellOrder
  signature: β s] : Subsingleton (r ≼i s)
  body: ⟨fun a => have := a.isWellFounded; Subsingleton.elim a⟩

中文:
实例 [IsWellOrder
  签名: β s] : Subsingleton (r ≼i s)
  定义体: ⟨fun a => have := a.isWellFounded; Subsingleton.elim a⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, a.isWellFounded, isWellFounded
-/
instance [IsWellOrder β s] : Subsingleton (r ≼i s) :=
  ⟨fun a => have := a.isWellFounded; Subsingleton.elim a⟩

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: [IsWellOrder β s] (f g : r ≼i s) (a)
  statement: f a = g a
  proof: by
  rw [Subsingleton.elim f g]

中文:
定理 eq
  条件: [IsWellOrder β s] (f g : r ≼i s) (a)
  结论: f a = g a
  证明: by
  rw [Subsingleton.elim f g]
-/
protected theorem eq [IsWellOrder β s] (f g : r ≼i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

/--
theorem `eq_relIso` / 定理 `eq_relIso`

English:
theorem eq_relIso
  given: [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α)
  statement: g a = f a
  proof: InitialSeg.eq g.toInitialSeg f a

中文:
定理 eq_relIso
  条件: [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α)
  结论: g a = f a
  证明: InitialSeg.eq g.toInitialSeg f a

Depends on / 依赖: InitialSeg, InitialSeg.eq, g.toInitialSeg, toInitialSeg
-/
theorem eq_relIso [IsWellOrder β s] (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a :=
  InitialSeg.eq g.toInitialSeg f a

/--
Definition of `antisymm` / `antisymm` 的定义

English:
definition antisymm
  signature: [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  body: have := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, (f.trans g).eq (InitialSeg.refl _), (g.trans f).eq (InitialSeg.refl _)⟩, f.map_rel_iff'⟩

@[simp]

中文:
定义 antisymm
  签名: [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  定义体: have := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, (f.trans g).eq (InitialSeg.refl _), (g.trans f).eq (InitialSeg.refl _)⟩, f.map_rel_iff'⟩

@[simp]

Depends on / 依赖: InitialSeg, InitialSeg.refl, f.map_rel_iff, f.toRelEmbedding.isWellOrder, f.trans, g.trans, isWellOrder, map_rel_iff, toRelEmbedding
-/
def antisymm [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
  have := f.toRelEmbedding.isWellOrder
  ⟨⟨f, g, (f.trans g).eq (InitialSeg.refl _), (g.trans f).eq (InitialSeg.refl _)⟩, f.map_rel_iff'⟩

@[simp]
/--
theorem `antisymm_toFun` / 定理 `antisymm_toFun`

English:
theorem antisymm_toFun
  given: [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  statement: (antisymm f g : α -> β) = f
  proof: rfl

@[simp]

中文:
定理 antisymm_toFun
  条件: [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  结论: (antisymm f g : α -> β) = f
  证明: rfl

@[simp]
-/
theorem antisymm_toFun [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α -> β) = f :=
  rfl

@[simp]
/--
theorem `antisymm_symm` / 定理 `antisymm_symm`

English:
theorem antisymm_symm
  given: [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  proof: RelIso.coe_fn_injective rfl

中文:
定理 antisymm_symm
  条件: [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r)
  证明: RelIso.coe_fn_injective rfl

Depends on / 依赖: RelIso, RelIso.coe_fn_injective, coe_fn_injective
-/
theorem antisymm_symm [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s) (g : s ≼i r) :
    (antisymm f g).symm = antisymm g f :=
  RelIso.coe_fn_injective rfl

/--
theorem `eq_or_principal` / 定理 `eq_or_principal`

English:
theorem eq_or_principal
  given: [IsWellOrder β s] (f : r ≼i s)
  proof: by
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
  · obtain ⟨z

中文:
定理 eq_or_principal
  条件: [IsWellOrder β s] (f : r ≼i s)
  证明: by
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
  · obtain ⟨z

Depends on / 依赖: IsWellFounded, IsWellFounded.induction, Set.mem_range_self, f.mem_range_of_rel, mem_range_of_rel, mem_range_self, or_iff_not_imp_right, resolve_left, trichotomous
-/
theorem eq_or_principal [IsWellOrder β s] (f : r ≼i s) :
    Surjective f ∨ exists b, forall x, x in Set.range f ↔ s x b := by
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

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (p : Set β) (f : r ≼i s) (H : forall a, f a in p)
  body: ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.mem_range_of_rel h
    ⟨a', by subst e; rfl⟩⟩

@[simp]

中文:
定义 codRestrict
  签名: (p : Set β) (f : r ≼i s) (H : 对任意 a, f a in p)
  定义体: ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.mem_range_of_rel h
    ⟨a', by subst e; rfl⟩⟩

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.codRestrict, codRestrict, f.mem_range_of_rel, mem_range_of_rel
-/
def codRestrict (p : Set β) (f : r ≼i s) (H : forall a, f a in p) : r ≼i Subrel s (· in p) :=
  ⟨RelEmbedding.codRestrict p f H, fun a ⟨b, m⟩ h =>
    let ⟨a', e⟩ := f.mem_range_of_rel h
    ⟨a', by subst e; rfl⟩⟩

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: (p) (f : r ≼i s) (H a)
  statement: codRestrict p f H a = ⟨f a, H a⟩
  proof: rfl

中文:
定理 codRestrict_apply
  条件: (p) (f : r ≼i s) (H a)
  结论: codRestrict p f H a = ⟨f a, H a⟩
  证明: rfl
-/
theorem codRestrict_apply (p) (f : r ≼i s) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α]
  body: ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩

中文:
定义 ofIsEmpty
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [IsEmpty α]
  定义体: ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩

Depends on / 依赖: RelEmbedding, RelEmbedding.ofIsEmpty, isEmptyElim, ofIsEmpty
-/
def ofIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : r ≼i s :=
  ⟨RelEmbedding.ofIsEmpty r s, isEmptyElim⟩

/--
Definition of `leAdd` / `leAdd` 的定义

English:
definition leAdd
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop)
  body: ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩

@[simp]

中文:
定义 leAdd
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题)
  定义体: ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩

@[simp]

Depends on / 依赖: False.elim, Sum.inl, Sum.inl.inj, Sum.lex_inl_inl, Sum.lex_inr_inl, lex_inl_inl, lex_inr_inl
-/
def leAdd (r : α -> α -> Prop) (s : β -> β -> Prop) : r ≼i Sum.Lex r s :=
  ⟨⟨⟨Sum.inl, fun _ _ => Sum.inl.inj⟩, Sum.lex_inl_inl⟩, fun a b => by
    cases b <;> [exact fun _ => ⟨_, rfl⟩; exact False.elim ∘ Sum.lex_inr_inl]⟩

@[simp]
/--
theorem `leAdd_apply` / 定理 `leAdd_apply`

English:
theorem leAdd_apply
  given: (r : α -> α -> Prop) (s : β -> β -> Prop) (a)
  statement: leAdd r s a = Sum.inl a
  proof: rfl

中文:
定理 leAdd_apply
  条件: (r : α -> α -> 命题) (s : β -> β -> 命题) (a)
  结论: leAdd r s a = Sum.inl a
  证明: rfl
-/
theorem leAdd_apply (r : α -> α -> Prop) (s : β -> β -> Prop) (a) : leAdd r s a = Sum.inl a :=
  rfl

/--
theorem `acc` / 定理 `acc`

English:
theorem acc
  given: (f : r ≼i s) (a : α)
  statement: Acc r a ↔ Acc s (f a)
  proof: ⟨by
    refine fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => ?_
    obtain ⟨a', rfl⟩ := f.mem_range_of_rel hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩

中文:
定理 acc
  条件: (f : r ≼i s) (a : α)
  结论: Acc r a ↔ Acc s (f a)
  证明: ⟨by
    refine fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => ?_
    obtain ⟨a', rfl⟩ := f.mem_range_of_rel hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩
-/
protected theorem acc (f : r ≼i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  ⟨by
    refine fun h => Acc.recOn h fun a _ ha => Acc.intro _ fun b hb => ?_
    obtain ⟨a', rfl⟩ := f.mem_range_of_rel hb
    exact ha _ (f.map_rel_iff.mp hb), f.toRelEmbedding.acc a⟩

end InitialSeg

/-! ### Principal segments -/

/--
Definition of `PrincipalSeg` / `PrincipalSeg` 的定义

English:
structure PrincipalSeg
  parameters: {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)
  extends: r ↪r s
  axioms and operations (2):
    - top : β
    - mem_range_iff_rel' : forall b, b in Set.range toRelEmbedding ↔ s b top

中文:
结构 PrincipalSeg
  参数: {α β : 类型} (r : α -> α -> 命题) (s : β -> β -> 命题)
  继承: r ↪r s
  公理与运算 (2 个):
    - top : β
    - mem_range_iff_rel' : 对任意 b, b in Set.range toRelEmbedding ↔ s b top
-/
structure PrincipalSeg {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop) extends r ↪r s where
  /-- The supremum of the principal segment -/
  top : β
  /-- The range of the order embedding is the set of elements `b` such that `s b top` -/
  mem_range_iff_rel' : forall b, b in Set.range toRelEmbedding ↔ s b top

@[inherit_doc]
scoped[InitialSeg] infixl:25 " ≺i " => PrincipalSeg

/-- A `PrincipalSeg` between the `<` relations of two types. -/
notation3:25 α:24 " <i " β:25 => @PrincipalSeg α β (· < ·) (· < ·)

open scoped InitialSeg

namespace PrincipalSeg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (r ≺i s) (r ↪r s)
  body: ⟨PrincipalSeg.toRelEmbedding⟩

中文:
实例 :
  签名: CoeOut (r ≺i s) (r ↪r s)
  定义体: ⟨PrincipalSeg.toRelEmbedding⟩

Depends on / 依赖: PrincipalSeg, PrincipalSeg.toRelEmbedding, toRelEmbedding
-/
instance : CoeOut (r ≺i s) (r ↪r s) :=
  ⟨PrincipalSeg.toRelEmbedding⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (r ≺i s) fun _ => α -> β
  body: ⟨fun f => f⟩

中文:
实例 :
  签名: CoeFun (r ≺i s) fun _ => α -> β
  定义体: ⟨fun f => f⟩
-/
instance : CoeFun (r ≺i s) fun _ => α -> β :=
  ⟨fun f => f⟩

/--
theorem `toRelEmbedding_injective` / 定理 `toRelEmbedding_injective`

English:
theorem toRelEmbedding_injective
  given: [Std.Irrefl s] [Std.Trichotomous s]
  proof: by
  rintro ⟨f, a, hf⟩ ⟨g, b, hg⟩ rfl
  congr
  refine extensional_of_trichotomous_of_irrefl s fun x => ?_
  rw [← hf]; rw [hg]

@[simp]

中文:
定理 toRelEmbedding_injective
  条件: [Std.Irrefl s] [Std.Trichotomous s]
  证明: by
  rintro ⟨f, a, hf⟩ ⟨g, b, hg⟩ rfl
  congr
  refine extensional_of_trichotomous_of_irrefl s fun x => ?_
  rw [← hf]; rw [hg]

@[simp]

Depends on / 依赖: extensional_of_trichotomous_of_irrefl
-/
theorem toRelEmbedding_injective [Std.Irrefl s] [Std.Trichotomous s] :
    Function.Injective (@toRelEmbedding α β r s) := by
  rintro ⟨f, a, hf⟩ ⟨g, b, hg⟩ rfl
  congr
  refine extensional_of_trichotomous_of_irrefl s fun x => ?_
  rw [← hf]; rw [hg]

@[simp]
/--
theorem `toRelEmbedding_inj` / 定理 `toRelEmbedding_inj`

English:
theorem toRelEmbedding_inj
  given: [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s}
  proof: toRelEmbedding_injective.eq_iff

@[ext]

中文:
定理 toRelEmbedding_inj
  条件: [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s}
  证明: toRelEmbedding_injective.eq_iff

@[ext]

Depends on / 依赖: eq_iff, toRelEmbedding_injective, toRelEmbedding_injective.eq_iff
-/
theorem toRelEmbedding_inj [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} :
    f.toRelEmbedding = g.toRelEmbedding ↔ f = g :=
  toRelEmbedding_injective.eq_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : forall x, f x = g x)
  statement: f = g
  proof: by
  rw [← toRelEmbedding_inj]
  ext
  exact h _

@[simp]

中文:
定理 ext
  条件: [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: by
  rw [← toRelEmbedding_inj]
  ext
  exact h _

@[simp]

Depends on / 依赖: toRelEmbedding_inj
-/
theorem ext [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : forall x, f x = g x) : f = g := by
  rw [← toRelEmbedding_inj]
  ext
  exact h _

@[simp]
/--
theorem `coe_fn_mk` / 定理 `coe_fn_mk`

English:
theorem coe_fn_mk
  given: (f : r ↪r s) (t o)
  statement: (@PrincipalSeg.mk _ _ r s f t o : α -> β) = f
  proof: rfl

中文:
定理 coe_fn_mk
  条件: (f : r ↪r s) (t o)
  结论: (@PrincipalSeg.mk _ _ r s f t o : α -> β) = f
  证明: rfl
-/
theorem coe_fn_mk (f : r ↪r s) (t o) : (@PrincipalSeg.mk _ _ r s f t o : α -> β) = f :=
  rfl

/--
theorem `mem_range_iff_rel` / 定理 `mem_range_iff_rel`

English:
theorem mem_range_iff_rel
  given: (f : r ≺i s)
  statement: forall {b : β}, b in Set.range f ↔ s b f.top
  proof: f.mem_range_iff_rel' _

中文:
定理 mem_range_iff_rel
  条件: (f : r ≺i s)
  结论: 对任意 {b : β}, b in Set.range f ↔ s b f.top
  证明: f.mem_range_iff_rel' _

Depends on / 依赖: f.mem_range_iff_rel, mem_range_iff_rel
-/
theorem mem_range_iff_rel (f : r ≺i s) : forall {b : β}, b in Set.range f ↔ s b f.top :=
  f.mem_range_iff_rel' _

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: (f : r ≺i s)
  statement: Set.range f = {b | s b f.top}
  proof: Set.ext_iff.2 fun _ => mem_range_iff_rel f

中文:
定理 range_eq
  条件: (f : r ≺i s)
  结论: Set.range f = {b | s b f.top}
  证明: Set.ext_iff.2 fun _ => mem_range_iff_rel f

Depends on / 依赖: Set.ext_iff, ext_iff, mem_range_iff_rel
-/
theorem range_eq (f : r ≺i s) : Set.range f = {b | s b f.top} :=
  Set.ext_iff.2 fun _ => mem_range_iff_rel f

/--
theorem `lt_top` / 定理 `lt_top`

English:
theorem lt_top
  given: (f : r ≺i s) (a : α)
  statement: s (f a) f.top
  proof: f.mem_range_iff_rel.1 ⟨_, rfl⟩

中文:
定理 lt_top
  条件: (f : r ≺i s) (a : α)
  结论: s (f a) f.top
  证明: f.mem_range_iff_rel.1 ⟨_, rfl⟩

Depends on / 依赖: f.mem_range_iff_rel, mem_range_iff_rel
-/
theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
  f.mem_range_iff_rel.1 ⟨_, rfl⟩

/--
theorem `mem_range_of_rel_top` / 定理 `mem_range_of_rel_top`

English:
theorem mem_range_of_rel_top
  given: (f : r ≺i s) {b : β} (h : s b f.top)
  statement: b in Set.range f
  proof: f.mem_range_iff_rel.2 h

中文:
定理 mem_range_of_rel_top
  条件: (f : r ≺i s) {b : β} (h : s b f.top)
  结论: b in Set.range f
  证明: f.mem_range_iff_rel.2 h

Depends on / 依赖: f.mem_range_iff_rel, mem_range_iff_rel
-/
theorem mem_range_of_rel_top (f : r ≺i s) {b : β} (h : s b f.top) : b in Set.range f :=
  f.mem_range_iff_rel.2 h

/--
theorem `mem_range_of_rel` / 定理 `mem_range_of_rel`

English:
theorem mem_range_of_rel
  given: [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a))
  proof: f.mem_range_of_rel_top _root_.trans h f.lt_top _

中文:
定理 mem_range_of_rel
  条件: [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a))
  证明: f.mem_range_of_rel_top _root_.trans h f.lt_top _

Depends on / 依赖: _root_, _root_.trans, f.lt_top, f.mem_range_of_rel_top, lt_top, mem_range_of_rel_top
-/
theorem mem_range_of_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) :
    b in Set.range f :=
f.mem_range_of_rel_top _root_.trans h f.lt_top _

/--
theorem `surjOn` / 定理 `surjOn`

English:
theorem surjOn
  given: (f : r ≺i s)
  statement: Set.SurjOn f Set.univ { b | s b f.top }
  proof: by
  intro b h
  simpa using mem_range_of_rel_top _ h

中文:
定理 surjOn
  条件: (f : r ≺i s)
  结论: Set.SurjOn f Set.univ { b | s b f.top }
  证明: by
  intro b h
  simpa using mem_range_of_rel_top _ h

Depends on / 依赖: mem_range_of_rel_top
-/
theorem surjOn (f : r ≺i s) : Set.SurjOn f Set.univ { b | s b f.top } := by
  intro b h
  simpa using mem_range_of_rel_top _ h

/--
Instance `hasCoeInitialSeg` / 实例 `hasCoeInitialSeg`

English:
instance hasCoeInitialSeg
  signature: [IsTrans β s]
  body: ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.mem_range_of_rel⟩⟩

中文:
实例 hasCoeInitialSeg
  签名: [IsTrans β s]
  定义体: ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.mem_range_of_rel⟩⟩

Depends on / 依赖: f.mem_range_of_rel, f.toRelEmbedding, mem_range_of_rel, toRelEmbedding
-/
instance hasCoeInitialSeg [IsTrans β s] : Coe (r ≺i s) (r ≼i s) :=
  ⟨fun f => ⟨f.toRelEmbedding, fun _ _ => f.mem_range_of_rel⟩⟩

/--
theorem `coe_coe_fn'` / 定理 `coe_coe_fn'`

English:
theorem coe_coe_fn'
  given: [IsTrans β s] (f : r ≺i s)
  statement: ((f : r ≼i s) : α -> β) = f
  proof: rfl

中文:
定理 coe_coe_fn'
  条件: [IsTrans β s] (f : r ≺i s)
  结论: ((f : r ≼i s) : α -> β) = f
  证明: rfl
-/
theorem coe_coe_fn' [IsTrans β s] (f : r ≺i s) : ((f : r ≼i s) : α -> β) = f :=
  rfl

/--
theorem `_root_.InitialSeg.eq_principalSeg` / 定理 `_root_.InitialSeg.eq_principalSeg`

English:
theorem _root_.InitialSeg.eq_principalSeg
  given: [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α)
  proof: InitialSeg.eq g f a

中文:
定理 _root_.InitialSeg.eq_principalSeg
  条件: [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α)
  证明: InitialSeg.eq g f a

Depends on / 依赖: InitialSeg, InitialSeg.eq
-/
theorem _root_.InitialSeg.eq_principalSeg [IsWellOrder β s] (f : r ≼i s) (g : r ≺i s) (a : α) :
    g a = f a :=
  InitialSeg.eq g f a

/--
theorem `exists_eq_iff_rel` / 定理 `exists_eq_iff_rel`

English:
theorem exists_eq_iff_rel
  given: [IsTrans β s] (f : r ≺i s) {a : α} {b : β}
  proof: @InitialSeg.exists_eq_iff_rel α β r s f a b

中文:
定理 exists_eq_iff_rel
  条件: [IsTrans β s] (f : r ≺i s) {a : α} {b : β}
  证明: @InitialSeg.exists_eq_iff_rel α β r s f a b

Depends on / 依赖: InitialSeg, InitialSeg.exists_eq_iff_rel, exists_eq_iff_rel
-/
theorem exists_eq_iff_rel [IsTrans β s] (f : r ≺i s) {a : α} {b : β} :
    s b (f a) ↔ exists a', f a' = b ∧ r a' a :=
  @InitialSeg.exists_eq_iff_rel α β r s f a b

/--
Definition of `_root_.InitialSeg.toPrincipalSeg` / `_root_.InitialSeg.toPrincipalSeg` 的定义

English:
definition _root_.InitialSeg.toPrincipalSeg
  signature: [IsWellOrder β s] (f : r ≼i s)
  body: ⟨f, _, Classical.choose_spec (f.eq_or_principal.resolve_left hf)⟩

@[simp]

中文:
定义 _root_.InitialSeg.toPrincipalSeg
  签名: [IsWellOrder β s] (f : r ≼i s)
  定义体: ⟨f, _, Classical.choose_spec (f.eq_or_principal.resolve_left hf)⟩

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, eq_or_principal, f.eq_or_principal.resolve_left, resolve_left
-/
noncomputable def _root_.InitialSeg.toPrincipalSeg [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) : r ≺i s :=
  ⟨f, _, Classical.choose_spec (f.eq_or_principal.resolve_left hf)⟩

@[simp]
/--
theorem `_root_.InitialSeg.toPrincipalSeg_apply` / 定理 `_root_.InitialSeg.toPrincipalSeg_apply`

English:
theorem _root_.InitialSeg.toPrincipalSeg_apply
  statement: [IsWellOrder β s] (f : r ≼i s)
  proof: rfl

中文:
定理 _root_.InitialSeg.toPrincipalSeg_apply
  结论: [IsWellOrder β s] (f : r ≼i s)
  证明: rfl
-/
theorem _root_.InitialSeg.toPrincipalSeg_apply [IsWellOrder β s] (f : r ≼i s)
    (hf : ¬ Surjective f) (x : α) : f.toPrincipalSeg hf x = f x :=
  rfl

/--
theorem `irrefl` / 定理 `irrefl`

English:
theorem irrefl
  given: {r : α -> α -> Prop} [IsWellOrder α r] (f : r ≺i r)
  statement: False
  proof: by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq f (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h

中文:
定理 irrefl
  条件: {r : α -> α -> 命题} [IsWellOrder α r] (f : r ≺i r)
  结论: False
  证明: by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq f (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h

Depends on / 依赖: InitialSeg, InitialSeg.eq, InitialSeg.refl, _root_, _root_.irrefl, f.lt_top, f.top, irrefl, lt_top
-/
theorem irrefl {r : α -> α -> Prop} [IsWellOrder α r] (f : r ≺i r) : False := by
  have h := f.lt_top f.top
  rw [show f f.top = f.top from InitialSeg.eq f (InitialSeg.refl r) f.top] at h
  exact _root_.irrefl _ h

instance (r : α -> α -> Prop) [IsWellOrder α r] : IsEmpty (r ≺i r) :=
  ⟨fun f => f.irrefl⟩

/--
Definition of `transInitial` / `transInitial` 的定义

English:
definition transInitial
  signature: (f : r ≺i s) (g : s ≼i t)
  body: ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp [g.exists_eq_iff_rel, ← PrincipalSeg.mem_range_iff_rel, exists_comm, ← exists_and_left]⟩

@[simp]

中文:
定义 transInitial
  签名: (f : r ≺i s) (g : s ≼i t)
  定义体: ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp [g.exists_eq_iff_rel, ← PrincipalSeg.mem_range_iff_rel, exists_comm, ← exists_and_left]⟩

@[simp]

Depends on / 依赖: PrincipalSeg, PrincipalSeg.mem_range_iff_rel, RelEmbedding, RelEmbedding.trans, exists_and_left, exists_comm, exists_eq_iff_rel, f.top, g.exists_eq_iff_rel, mem_range_iff_rel
-/
def transInitial (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g f.top, fun a => by
    simp [g.exists_eq_iff_rel, ← PrincipalSeg.mem_range_iff_rel, exists_comm, ← exists_and_left]⟩

@[simp]
/--
theorem `transInitial_apply` / 定理 `transInitial_apply`

English:
theorem transInitial_apply
  given: (f : r ≺i s) (g : s ≼i t) (a : α)
  statement: f.transInitial g a = g (f a)
  proof: rfl

@[simp]

中文:
定理 transInitial_apply
  条件: (f : r ≺i s) (g : s ≼i t) (a : α)
  结论: f.transInitial g a = g (f a)
  证明: rfl

@[simp]
-/
theorem transInitial_apply (f : r ≺i s) (g : s ≼i t) (a : α) : f.transInitial g a = g (f a) :=
  rfl

@[simp]
/--
theorem `transInitial_top` / 定理 `transInitial_top`

English:
theorem transInitial_top
  given: (f : r ≺i s) (g : s ≼i t)
  statement: (f.transInitial g).top = g f.top
  proof: rfl

中文:
定理 transInitial_top
  条件: (f : r ≺i s) (g : s ≼i t)
  结论: (f.transInitial g).top = g f.top
  证明: rfl
-/
theorem transInitial_top (f : r ≺i s) (g : s ≼i t) : (f.transInitial g).top = g f.top :=
  rfl

/-- Composition of two principal segment embeddings as a principal segment embedding -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t)
  body: transInitial f g

@[simp]

中文:
定义 trans
  签名: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t)
  定义体: transInitial f g

@[simp]
-/
protected def trans [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
  transInitial f g

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α)
  statement: f.trans g a = g (f a)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α)
  结论: f.trans g a = g (f a)
  证明: rfl

@[simp]
-/
theorem trans_apply [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : f.trans g a = g (f a) :=
  rfl

@[simp]
/--
theorem `trans_top` / 定理 `trans_top`

English:
theorem trans_top
  given: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t)
  statement: (f.trans g).top = g f.top
  proof: rfl

中文:
定理 trans_top
  条件: [IsTrans γ t] (f : r ≺i s) (g : s ≺i t)
  结论: (f.trans g).top = g f.top
  证明: rfl
-/
theorem trans_top [IsTrans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top :=
  rfl

/--
Definition of `relIsoTrans` / `relIsoTrans` 的定义

English:
definition relIsoTrans
  signature: (f : r ≃r s) (g : s ≺i t)
  body: ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c => by simp [g.mem_range_iff_rel]⟩

@[simp]

中文:
定义 relIsoTrans
  签名: (f : r ≃r s) (g : s ≺i t)
  定义体: ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c => by simp [g.mem_range_iff_rel]⟩

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.trans, g.mem_range_iff_rel, g.top, mem_range_iff_rel
-/
def relIsoTrans (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
  ⟨@RelEmbedding.trans _ _ _ r s t f g, g.top, fun c => by simp [g.mem_range_iff_rel]⟩

@[simp]
/--
theorem `relIsoTrans_apply` / 定理 `relIsoTrans_apply`

English:
theorem relIsoTrans_apply
  given: (f : r ≃r s) (g : s ≺i t) (a : α)
  statement: relIsoTrans f g a = g (f a)
  proof: rfl

@[simp]

中文:
定理 relIsoTrans_apply
  条件: (f : r ≃r s) (g : s ≺i t) (a : α)
  结论: relIsoTrans f g a = g (f a)
  证明: rfl

@[simp]
-/
theorem relIsoTrans_apply (f : r ≃r s) (g : s ≺i t) (a : α) : relIsoTrans f g a = g (f a) :=
  rfl

@[simp]
/--
theorem `relIsoTrans_top` / 定理 `relIsoTrans_top`

English:
theorem relIsoTrans_top
  given: (f : r ≃r s) (g : s ≺i t)
  statement: (relIsoTrans f g).top = g.top
  proof: rfl

中文:
定理 relIsoTrans_top
  条件: (f : r ≃r s) (g : s ≺i t)
  结论: (relIsoTrans f g).top = g.top
  证明: rfl
-/
theorem relIsoTrans_top (f : r ≃r s) (g : s ≺i t) : (relIsoTrans f g).top = g.top :=
  rfl

/--
Definition of `transRelIso` / `transRelIso` 的定义

English:
definition transRelIso
  signature: (f : r ≺i s) (g : s ≃r t)
  body: transInitial f g.toInitialSeg

@[simp]

中文:
定义 transRelIso
  签名: (f : r ≺i s) (g : s ≃r t)
  定义体: transInitial f g.toInitialSeg

@[simp]

Depends on / 依赖: g.toInitialSeg, toInitialSeg, transInitial
-/
def transRelIso (f : r ≺i s) (g : s ≃r t) : r ≺i t :=
  transInitial f g.toInitialSeg

@[simp]
/--
theorem `transRelIso_apply` / 定理 `transRelIso_apply`

English:
theorem transRelIso_apply
  given: (f : r ≺i s) (g : s ≃r t) (a : α)
  statement: transRelIso f g a = g (f a)
  proof: rfl

@[simp]

中文:
定理 transRelIso_apply
  条件: (f : r ≺i s) (g : s ≃r t) (a : α)
  结论: transRelIso f g a = g (f a)
  证明: rfl

@[simp]
-/
theorem transRelIso_apply (f : r ≺i s) (g : s ≃r t) (a : α) : transRelIso f g a = g (f a) :=
  rfl

@[simp]
/--
theorem `transRelIso_top` / 定理 `transRelIso_top`

English:
theorem transRelIso_top
  given: (f : r ≺i s) (g : s ≃r t)
  statement: (transRelIso f g).top = g f.top
  proof: rfl

中文:
定理 transRelIso_top
  条件: (f : r ≺i s) (g : s ≃r t)
  结论: (transRelIso f g).top = g f.top
  证明: rfl
-/
theorem transRelIso_top (f : r ≺i s) (g : s ≃r t) : (transRelIso f g).top = g f.top :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWellOrder
  signature: β s] : Subsingleton (r ≺i s) where
  body: ext ((f : r ≼i s).eq g)

中文:
实例 [IsWellOrder
  签名: β s] : Subsingleton (r ≺i s) where
  定义体: ext ((f : r ≼i s).eq g)
-/
instance [IsWellOrder β s] : Subsingleton (r ≺i s) where
  allEq f g := ext ((f : r ≼i s).eq g)

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: [IsWellOrder β s] (f g : r ≺i s) (a)
  statement: f a = g a
  proof: by
  rw [Subsingleton.elim f g]

中文:
定理 eq
  条件: [IsWellOrder β s] (f g : r ≺i s) (a)
  结论: f a = g a
  证明: by
  rw [Subsingleton.elim f g]
-/
protected theorem eq [IsWellOrder β s] (f g : r ≺i s) (a) : f a = g a := by
  rw [Subsingleton.elim f g]

/--
theorem `top_eq` / 定理 `top_eq`

English:
theorem top_eq
  given: [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t)
  statement: f.top = g.top
  proof: by
  rw [Subsingleton.elim f (PrincipalSeg.relIsoTrans e g)]; rfl

中文:
定理 top_eq
  条件: [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t)
  结论: f.top = g.top
  证明: by
  rw [Subsingleton.elim f (PrincipalSeg.relIsoTrans e g)]; rfl

Depends on / 依赖: PrincipalSeg, PrincipalSeg.relIsoTrans, Subsingleton, Subsingleton.elim, relIsoTrans
-/
theorem top_eq [IsWellOrder γ t] (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top := by
  rw [Subsingleton.elim f (PrincipalSeg.relIsoTrans e g)]; rfl

/--
theorem `top_rel_top` / 定理 `top_rel_top`

English:
theorem top_rel_top
  statement: {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [IsWellOrder γ t]
  proof: by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

中文:
定理 top_rel_top
  结论: {r : α -> α -> 命题} {s : β -> β -> 命题} {t : γ -> γ -> 命题} [IsWellOrder γ t]
  证明: by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

Depends on / 依赖: PrincipalSeg, PrincipalSeg.lt_top, Subsingleton, Subsingleton.elim, f.trans, lt_top
-/
theorem top_rel_top {r : α -> α -> Prop} {s : β -> β -> Prop} {t : γ -> γ -> Prop} [IsWellOrder γ t]
    (f : r ≺i s) (g : s ≺i t) (h : r ≺i t) : t h.top g.top := by
  rw [Subsingleton.elim h (f.trans g)]
  apply PrincipalSeg.lt_top

/-- Any element of a well order yields a principal segment. -/
@[simps!]
/--
Definition of `ofElement` / `ofElement` 的定义

English:
definition ofElement
  signature: {α : Type*} (r : α -> α -> Prop) (a : α)
  body: ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun ⟨⟨_, h⟩, rfl⟩ => h, fun h => ⟨⟨_, h⟩, rfl⟩⟩⟩

@[simp]

中文:
定义 ofElement
  签名: {α : 类型} (r : α -> α -> 命题) (a : α)
  定义体: ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun ⟨⟨_, h⟩, rfl⟩ => h, fun h => ⟨⟨_, h⟩, rfl⟩⟩⟩

@[simp]

Depends on / 依赖: Subrel, Subrel.relEmbedding, relEmbedding
-/
def ofElement {α : Type*} (r : α -> α -> Prop) (a : α) : Subrel r (r · a) ≺i r :=
  ⟨Subrel.relEmbedding _ _, a, fun _ => ⟨fun ⟨⟨_, h⟩, rfl⟩ => h, fun h => ⟨⟨_, h⟩, rfl⟩⟩⟩

@[simp]
/--
theorem `ofElement_apply` / 定理 `ofElement_apply`

English:
theorem ofElement_apply
  given: {α : Type*} (r : α -> α -> Prop) (a : α) (b)
  statement: ofElement r a b = b.1
  proof: rfl

中文:
定理 ofElement_apply
  条件: {α : 类型} (r : α -> α -> 命题) (a : α) (b)
  结论: ofElement r a b = b.1
  证明: rfl
-/
theorem ofElement_apply {α : Type*} (r : α -> α -> Prop) (a : α) (b) : ofElement r a b = b.1 :=
  rfl

/-- For any principal segment `r ≺i s`, there is a `Subrel` of `s` order isomorphic to `r`. -/
@[simps! symm_apply]
/--
Definition of `subrelIso` / `subrelIso` 的定义

English:
definition subrelIso
  signature: (f : r ≺i s)
  body: RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
    (Equiv.subtypeEquivProp <| funext fun _ => propext f.mem_range_iff_rel), f.map_rel_iff⟩

@[simp]

中文:
定义 subrelIso
  签名: (f : r ≺i s)
  定义体: RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
    (Equiv.subtypeEquivProp <| funext fun _ => propext f.mem_range_iff_rel), f.map_rel_iff⟩

@[simp]

Depends on / 依赖: Equiv.ofInjective, Equiv.subtypeEquivProp, RelIso, RelIso.symm, f.injective, f.map_rel_iff, f.mem_range_iff_rel, injective, map_rel_iff, mem_range_iff_rel, ofInjective, propext, subtypeEquivProp
-/
noncomputable def subrelIso (f : r ≺i s) : Subrel s (s · f.top) ≃r r :=
  RelIso.symm ⟨(Equiv.ofInjective f f.injective).trans
    (Equiv.subtypeEquivProp <| funext fun _ => propext f.mem_range_iff_rel), f.map_rel_iff⟩

@[simp]
/--
theorem `apply_subrelIso` / 定理 `apply_subrelIso`

English:
theorem apply_subrelIso
  given: (f : r ≺i s) (b : {b // s b f.top})
  statement: f (f.subrelIso b) = b
  proof: Equiv.apply_ofInjective_symm f.injective _

@[simp]

中文:
定理 apply_subrelIso
  条件: (f : r ≺i s) (b : {b // s b f.top})
  结论: f (f.subrelIso b) = b
  证明: Equiv.apply_ofInjective_symm f.injective _

@[simp]

Depends on / 依赖: Equiv.apply_ofInjective_symm, apply_ofInjective_symm, f.injective, injective
-/
theorem apply_subrelIso (f : r ≺i s) (b : {b // s b f.top}) : f (f.subrelIso b) = b :=
  Equiv.apply_ofInjective_symm f.injective _

@[simp]
/--
theorem `subrelIso_apply` / 定理 `subrelIso_apply`

English:
theorem subrelIso_apply
  given: (f : r ≺i s) (a : α)
  statement: f.subrelIso ⟨f a, f.lt_top a⟩ = a
  proof: Equiv.ofInjective_symm_apply f.injective _

中文:
定理 subrelIso_apply
  条件: (f : r ≺i s) (a : α)
  结论: f.subrelIso ⟨f a, f.lt_top a⟩ = a
  证明: Equiv.ofInjective_symm_apply f.injective _

Depends on / 依赖: Equiv.ofInjective_symm_apply, f.injective, injective, ofInjective_symm_apply
-/
theorem subrelIso_apply (f : r ≺i s) (a : α) : f.subrelIso ⟨f a, f.lt_top a⟩ = a :=
  Equiv.ofInjective_symm_apply f.injective _

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (p : Set β) (f : r ≺i s) (H : forall a, f a in p) (H₂ : f.top in p)
  body: ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ => by simp [← f.mem_range_iff_rel]⟩

@[simp]

中文:
定义 codRestrict
  签名: (p : Set β) (f : r ≺i s) (H : 对任意 a, f a in p) (H₂ : f.top in p)
  定义体: ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ => by simp [← f.mem_range_iff_rel]⟩

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.codRestrict, codRestrict, f.mem_range_iff_rel, f.top, mem_range_iff_rel
-/
def codRestrict (p : Set β) (f : r ≺i s) (H : forall a, f a in p) (H₂ : f.top in p) :
    r ≺i Subrel s (· in p) :=
  ⟨RelEmbedding.codRestrict p f H, ⟨f.top, H₂⟩, fun ⟨_, _⟩ => by simp [← f.mem_range_iff_rel]⟩

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: (p) (f : r ≺i s) (H H₂ a)
  statement: codRestrict p f H H₂ a = ⟨f a, H a⟩
  proof: rfl

@[simp]

中文:
定理 codRestrict_apply
  条件: (p) (f : r ≺i s) (H H₂ a)
  结论: codRestrict p f H H₂ a = ⟨f a, H a⟩
  证明: rfl

@[simp]
-/
theorem codRestrict_apply (p) (f : r ≺i s) (H H₂ a) : codRestrict p f H H₂ a = ⟨f a, H a⟩ :=
  rfl

@[simp]
/--
theorem `codRestrict_top` / 定理 `codRestrict_top`

English:
theorem codRestrict_top
  given: (p) (f : r ≺i s) (H H₂)
  statement: (codRestrict p f H H₂).top = ⟨f.top, H₂⟩
  proof: rfl

中文:
定理 codRestrict_top
  条件: (p) (f : r ≺i s) (H H₂)
  结论: (codRestrict p f H H₂).top = ⟨f.top, H₂⟩
  证明: rfl
-/
theorem codRestrict_top (p) (f : r ≺i s) (H H₂) : (codRestrict p f H H₂).top = ⟨f.top, H₂⟩ :=
  rfl

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s b' b)
  body: { RelEmbedding.ofIsEmpty r s with
    top := b
    mem_range_iff_rel' := by simp [H] }

@[simp]

中文:
定义 ofIsEmpty
  签名: (r : α -> α -> 命题) [IsEmpty α] {b : β} (H : 对任意 b', ¬s b' b)
  定义体: { RelEmbedding.ofIsEmpty r s with
    top := b
    mem_range_iff_rel' := by simp [H] }

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.ofIsEmpty, mem_range_iff_rel, ofIsEmpty
-/
def ofIsEmpty (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s b' b) : r ≺i s :=
  { RelEmbedding.ofIsEmpty r s with
    top := b
    mem_range_iff_rel' := by simp [H] }

@[simp]
/--
theorem `ofIsEmpty_top` / 定理 `ofIsEmpty_top`

English:
theorem ofIsEmpty_top
  given: (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s b' b)
  proof: rfl

中文:
定理 ofIsEmpty_top
  条件: (r : α -> α -> 命题) [IsEmpty α] {b : β} (H : 对任意 b', ¬s b' b)
  证明: rfl
-/
theorem ofIsEmpty_top (r : α -> α -> Prop) [IsEmpty α] {b : β} (H : forall b', ¬s b' b) :
    (ofIsEmpty r H).top = b :=
  rfl

/--
Definition of `pemptyToPUnit` / `pemptyToPUnit` 的定义

English:
abbreviation pemptyToPUnit
  signature: : @emptyRelation PEmpty ≺i @emptyRelation PUnit
  body: (@ofIsEmpty _ _ emptyRelation _ _ PUnit.unit) fun _ => not_false

@[deprecated (since := "2026-02-08")] alias pemptyToPunit := pemptyToPUnit

中文:
缩写 pemptyToPUnit
  签名: : @emptyRelation PEmpty ≺i @emptyRelation PUnit
  定义体: (@ofIsEmpty _ _ emptyRelation _ _ PUnit.unit) fun _ => not_false

@[deprecated (since := "2026-02-08")] alias pemptyToPunit := pemptyToPUnit

Depends on / 依赖: PUnit.unit, emptyRelation, not_false, ofIsEmpty
-/
abbrev pemptyToPUnit : @emptyRelation PEmpty ≺i @emptyRelation PUnit :=
  (@ofIsEmpty _ _ emptyRelation _ _ PUnit.unit) fun _ => not_false

@[deprecated (since := "2026-02-08")] alias pemptyToPunit := pemptyToPUnit

/--
theorem `acc` / 定理 `acc`

English:
theorem acc
  given: [IsTrans β s] (f : r ≺i s) (a : α)
  statement: Acc r a ↔ Acc s (f a)
  proof: (f : r ≼i s).acc a

中文:
定理 acc
  条件: [IsTrans β s] (f : r ≺i s) (a : α)
  结论: Acc r a ↔ Acc s (f a)
  证明: (f : r ≼i s).acc a
-/
protected theorem acc [IsTrans β s] (f : r ≺i s) (a : α) : Acc r a ↔ Acc s (f a) :=
  (f : r ≼i s).acc a

end PrincipalSeg

/--
theorem `wellFounded_iff_principalSeg` / 定理 `wellFounded_iff_principalSeg`

English:
theorem wellFounded_iff_principalSeg
  given: {β : Type u} {s : β -> β -> Prop} [IsTrans β s]
  proof: ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩

中文:
定理 wellFounded_iff_principalSeg
  条件: {β : 类型u} {s : β -> β -> 命题} [IsTrans β s]
  证明: ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩

Depends on / 依赖: PrincipalSeg, PrincipalSeg.ofElement, RelHomClass, RelHomClass.wellFounded, f.toRelEmbedding, ofElement, toRelEmbedding, wellFounded, wellFounded_iff_wellFounded_subrel, wellFounded_iff_wellFounded_subrel.mpr
-/
theorem wellFounded_iff_principalSeg {β : Type u} {s : β -> β -> Prop} [IsTrans β s] :
    WellFounded s ↔ forall (α : Type u) (r : α -> α -> Prop) (_ : r ≺i s), WellFounded r :=
  ⟨fun wf _ _ f => RelHomClass.wellFounded f.toRelEmbedding wf, fun h =>
    wellFounded_iff_wellFounded_subrel.mpr fun b => h _ _ (PrincipalSeg.ofElement s b)⟩

/-! ### Properties of initial and principal segments -/

namespace InitialSeg

open scoped Classical in
/--
Definition of `principalSumRelIso` / `principalSumRelIso` 的定义

English:
definition principalSumRelIso
  signature: [IsWellOrder β s] (f : r ≼i s)
  body: if h : Surjective f
    then Sum.inr (RelIso.ofSurjective f h)
    else Sum.inl (f.toPrincipalSeg h)

中文:
定义 principalSumRelIso
  签名: [IsWellOrder β s] (f : r ≼i s)
  定义体: if h : Surjective f
    then Sum.inr (RelIso.ofSurjective f h)
    else Sum.inl (f.toPrincipalSeg h)

Depends on / 依赖: RelIso, RelIso.ofSurjective, Sum.inl, Sum.inr, Surjective, f.toPrincipalSeg, ofSurjective, toPrincipalSeg
-/
noncomputable def principalSumRelIso [IsWellOrder β s] (f : r ≼i s) : (r ≺i s) oplus (r ≃r s) :=
  if h : Surjective f
    then Sum.inr (RelIso.ofSurjective f h)
    else Sum.inl (f.toPrincipalSeg h)

/--
Definition of `transPrincipal` / `transPrincipal` 的定义

English:
definition transPrincipal
  signature: [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t)
  body: match f.principalSumRelIso with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.relIsoTrans f' g

@[simp]

中文:
定义 transPrincipal
  签名: [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t)
  定义体: match f.principalSumRelIso with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.relIsoTrans f' g

@[simp]

Depends on / 依赖: PrincipalSeg, PrincipalSeg.relIsoTrans, Sum.inl, Sum.inr, f.principalSumRelIso, principalSumRelIso, relIsoTrans
-/
noncomputable def transPrincipal [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) :
    r ≺i t :=
  match f.principalSumRelIso with
  | Sum.inl f' => f'.trans g
  | Sum.inr f' => PrincipalSeg.relIsoTrans f' g

@[simp]
/--
theorem `transPrincipal_apply` / 定理 `transPrincipal_apply`

English:
theorem transPrincipal_apply
  given: [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α)
  proof: by
  rw [InitialSeg.transPrincipal]
  obtain f' | f' := f.principalSumRelIso
  · rw [PrincipalSeg.trans_apply, f.eq_principalSeg]
  · rw [PrincipalSeg.relIsoTrans_apply, f.eq_relIso]

中文:
定理 transPrincipal_apply
  条件: [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α)
  证明: by
  rw [InitialSeg.transPrincipal]
  obtain f' | f' := f.principalSumRelIso
  · rw [PrincipalSeg.trans_apply, f.eq_principalSeg]
  · rw [PrincipalSeg.relIsoTrans_apply, f.eq_relIso]

Depends on / 依赖: HasCoeffs, HasCoeffs.of_isScalarTower, InitialSeg, InitialSeg.transPrincipal, PrincipalSeg, PrincipalSeg.relIsoTrans_apply, PrincipalSeg.trans_apply, eq_principalSeg, eq_relIso, f.eq_principalSeg, f.eq_relIso, f.principalSumRelIso, of_isScalarTower, principalSumRelIso, relIsoTrans_apply, transPrincipal, trans_apply
-/
theorem transPrincipal_apply [IsWellOrder β s] [IsTrans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) :
    f.transPrincipal g a = g (f a) := by
  rw [InitialSeg.transPrincipal]
  obtain f' | f' := f.principalSumRelIso
  · rw [PrincipalSeg.trans_apply, f.eq_principalSeg]
  · rw [PrincipalSeg.relIsoTrans_apply, f.eq_relIso]

/--
theorem `exists_sum_relIso` / 定理 `exists_sum_relIso`

English:
theorem exists_sum_relIso
  given: {β : Type u} {s : β -> β -> Prop} [IsWellOrder β s] (f : r ≼i s)
  proof: by
  classical
  obtain f | f := f.principalSumRelIso
  · exact ⟨_, _, inferInstance,
⟨(RelIso.sumLexCongr f.subrelIso.symm (.refl _)).trans .sumLexComplLeft ..⟩⟩
  · exact ⟨PEmpty, nofun, inferInstance, ⟨(RelIso.sumLexEmpty r _).trans f⟩⟩

中文:
定理 exists_sum_relIso
  条件: {β : 类型u} {s : β -> β -> 命题} [IsWellOrder β s] (f : r ≼i s)
  证明: by
  classical
  obtain f | f := f.principalSumRelIso
  · exact ⟨_, _, inferInstance,
⟨(RelIso.sumLexCongr f.subrelIso.symm (.refl _)).trans .sumLexComplLeft ..⟩⟩
  · exact ⟨PEmpty, nofun, inferInstance, ⟨(RelIso.sumLexEmpty r _).trans f⟩⟩

Depends on / 依赖: PEmpty, RelIso, RelIso.sumLexCongr, RelIso.sumLexEmpty, classical, f.principalSumRelIso, f.subrelIso.symm, principalSumRelIso, subrelIso, sumLexComplLeft, sumLexCongr, sumLexEmpty
-/
theorem exists_sum_relIso {β : Type u} {s : β -> β -> Prop} [IsWellOrder β s] (f : r ≼i s) :
    exists (γ : Type u) (t : γ -> γ -> Prop), IsWellOrder γ t ∧ Nonempty (Sum.Lex r t ≃r s) := by
  classical
  obtain f | f := f.principalSumRelIso
  · exact ⟨_, _, inferInstance,
⟨(RelIso.sumLexCongr f.subrelIso.symm (.refl _)).trans .sumLexComplLeft ..⟩⟩
  · exact ⟨PEmpty, nofun, inferInstance, ⟨(RelIso.sumLexEmpty r _).trans f⟩⟩

end InitialSeg

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def collapseF [IsWellOrder β s] (f : r ↪r s)
  body: (RelEmbedding.isWellFounded f).fix _ fun a IH =>
    have H : f a in { b | forall a h, s (IH a h).1 b } :=
      fun b h => trans_trichotomous_left (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ H⟩

中文:
定义 noncomputable
  签名: def collapseF [IsWellOrder β s] (f : r ↪r s)
  定义体: (RelEmbedding.isWellFounded f).fix _ fun a IH =>
    have H : f a in { b | forall a h, s (IH a h).1 b } :=
      fun b h => trans_trichotomous_left (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ H⟩
-/
private noncomputable def collapseF [IsWellOrder β s] (f : r ↪r s) : Π a, { b // ¬s (f a) b } :=
  (RelEmbedding.isWellFounded f).fix _ fun a IH =>
    have H : f a in { b | forall a h, s (IH a h).1 b } :=
      fun b h => trans_trichotomous_left (IH b h).2 (f.map_rel_iff.2 h)
    ⟨_, IsWellFounded.wf.not_lt_min _ H⟩

/--
theorem `collapseF_lt` / 定理 `collapseF_lt`

English:
theorem collapseF_lt
  given: [IsWellOrder β s] (f : r ↪r s) {a : α}
  proof: by
  change _ in { b | forall a', r a' a -> s (collapseF f a') b }
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _

中文:
定理 collapseF_lt
  条件: [IsWellOrder β s] (f : r ↪r s) {a : α}
  证明: by
  change _ in { b | forall a', r a' a -> s (collapseF f a') b }
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _
-/
private theorem collapseF_lt [IsWellOrder β s] (f : r ↪r s) {a : α} :
    forall {a'}, r a' a -> s (collapseF f a') (collapseF f a) := by
  change _ in { b | forall a', r a' a -> s (collapseF f a') b }
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.min_mem _ _ _

/--
theorem `collapseF_not_lt` / 定理 `collapseF_not_lt`

English:
theorem collapseF_not_lt
  statement: [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
  proof: by
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ {b | forall a', r a' a -> s (collapseF f a') b} h

中文:
定理 collapseF_not_lt
  结论: [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
  证明: by
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ {b | forall a', r a' a -> s (collapseF f a') b} h
-/
private theorem collapseF_not_lt [IsWellOrder β s] (f : r ↪r s) (a : α) {b}
    (h : forall a', r a' a -> s (collapseF f a') b) : ¬s b (collapseF f a) := by
  rw [collapseF]; rw [IsWellFounded.fix_eq]
  dsimp only
  exact WellFounded.not_lt_min _ {b | forall a', r a' a -> s (collapseF f a') b} h

/-- Construct an initial segment embedding `r ≼i s` by "filling in the gaps". That is, each
subsequent element in `α` is mapped to the least element in `β` that hasn't been used yet.

This construction is guaranteed to work as long as there exists some relation embedding `r ↪r s`. -/
@[no_expose]
/--
Definition of `RelEmbedding.collapse` / `RelEmbedding.collapse` 的定义

English:
definition RelEmbedding.collapse
  signature: [IsWellOrder β s] (f : r ↪r s)
  body: have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h => by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h => ?_

中文:
定义 RelEmbedding.collapse
  签名: [IsWellOrder β s] (f : r ↪r s)
  定义体: have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h => by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h => ?_

Depends on / 依赖: H.wf.has_min, RelEmbedding, RelEmbedding.isWellOrder, RelEmbedding.ofMonotone, collapseF, collapseF_lt, collapseF_not_lt, has_min, isWellOrder, ofMonotone, trichotomous_of
-/
noncomputable def RelEmbedding.collapse [IsWellOrder β s] (f : r ↪r s) : r ≼i s :=
  have H := RelEmbedding.isWellOrder f
  ⟨RelEmbedding.ofMonotone _ fun a b => collapseF_lt f, fun a b h => by
    obtain ⟨m, hm, hm'⟩ := H.wf.has_min { a | ¬s _ b } ⟨_, asymm h⟩
    use m
    obtain lt | rfl | gt := trichotomous_of s b (collapseF f m)
    · refine (collapseF_not_lt f m (fun c h => ?_) lt).elim
      by_contra hn
      exact hm' _ hn h
    · rfl
    · exact (hm gt).elim⟩

/--
Definition of `InitialSeg.total` / `InitialSeg.total` 的定义

English:
definition InitialSeg.total
  signature: (r s) [IsWellOrder α r] [IsWellOrder β s]
  body: match (leAdd r s).principalSumRelIso,
    (RelEmbedding.sumLexInr r s).collapse.principalSumRelIso with
| Sum.inl f, Sum.inr g => Sum.inl f.transRelIso g.symm
| Sum.inr f, Sum.inl g => Sum.inr g.transRelIso f.symm
| Sum.inr f, Sum.inr g => Sum.inl (f.trans g.symm).toInitialSeg
| Sum.inl f, Sum.inl g

中文:
定义 InitialSeg.total
  签名: (r s) [IsWellOrder α r] [IsWellOrder β s]
  定义体: match (leAdd r s).principalSumRelIso,
    (RelEmbedding.sumLexInr r s).collapse.principalSumRelIso with
| Sum.inl f, Sum.inr g => Sum.inl f.transRelIso g.symm
| Sum.inr f, Sum.inl g => Sum.inr g.transRelIso f.symm
| Sum.inr f, Sum.inr g => Sum.inl (f.trans g.symm).toInitialSeg
| Sum.inl f, Sum.inl g

Depends on / 依赖: Classical, Classical.choice, RelEmbedding, RelEmbedding.sumLexInr, Sum.Lex, Sum.inl, Sum.inr, _root_, _root_.trans, choice, codRestrict, collapse, collapse.principalSumRelIso, f.codRestrict, f.lt_top, f.symm, f.top, f.trans, f.transRelIso, g.subr
-/
noncomputable def InitialSeg.total (r s) [IsWellOrder α r] [IsWellOrder β s] :
    (r ≼i s) oplus (s ≼i r) :=
  match (leAdd r s).principalSumRelIso,
    (RelEmbedding.sumLexInr r s).collapse.principalSumRelIso with
| Sum.inl f, Sum.inr g => Sum.inl f.transRelIso g.symm
| Sum.inr f, Sum.inl g => Sum.inr g.transRelIso f.symm
| Sum.inr f, Sum.inr g => Sum.inl (f.trans g.symm).toInitialSeg
| Sum.inl f, Sum.inl g => Classical.choice by
      obtain h | h | h := trichotomous_of (Sum.Lex r s) f.top g.top
· exact ⟨Sum.inl (f.codRestrict {x | Sum.Lex r s x g.top}
          (fun a => _root_.trans (f.lt_top a) h) h).transRelIso g.subrelIso⟩
      · let f := f.subrelIso
        rw [h] at f
exact ⟨Sum.inl (f.symm.trans g.subrelIso).toInitialSeg⟩
· exact ⟨Sum.inr (g.codRestrict {x | Sum.Lex r s x f.top}
          (fun a => _root_.trans (g.lt_top a) h) h).transRelIso f.subrelIso⟩

/-! ### Initial or principal segments with `<` -/

namespace InitialSeg

/-- An order isomorphism is an initial segment -/
@[simps!]
/--
Definition of `_root_.OrderIso.toInitialSeg` / `_root_.OrderIso.toInitialSeg` 的定义

English:
definition _root_.OrderIso.toInitialSeg
  signature: [Preorder α] [Preorder β] (f : α ≃o β)
  body: f.toRelIsoLT.toInitialSeg

中文:
定义 _root_.OrderIso.toInitialSeg
  签名: [Preorder α] [Preorder β] (f : α ≃o β)
  定义体: f.toRelIsoLT.toInitialSeg

Depends on / 依赖: f.toRelIsoLT.toInitialSeg, toInitialSeg, toRelIsoLT
-/
def _root_.OrderIso.toInitialSeg [Preorder α] [Preorder β] (f : α ≃o β) : α <=i β :=
  f.toRelIsoLT.toInitialSeg

variable [PartialOrder β] {a a' : α} {b : β}

/--
theorem `mem_range_of_le` / 定理 `mem_range_of_le`

English:
theorem mem_range_of_le
  given: [LT α] (f : α <=i β) (h : b <= f a)
  statement: b in Set.range f
  proof: by
  obtain rfl | hb := h.eq_or_lt
  exacts [⟨a, rfl⟩, f.mem_range_of_rel hb]

中文:
定理 mem_range_of_le
  条件: [LT α] (f : α <=i β) (h : b <= f a)
  结论: b in Set.range f
  证明: by
  obtain rfl | hb := h.eq_or_lt
  exacts [⟨a, rfl⟩, f.mem_range_of_rel hb]

Depends on / 依赖: eq_or_lt, exacts, f.mem_range_of_rel, h.eq_or_lt, mem_range_of_rel
-/
theorem mem_range_of_le [LT α] (f : α <=i β) (h : b <= f a) : b in Set.range f := by
  obtain rfl | hb := h.eq_or_lt
  exacts [⟨a, rfl⟩, f.mem_range_of_rel hb]

/--
theorem `isLowerSet_range` / 定理 `isLowerSet_range`

English:
theorem isLowerSet_range
  given: [LT α] (f : α <=i β)
  statement: IsLowerSet (Set.range f)
  proof: by
  rintro _ b h ⟨a, rfl⟩
  exact mem_range_of_le f h

中文:
定理 isLowerSet_range
  条件: [LT α] (f : α <=i β)
  结论: IsLowerSet (Set.range f)
  证明: by
  rintro _ b h ⟨a, rfl⟩
  exact mem_range_of_le f h

Depends on / 依赖: mem_range_of_le
-/
theorem isLowerSet_range [LT α] (f : α <=i β) : IsLowerSet (Set.range f) := by
  rintro _ b h ⟨a, rfl⟩
  exact mem_range_of_le f h

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: [PartialOrder α] (f : α <=i β)
  statement: f a <= f a' ↔ a <= a'
  proof: f.toOrderEmbedding.le_iff_le

中文:
定理 le_iff_le
  条件: [PartialOrder α] (f : α <=i β)
  结论: f a <= f a' ↔ a <= a'
  证明: f.toOrderEmbedding.le_iff_le

Depends on / 依赖: f.toOrderEmbedding.le_iff_le, le_iff_le, toOrderEmbedding
-/
theorem le_iff_le [PartialOrder α] (f : α <=i β) : f a <= f a' ↔ a <= a' :=
  f.toOrderEmbedding.le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: [PartialOrder α] (f : α <=i β)
  statement: f a < f a' ↔ a < a'
  proof: f.toOrderEmbedding.lt_iff_lt

中文:
定理 lt_iff_lt
  条件: [PartialOrder α] (f : α <=i β)
  结论: f a < f a' ↔ a < a'
  证明: f.toOrderEmbedding.lt_iff_lt

Depends on / 依赖: f.toOrderEmbedding.lt_iff_lt, lt_iff_lt, toOrderEmbedding
-/
theorem lt_iff_lt [PartialOrder α] (f : α <=i β) : f a < f a' ↔ a < a' :=
  f.toOrderEmbedding.lt_iff_lt

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: [PartialOrder α] (f : α <=i β)
  statement: Monotone f
  proof: f.toOrderEmbedding.monotone

中文:
定理 monotone
  条件: [PartialOrder α] (f : α <=i β)
  结论: Monotone f
  证明: f.toOrderEmbedding.monotone

Depends on / 依赖: f.toOrderEmbedding.monotone, monotone, toOrderEmbedding
-/
theorem monotone [PartialOrder α] (f : α <=i β) : Monotone f :=
  f.toOrderEmbedding.monotone

/--
theorem `strictMono` / 定理 `strictMono`

English:
theorem strictMono
  given: [PartialOrder α] (f : α <=i β)
  statement: StrictMono f
  proof: f.toOrderEmbedding.strictMono

@[simp]

中文:
定理 strictMono
  条件: [PartialOrder α] (f : α <=i β)
  结论: StrictMono f
  证明: f.toOrderEmbedding.strictMono

@[simp]

Depends on / 依赖: f.toOrderEmbedding.strictMono, strictMono, toOrderEmbedding
-/
theorem strictMono [PartialOrder α] (f : α <=i β) : StrictMono f :=
  f.toOrderEmbedding.strictMono

@[simp]
/--
theorem `isMin_apply_iff` / 定理 `isMin_apply_iff`

English:
theorem isMin_apply_iff
  given: [PartialOrder α] (f : α <=i β)
  statement: IsMin (f a) ↔ IsMin a
  proof: by
  refine ⟨StrictMono.isMin_of_apply f.strictMono, fun h b hb => ?_⟩
  obtain ⟨x, rfl⟩ := f.mem_range_of_le hb
  rw [f.le_iff_le] at hb ⊢
  exact h hb

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]

中文:
定理 isMin_apply_iff
  条件: [PartialOrder α] (f : α <=i β)
  结论: IsMin (f a) ↔ IsMin a
  证明: by
  refine ⟨StrictMono.isMin_of_apply f.strictMono, fun h b hb => ?_⟩
  obtain ⟨x, rfl⟩ := f.mem_range_of_le hb
  rw [f.le_iff_le] at hb ⊢
  exact h hb

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]

Depends on / 依赖: StrictMono, StrictMono.isMin_of_apply, f.le_iff_le, f.mem_range_of_le, f.strictMono, isMin_of_apply, le_iff_le, mem_range_of_le, strictMono
-/
theorem isMin_apply_iff [PartialOrder α] (f : α <=i β) : IsMin (f a) ↔ IsMin a := by
  refine ⟨StrictMono.isMin_of_apply f.strictMono, fun h b hb => ?_⟩
  obtain ⟨x, rfl⟩ := f.mem_range_of_le hb
  rw [f.le_iff_le] at hb ⊢
  exact h hb

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <=i β)
  statement: f ⊥ = ⊥
  proof: (map_isMin f isMin_bot).eq_bot

中文:
定理 map_bot
  条件: [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <=i β)
  结论: f ⊥ = ⊥
  证明: (map_isMin f isMin_bot).eq_bot

Depends on / 依赖: eq_bot, isMin_bot, map_isMin
-/
theorem map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <=i β) : f ⊥ = ⊥ :=
  (map_isMin f isMin_bot).eq_bot

/--
theorem `image_Iio` / 定理 `image_Iio`

English:
theorem image_Iio
  given: [PartialOrder α] (f : α <=i β) (a : α)
  statement: f '' Set.Iio a = Set.Iio (f a)
  proof: f.toOrderEmbedding.image_Iio f.isLowerSet_range a

中文:
定理 image_Iio
  条件: [PartialOrder α] (f : α <=i β) (a : α)
  结论: f '' Set.Iio a = Set.Iio (f a)
  证明: f.toOrderEmbedding.image_Iio f.isLowerSet_range a

Depends on / 依赖: f.isLowerSet_range, f.toOrderEmbedding.image_Iio, image_Iio, isLowerSet_range, toOrderEmbedding
-/
theorem image_Iio [PartialOrder α] (f : α <=i β) (a : α) : f '' Set.Iio a = Set.Iio (f a) :=
  f.toOrderEmbedding.image_Iio f.isLowerSet_range a

/--
theorem `le_apply_iff` / 定理 `le_apply_iff`

English:
theorem le_apply_iff
  given: [PartialOrder α] (f : α <=i β)
  statement: b <= f a ↔ exists c <= a, f c = b
  proof: by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_le h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.le_iff_le] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.monotone hc

中文:
定理 le_apply_iff
  条件: [PartialOrder α] (f : α <=i β)
  结论: b <= f a ↔ 存在 c <= a, f c = b
  证明: by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_le h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.le_iff_le] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.monotone hc

Depends on / 依赖: f.le_iff_le, f.mem_range_of_le, f.monotone, le_iff_le, mem_range_of_le, monotone
-/
theorem le_apply_iff [PartialOrder α] (f : α <=i β) : b <= f a ↔ exists c <= a, f c = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_le h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.le_iff_le] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.monotone hc

/--
theorem `lt_apply_iff` / 定理 `lt_apply_iff`

English:
theorem lt_apply_iff
  given: [PartialOrder α] (f : α <=i β)
  statement: b < f a ↔ exists a' < a, f a' = b
  proof: by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_rel h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.lt_iff_lt] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.strictMono hc

中文:
定理 lt_apply_iff
  条件: [PartialOrder α] (f : α <=i β)
  结论: b < f a ↔ 存在 a' < a, f a' = b
  证明: by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := f.mem_range_of_rel h
    refine ⟨c, ?_, hc⟩
    rwa [← hc, f.lt_iff_lt] at h
  · rintro ⟨c, hc, rfl⟩
    exact f.strictMono hc

Depends on / 依赖: f.lt_iff_lt, f.mem_range_of_rel, f.strictMono, lt_iff_lt, mem_range_of_rel, strictMono
-/
theorem lt_apply_iff [PartialOrder α] (f : α <=i β) : b < f a ↔ exists a' < a, f a' = b := by
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

/--
theorem `mem_range_of_le` / 定理 `mem_range_of_le`

English:
theorem mem_range_of_le
  given: [LT α] (f : α <i β) (h : b <= f a)
  statement: b in Set.range f
  proof: (f : α <=i β).mem_range_of_le h

中文:
定理 mem_range_of_le
  条件: [LT α] (f : α <i β) (h : b <= f a)
  结论: b in Set.range f
  证明: (f : α <=i β).mem_range_of_le h

Depends on / 依赖: mem_range_of_le
-/
theorem mem_range_of_le [LT α] (f : α <i β) (h : b <= f a) : b in Set.range f :=
  (f : α <=i β).mem_range_of_le h

/--
theorem `range_eq_Iio` / 定理 `range_eq_Iio`

English:
theorem range_eq_Iio
  given: [LT α] (f : α <i β)
  statement: Set.range f = Set.Iio f.top
  proof: f.range_eq

中文:
定理 range_eq_Iio
  条件: [LT α] (f : α <i β)
  结论: Set.range f = Set.Iio f.top
  证明: f.range_eq

Depends on / 依赖: f.range_eq, range_eq
-/
theorem range_eq_Iio [LT α] (f : α <i β) : Set.range f = Set.Iio f.top :=
  f.range_eq

/--
theorem `isLowerSet_range` / 定理 `isLowerSet_range`

English:
theorem isLowerSet_range
  given: [LT α] (f : α <i β)
  statement: IsLowerSet (Set.range f)
  proof: (f : α <=i β).isLowerSet_range

中文:
定理 isLowerSet_range
  条件: [LT α] (f : α <i β)
  结论: IsLowerSet (Set.range f)
  证明: (f : α <=i β).isLowerSet_range

Depends on / 依赖: isLowerSet_range
-/
theorem isLowerSet_range [LT α] (f : α <i β) : IsLowerSet (Set.range f) :=
  (f : α <=i β).isLowerSet_range

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  given: [PartialOrder α] (f : α <i β)
  statement: f a <= f a' ↔ a <= a'
  proof: (f : α <=i β).le_iff_le

中文:
定理 le_iff_le
  条件: [PartialOrder α] (f : α <i β)
  结论: f a <= f a' ↔ a <= a'
  证明: (f : α <=i β).le_iff_le

Depends on / 依赖: le_iff_le
-/
theorem le_iff_le [PartialOrder α] (f : α <i β) : f a <= f a' ↔ a <= a' :=
  (f : α <=i β).le_iff_le

-- TODO: this would follow immediately if we had a `RelEmbeddingClass`
@[simp]
/--
theorem `lt_iff_lt` / 定理 `lt_iff_lt`

English:
theorem lt_iff_lt
  given: [PartialOrder α] (f : α <i β)
  statement: f a < f a' ↔ a < a'
  proof: (f : α <=i β).lt_iff_lt

中文:
定理 lt_iff_lt
  条件: [PartialOrder α] (f : α <i β)
  结论: f a < f a' ↔ a < a'
  证明: (f : α <=i β).lt_iff_lt

Depends on / 依赖: lt_iff_lt
-/
theorem lt_iff_lt [PartialOrder α] (f : α <i β) : f a < f a' ↔ a < a' :=
  (f : α <=i β).lt_iff_lt

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: [PartialOrder α] (f : α <i β)
  statement: Monotone f
  proof: (f : α <=i β).monotone

中文:
定理 monotone
  条件: [PartialOrder α] (f : α <i β)
  结论: Monotone f
  证明: (f : α <=i β).monotone

Depends on / 依赖: monotone
-/
theorem monotone [PartialOrder α] (f : α <i β) : Monotone f :=
  (f : α <=i β).monotone

/--
theorem `strictMono` / 定理 `strictMono`

English:
theorem strictMono
  given: [PartialOrder α] (f : α <i β)
  statement: StrictMono f
  proof: (f : α <=i β).strictMono

@[simp]

中文:
定理 strictMono
  条件: [PartialOrder α] (f : α <i β)
  结论: StrictMono f
  证明: (f : α <=i β).strictMono

@[simp]

Depends on / 依赖: HasCoeffs, P.toPresentation.HasCoeffs, strictMono, toPresentation
-/
theorem strictMono [PartialOrder α] (f : α <i β) : StrictMono f :=
  (f : α <=i β).strictMono

@[simp]
/--
theorem `isMin_apply_iff` / 定理 `isMin_apply_iff`

English:
theorem isMin_apply_iff
  given: [PartialOrder α] (f : α <i β)
  statement: IsMin (f a) ↔ IsMin a
  proof: (f : α <=i β).isMin_apply_iff

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]

中文:
定理 isMin_apply_iff
  条件: [PartialOrder α] (f : α <i β)
  结论: IsMin (f a) ↔ IsMin a
  证明: (f : α <=i β).isMin_apply_iff

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]

Depends on / 依赖: isMin_apply_iff
-/
theorem isMin_apply_iff [PartialOrder α] (f : α <i β) : IsMin (f a) ↔ IsMin a :=
  (f : α <=i β).isMin_apply_iff

alias ⟨_, map_isMin⟩ := isMin_apply_iff

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <i β)
  statement: f ⊥ = ⊥
  proof: (f : α <=i β).map_bot

中文:
定理 map_bot
  条件: [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <i β)
  结论: f ⊥ = ⊥
  证明: (f : α <=i β).map_bot

Depends on / 依赖: map_bot
-/
theorem map_bot [PartialOrder α] [OrderBot α] [OrderBot β] (f : α <i β) : f ⊥ = ⊥ :=
  (f : α <=i β).map_bot

/--
theorem `image_Iio` / 定理 `image_Iio`

English:
theorem image_Iio
  given: [PartialOrder α] (f : α <i β) (a : α)
  statement: f '' Set.Iio a = Set.Iio (f a)
  proof: (f : α <=i β).image_Iio a

中文:
定理 image_Iio
  条件: [PartialOrder α] (f : α <i β) (a : α)
  结论: f '' Set.Iio a = Set.Iio (f a)
  证明: (f : α <=i β).image_Iio a

Depends on / 依赖: image_Iio
-/
theorem image_Iio [PartialOrder α] (f : α <i β) (a : α) : f '' Set.Iio a = Set.Iio (f a) :=
  (f : α <=i β).image_Iio a

/--
theorem `le_apply_iff` / 定理 `le_apply_iff`

English:
theorem le_apply_iff
  given: [PartialOrder α] (f : α <i β)
  statement: b <= f a ↔ exists c <= a, f c = b
  proof: (f : α <=i β).le_apply_iff

中文:
定理 le_apply_iff
  条件: [PartialOrder α] (f : α <i β)
  结论: b <= f a ↔ 存在 c <= a, f c = b
  证明: (f : α <=i β).le_apply_iff

Depends on / 依赖: le_apply_iff
-/
theorem le_apply_iff [PartialOrder α] (f : α <i β) : b <= f a ↔ exists c <= a, f c = b :=
  (f : α <=i β).le_apply_iff

/--
theorem `lt_apply_iff` / 定理 `lt_apply_iff`

English:
theorem lt_apply_iff
  given: [PartialOrder α] (f : α <i β)
  statement: b < f a ↔ exists a' < a, f a' = b
  proof: (f : α <=i β).lt_apply_iff

中文:
定理 lt_apply_iff
  条件: [PartialOrder α] (f : α <i β)
  结论: b < f a ↔ 存在 a' < a, f a' = b
  证明: (f : α <=i β).lt_apply_iff

Depends on / 依赖: lt_apply_iff
-/
theorem lt_apply_iff [PartialOrder α] (f : α <i β) : b < f a ↔ exists a' < a, f a' = b :=
  (f : α <=i β).lt_apply_iff

end PrincipalSeg
