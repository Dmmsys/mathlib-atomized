/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice

/-! # Semiquotients

A data type for semiquotients, which are classically equivalent to
nonempty sets, but are useful for programming; the idea is that
a semiquotient set `S` represents some (particular but unknown)
element of `S`. This can be used to model nondeterministic functions,
which return something in a range of values (represented by the
predicate `S`) but are not completely determined.
-/

@[expose] public section


/--
Definition of `Semiquot` / `Semiquot` 的定义

English:
structure Semiquot
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 Semiquot
  参数: (α : 类型)
  (无附加公理)
-/
structure Semiquot (α : Type*) where mk' ::
  /-- Set containing some element of `α` -/
  s : Set α
  /-- Assertion of non-emptiness via `Trunc` -/
  val : Trunc s

namespace Semiquot

variable {α : Type*} {β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Semiquot α)
  body: ⟨fun q a => a in q.s⟩

中文:
实例 :
  签名: Membership α (Semiquot α)
  定义体: ⟨fun q a => a in q.s⟩
-/
instance : Membership α (Semiquot α) :=
  ⟨fun q a => a in q.s⟩

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {a : α} {s : Set α} (h : a in s)
  body: ⟨s, Trunc.mk ⟨a, h⟩⟩

中文:
定义 mk
  签名: {a : α} {s : Set α} (h : a in s)
  定义体: ⟨s, Trunc.mk ⟨a, h⟩⟩

Depends on / 依赖: Trunc.mk
-/
def mk {a : α} {s : Set α} (h : a in s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩

/--
theorem `ext_s` / 定理 `ext_s`

English:
theorem ext_s
  given: {q₁ q₂ : Semiquot α}
  statement: q₁ = q₂ ↔ q₁.s = q₂.s
  proof: by
  refine ⟨congr_arg _, fun h => ?_⟩
  obtain ⟨_, v₁⟩ := q₁; obtain ⟨_, v₂⟩ := q₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂

中文:
定理 ext_s
  条件: {q₁ q₂ : Semiquot α}
  结论: q₁ = q₂ ↔ q₁.s = q₂.s
  证明: by
  refine ⟨congr_arg _, fun h => ?_⟩
  obtain ⟨_, v₁⟩ := q₁; obtain ⟨_, v₂⟩ := q₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂

Depends on / 依赖: Set.Elem, Subsingleton, Subsingleton.helim, congr_arg
-/
theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s := by
  refine ⟨congr_arg _, fun h => ?_⟩
  obtain ⟨_, v₁⟩ := q₁; obtain ⟨_, v₂⟩ := q₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {q₁ q₂ : Semiquot α}
  statement: q₁ = q₂ ↔ forall a, a in q₁ ↔ a in q₂
  proof: ext_s.trans Set.ext_iff

中文:
定理 ext
  条件: {q₁ q₂ : Semiquot α}
  结论: q₁ = q₂ ↔ 对任意 a, a in q₁ ↔ a in q₂
  证明: ext_s.trans Set.ext_iff

Depends on / 依赖: Set.ext_iff, ext_iff, ext_s, ext_s.trans
-/
theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ forall a, a in q₁ ↔ a in q₂ :=
  ext_s.trans Set.ext_iff

/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  given: (q : Semiquot α)
  statement: exists a, a in q
  proof: let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩

中文:
定理 exists_mem
  条件: (q : Semiquot α)
  结论: 存在 a, a in q
  证明: let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩

Depends on / 依赖: exists_rep
-/
theorem exists_mem (q : Semiquot α) : exists a, a in q :=
  let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩

/--
theorem `eq_mk_of_mem` / 定理 `eq_mk_of_mem`

English:
theorem eq_mk_of_mem
  given: {q : Semiquot α} {a : α} (h : a in q)
  statement: q = @mk _ a q.1 h
  proof: ext_s.2 rfl

中文:
定理 eq_mk_of_mem
  条件: {q : Semiquot α} {a : α} (h : a in q)
  结论: q = @mk _ a q.1 h
  证明: ext_s.2 rfl

Depends on / 依赖: ext_s
-/
theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a in q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (q : Semiquot α)
  statement: q.s.Nonempty
  proof: q.exists_mem

中文:
定理 nonempty
  条件: (q : Semiquot α)
  结论: q.s.Nonempty
  证明: q.exists_mem

Depends on / 依赖: exists_mem, q.exists_mem
-/
theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem

/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: mk (Set.mem_singleton a)

@[simp]

中文:
定义 pure
  签名: (a : α)
  定义体: mk (Set.mem_singleton a)

@[simp]
-/
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)

@[simp]
/--
theorem `mem_pure'` / 定理 `mem_pure'`

English:
theorem mem_pure'
  given: {a b : α}
  statement: a in Semiquot.pure b ↔ a = b
  proof: Set.mem_singleton_iff

中文:
定理 mem_pure'
  条件: {a b : α}
  结论: a in Semiquot.pure b ↔ a = b
  证明: Set.mem_singleton_iff

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem mem_pure' {a b : α} : a in Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff

/--
Definition of `blur'` / `blur'` 的定义

English:
definition blur'
  signature: (q : Semiquot α) {s : Set α} (h : q.s subseteq s)
  body: ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩

中文:
定义 blur'
  签名: (q : Semiquot α) {s : Set α} (h : q.s subseteq s)
  定义体: ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩

Depends on / 依赖: Trunc.eq, Trunc.lift, Trunc.mk
-/
def blur' (q : Semiquot α) {s : Set α} (h : q.s subseteq s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩

/--
Definition of `blur` / `blur` 的定义

English:
definition blur
  signature: (s : Set α) (q : Semiquot α)
  body: blur' q (s.subset_union_right (t := q.s))

中文:
定义 blur
  签名: (s : Set α) (q : Semiquot α)
  定义体: blur' q (s.subset_union_right (t := q.s))

Depends on / 依赖: s.subset_union_right, subset_union_right
-/
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (s.subset_union_right (t := q.s))

/--
theorem `blur_eq_blur'` / 定理 `blur_eq_blur'`

English:
theorem blur_eq_blur'
  given: (q : Semiquot α) (s : Set α) (h : q.s subseteq s)
  statement: blur s q = blur' q h
  proof: by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h

@[simp]

中文:
定理 blur_eq_blur'
  条件: (q : Semiquot α) (s : Set α) (h : q.s subseteq s)
  结论: blur s q = blur' q h
  证明: by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h

@[simp]

Depends on / 依赖: Set.union_eq_self_of_subset_right, union_eq_self_of_subset_right
-/
theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s subseteq s) : blur s q = blur' q h := by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h

@[simp]
/--
theorem `mem_blur'` / 定理 `mem_blur'`

English:
theorem mem_blur'
  given: (q : Semiquot α) {s : Set α} (h : q.s subseteq s) {a : α}
  statement: a in blur' q h ↔ a in s
  proof: Iff.rfl

中文:
定理 mem_blur'
  条件: (q : Semiquot α) {s : Set α} (h : q.s subseteq s) {a : α}
  结论: a in blur' q h ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s subseteq s) {a : α} : a in blur' q h ↔ a in s :=
  Iff.rfl

/--
Definition of `ofTrunc` / `ofTrunc` 的定义

English:
definition ofTrunc
  signature: (q : Trunc α)
  body: ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩

中文:
定义 ofTrunc
  签名: (q : Trunc α)
  定义体: ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩

Depends on / 依赖: Set.univ, q.map
-/
def ofTrunc (q : Trunc α) : Semiquot α :=
  ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩

/--
Definition of `toTrunc` / `toTrunc` 的定义

English:
definition toTrunc
  signature: (q : Semiquot α)
  body: q.2.map Subtype.val

中文:
定义 toTrunc
  签名: (q : Semiquot α)
  定义体: q.2.map Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
def toTrunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: (q : Semiquot α) (f : α -> β) (h : forall a in q, forall b in q, f a = f b)
  body: Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2

中文:
定义 liftOn
  签名: (q : Semiquot α) (f : α -> β) (h : 对任意 a in q, 对任意 b in q, f a = f b)
  定义体: Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2

Depends on / 依赖: Trunc.liftOn, liftOn
-/
def liftOn (q : Semiquot α) (f : α -> β) (h : forall a in q, forall b in q, f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2

/--
theorem `liftOn_ofMem` / 定理 `liftOn_ofMem`

English:
theorem liftOn_ofMem
  statement: (q : Semiquot α) (f : α -> β)
  proof: by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl

中文:
定理 liftOn_ofMem
  结论: (q : Semiquot α) (f : α -> β)
  证明: by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl

Depends on / 依赖: eq_mk_of_mem, revert
-/
theorem liftOn_ofMem (q : Semiquot α) (f : α -> β)
    (h : forall a in q, forall b in q, f a = f b) (a : α) (aq : a in q) : liftOn q f h = f a := by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (q : Semiquot α)
  body: ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩

@[simp]

中文:
定义 map
  签名: (f : α -> β) (q : Semiquot α)
  定义体: ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩

@[simp]

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
def map (f : α -> β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (f : α -> β) (q : Semiquot α) (b : β)
  statement: b in map f q ↔ exists a, a in q ∧ f a = b
  proof: Set.mem_image _ _ _

中文:
定理 mem_map
  条件: (f : α -> β) (q : Semiquot α) (b : β)
  结论: b in map f q ↔ 存在 a, a in q ∧ f a = b
  证明: Set.mem_image _ _ _

Depends on / 依赖: Set.mem_image, mem_image
-/
theorem mem_map (f : α -> β) (q : Semiquot α) (b : β) : b in map f q ↔ exists a, a in q ∧ f a = b :=
  Set.mem_image _ _ _

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (q : Semiquot α) (f : α -> Semiquot β)
  body: ⟨⋃ a in q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩

@[simp]

中文:
定义 bind
  签名: (q : Semiquot α) (f : α -> Semiquot β)
  定义体: ⟨⋃ a in q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩

@[simp]

Depends on / 依赖: Set.mem_biUnion, mem_biUnion
-/
def bind (q : Semiquot α) (f : α -> Semiquot β) : Semiquot β :=
  ⟨⋃ a in q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩

@[simp]
/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  given: (q : Semiquot α) (f : α -> Semiquot β) (b : β)
  proof: by simp_rw [← exists_prop]; exact Set.mem_iUnion₂

中文:
定理 mem_bind
  条件: (q : Semiquot α) (f : α -> Semiquot β) (b : β)
  证明: by simp_rw [← exists_prop]; exact Set.mem_iUnion₂

Depends on / 依赖: Set.mem_iUnion, exists_prop, simp_rw
-/
theorem mem_bind (q : Semiquot α) (f : α -> Semiquot β) (b : β) :
    b in bind q f ↔ exists a in q, b in f a := by simp_rw [← exists_prop]; exact Set.mem_iUnion₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad Semiquot
  body: @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

@[simp]

中文:
实例 :
  签名: Monad Semiquot
  定义体: @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

@[simp]

Depends on / 依赖: Semiquot, Semiquot.pure
-/
instance : Monad Semiquot where
  pure := @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind

@[simp]
/--
theorem `map_def` / 定理 `map_def`

English:
theorem map_def
  given: {β}
  statement: ((· <$> ·) : (α -> β) -> Semiquot α -> Semiquot β) = map
  proof: rfl

@[simp]

中文:
定理 map_def
  条件: {β}
  结论: ((· <$> ·) : (α -> β) -> Semiquot α -> Semiquot β) = map
  证明: rfl

@[simp]
-/
theorem map_def {β} : ((· <$> ·) : (α -> β) -> Semiquot α -> Semiquot β) = map :=
  rfl

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  given: {β}
  statement: ((· >>= ·) : Semiquot α -> (α -> Semiquot β) -> Semiquot β) = bind
  proof: rfl

@[simp]

中文:
定理 bind_def
  条件: {β}
  结论: ((· >>= ·) : Semiquot α -> (α -> Semiquot β) -> Semiquot β) = bind
  证明: rfl

@[simp]
-/
theorem bind_def {β} : ((· >>= ·) : Semiquot α -> (α -> Semiquot β) -> Semiquot β) = bind :=
  rfl

@[simp]
/--
theorem `mem_pure` / 定理 `mem_pure`

English:
theorem mem_pure
  given: {a b : α}
  statement: a in (pure b : Semiquot α) ↔ a = b
  proof: Set.mem_singleton_iff

中文:
定理 mem_pure
  条件: {a b : α}
  结论: a in (pure b : Semiquot α) ↔ a = b
  证明: Set.mem_singleton_iff

Depends on / 依赖: Set.mem_singleton_iff, mem_singleton_iff
-/
theorem mem_pure {a b : α} : a in (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff

/--
theorem `mem_pure_self` / 定理 `mem_pure_self`

English:
theorem mem_pure_self
  given: (a : α)
  statement: a in (pure a : Semiquot α)
  proof: Set.mem_singleton a

@[simp]

中文:
定理 mem_pure_self
  条件: (a : α)
  结论: a in (pure a : Semiquot α)
  证明: Set.mem_singleton a

@[simp]

Depends on / 依赖: Set.mem_singleton, mem_singleton
-/
theorem mem_pure_self (a : α) : a in (pure a : Semiquot α) :=
  Set.mem_singleton a

@[simp]
/--
theorem `pure_inj` / 定理 `pure_inj`

English:
theorem pure_inj
  given: {a b : α}
  statement: (pure a : Semiquot α) = pure b ↔ a = b
  proof: ext_s.trans Set.singleton_eq_singleton_iff

中文:
定理 pure_inj
  条件: {a b : α}
  结论: (pure a : Semiquot α) = pure b ↔ a = b
  证明: ext_s.trans Set.singleton_eq_singleton_iff

Depends on / 依赖: Set.singleton_eq_singleton_iff, ext_s, ext_s.trans, singleton_eq_singleton_iff
-/
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Semiquot
  body: LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
ext.2 by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ex

中文:
实例 :
  签名: LawfulMonad Semiquot
  定义体: LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
ext.2 by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ex

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad Semiquot := LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
ext.2 by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ext.2 <| by simp)
  (bind_pure_comp := fun {α β} f s => ext.2 <| by simp [eq_comm])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Semiquot α)
  body: ⟨fun s t => forall ⦃x⦄, x in s -> x in t⟩

中文:
实例 :
  签名: LE (Semiquot α)
  定义体: ⟨fun s t => forall ⦃x⦄, x in s -> x in t⟩
-/
instance : LE (Semiquot α) :=
  ⟨fun s t => forall ⦃x⦄, x in s -> x in t⟩

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: : PartialOrder (Semiquot α) where
  body: Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)

中文:
实例 partialOrder
  签名: : PartialOrder (Semiquot α) where
  定义体: Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)

Depends on / 依赖: Set.Subset.refl, Subset
-/
instance partialOrder : PartialOrder (Semiquot α) where
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (Semiquot α)
  body: { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }

@[simp]

中文:
实例 :
  签名: SemilatticeSup (Semiquot α)
  定义体: { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }

@[simp]

Depends on / 依赖: Semiquot, Semiquot.partialOrder, Set.subset_union_left, Set.subset_union_right, Set.union_subset, le_sup_left, le_sup_right, partialOrder, subset_union_left, subset_union_right, sup_le, union_subset
-/
instance : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }

@[simp]
/--
theorem `pure_le` / 定理 `pure_le`

English:
theorem pure_le
  given: {a : α} {s : Semiquot α}
  statement: pure a <= s ↔ a in s
  proof: Set.singleton_subset_iff

中文:
定理 pure_le
  条件: {a : α} {s : Semiquot α}
  结论: pure a <= s ↔ a in s
  证明: Set.singleton_subset_iff

Depends on / 依赖: Set.singleton_subset_iff, singleton_subset_iff
-/
theorem pure_le {a : α} {s : Semiquot α} : pure a <= s ↔ a in s :=
  Set.singleton_subset_iff

/--
Definition of `IsPure` / `IsPure` 的定义

English:
definition IsPure
  signature: (q : Semiquot α)
  body: forall a in q, forall b in q, a = b

中文:
定义 IsPure
  签名: (q : Semiquot α)
  定义体: forall a in q, forall b in q, a = b
-/
def IsPure (q : Semiquot α) : Prop :=
  forall a in q, forall b in q, a = b

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (q : Semiquot α) (h : q.IsPure)
  body: liftOn q id h

中文:
定义 get
  签名: (q : Semiquot α) (h : q.IsPure)
  定义体: liftOn q id h

Depends on / 依赖: liftOn
-/
def get (q : Semiquot α) (h : q.IsPure) : α :=
  liftOn q id h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `get_mem` / 定理 `get_mem`

English:
theorem get_mem
  given: {q : Semiquot α} (p)
  statement: get q p in q
  proof: by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h

中文:
定理 get_mem
  条件: {q : Semiquot α} (p)
  结论: get q p in q
  证明: by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h

Depends on / 依赖: exists_mem, liftOn_ofMem
-/
theorem get_mem {q : Semiquot α} (p) : get q p in q := by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h

/--
theorem `eq_pure` / 定理 `eq_pure`

English:
theorem eq_pure
  given: {q : Semiquot α} (p)
  statement: q = pure (get q p)
  proof: ext.2 fun a => by simpa using ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩

@[simp]

中文:
定理 eq_pure
  条件: {q : Semiquot α} (p)
  结论: q = pure (get q p)
  证明: ext.2 fun a => by simpa using ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩

@[simp]

Depends on / 依赖: e.symm, get_mem
-/
theorem eq_pure {q : Semiquot α} (p) : q = pure (get q p) :=
  ext.2 fun a => by simpa using ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩

@[simp]
/--
theorem `pure_isPure` / 定理 `pure_isPure`

English:
theorem pure_isPure
  given: (a : α)
  statement: IsPure (pure a)

中文:
定理 pure_isPure
  条件: (a : α)
  结论: IsPure (pure a)
-/
theorem pure_isPure (a : α) : IsPure (pure a)
  | b, ab, c, ac => by
    rw [mem_pure] at ab ac
    rwa [← ac] at ab

/--
theorem `isPure_iff` / 定理 `isPure_iff`

English:
theorem isPure_iff
  given: {s : Semiquot α}
  statement: IsPure s ↔ exists a, s = pure a
  proof: ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩

中文:
定理 isPure_iff
  条件: {s : Semiquot α}
  结论: IsPure s ↔ 存在 a, s = pure a
  证明: ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩

Depends on / 依赖: e.symm, eq_pure, pure_isPure
-/
theorem isPure_iff {s : Semiquot α} : IsPure s ↔ exists a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩

/--
theorem `IsPure.mono` / 定理 `IsPure.mono`

English:
theorem IsPure.mono
  given: {s t : Semiquot α} (st : s <= t) (h : IsPure t)
  statement: IsPure s

中文:
定理 IsPure.mono
  条件: {s t : Semiquot α} (st : s <= t) (h : IsPure t)
  结论: IsPure s
-/
theorem IsPure.mono {s t : Semiquot α} (st : s <= t) (h : IsPure t) : IsPure s
  | _, as, _, bs => h _ (st as) _ (st bs)

/--
theorem `IsPure.min` / 定理 `IsPure.min`

English:
theorem IsPure.min
  given: {s t : Semiquot α} (h : IsPure t)
  statement: s <= t ↔ s = t
  proof: ⟨fun st =>
le_antisymm st by
      rw [eq_pure h]; rw [eq_pure (h.mono st)]; simpa using h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩

中文:
定理 IsPure.min
  条件: {s t : Semiquot α} (h : IsPure t)
  结论: s <= t ↔ s = t
  证明: ⟨fun st =>
le_antisymm st by
      rw [eq_pure h]; rw [eq_pure (h.mono st)]; simpa using h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩

Depends on / 依赖: eq_pure, get_mem, h.mono, le_antisymm, le_of_eq
-/
theorem IsPure.min {s t : Semiquot α} (h : IsPure t) : s <= t ↔ s = t :=
  ⟨fun st =>
le_antisymm st by
      rw [eq_pure h]; rw [eq_pure (h.mono st)]; simpa using h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩

/--
theorem `isPure_of_subsingleton` / 定理 `isPure_of_subsingleton`

English:
theorem isPure_of_subsingleton
  given: [Subsingleton α] (q : Semiquot α)
  statement: IsPure q

中文:
定理 isPure_of_subsingleton
  条件: [Subsingleton α] (q : Semiquot α)
  结论: IsPure q
-/
theorem isPure_of_subsingleton [Subsingleton α] (q : Semiquot α) : IsPure q
  | _, _, _, _ => Subsingleton.elim _ _

/--
Definition of `univ` / `univ` 的定义

English:
definition univ
  signature: [Inhabited α]
  body: mk Set.mem_univ default

中文:
定义 univ
  签名: [Inhabited α]
  定义体: mk Set.mem_univ default

Depends on / 依赖: Set.mem_univ, mem_univ
-/
def univ [Inhabited α] : Semiquot α :=
mk Set.mem_univ default

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Semiquot α)
  body: ⟨univ⟩

@[simp]

中文:
实例 [Inhabited
  签名: α] : Inhabited (Semiquot α)
  定义体: ⟨univ⟩

@[simp]
-/
instance [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩

@[simp]
/--
theorem `mem_univ` / 定理 `mem_univ`

English:
theorem mem_univ
  given: [Inhabited α]
  statement: forall a, a in @univ α _
  proof: @Set.mem_univ α

@[congr]

中文:
定理 mem_univ
  条件: [Inhabited α]
  结论: 对任意 a, a in @univ α _
  证明: @Set.mem_univ α

@[congr]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_univ [Inhabited α] : forall a, a in @univ α _ :=
  @Set.mem_univ α

@[congr]
/--
theorem `univ_unique` / 定理 `univ_unique`

English:
theorem univ_unique
  given: (I J : Inhabited α)
  statement: @univ _ I = @univ _ J
  proof: ext.2 fun a => refl (a in univ)

@[simp]

中文:
定理 univ_unique
  条件: (I J : Inhabited α)
  结论: @univ _ I = @univ _ J
  证明: ext.2 fun a => refl (a in univ)

@[simp]
-/
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2 fun a => refl (a in univ)

@[simp]
/--
theorem `isPure_univ` / 定理 `isPure_univ`

English:
theorem isPure_univ
  given: [Inhabited α]
  statement: @IsPure α univ ↔ Subsingleton α
  proof: ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩

中文:
定理 isPure_univ
  条件: [Inhabited α]
  结论: @IsPure α univ ↔ Subsingleton α
  证明: ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩
-/
theorem isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : OrderTop (Semiquot α) where
  body: univ
  le_top _ := Set.subset_univ _

中文:
实例 [Inhabited
  签名: α] : OrderTop (Semiquot α) where
  定义体: univ
  le_top _ := Set.subset_univ _
-/
instance [Inhabited α] : OrderTop (Semiquot α) where
  top := univ
  le_top _ := Set.subset_univ _

end Semiquot
