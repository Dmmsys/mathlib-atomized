/-
Copyright (c) 2024 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import Mathlib.Order.CompleteLattice.SetLike

/-!
# Trees in the sense of descriptive set theory

This file defines trees of depth `ω` in the sense of descriptive set theory as sets of finite
sequences that are stable under taking prefixes.

## Main declarations

* `tree A`: a (possibly infinite) tree of depth at most `ω` with nodes in `A`
-/

@[expose] public section

namespace Descriptive

/--
Definition of `tree` / `tree` 的定义

English:
definition tree
  signature: (A : Type*)
  body: CompleteSublattice.mk' {T | forall ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] in T -> x in T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

中文:
定义 tree
  签名: (A : 类型)
  定义体: CompleteSublattice.mk' {T | forall ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] in T -> x in T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

Depends on / 依赖: CompleteSublattice, CompleteSublattice.mk
-/
def tree (A : Type*) : CompleteSublattice (Set (List A)) :=
  CompleteSublattice.mk' {T | forall ⦃x : List A⦄ ⦃a : A⦄, x ++ [a] in T -> x in T}
    (by rintro S hS x a ⟨t, ht, hx⟩; use t, ht, hS ht hx)
    (by rintro S hS x a h T hT; exact hS hT <| h T hT)

@[simps!] instance (A : Type*) : SetLike (tree A) (List A) := SetLike.instSubtypeSet

example (A : Type*) : PartialOrder (tree A) := inferInstance

namespace Tree
variable {A : Type*} {S T : tree A}

/--
lemma `mem_of_append` / 引理 `mem_of_append`

English:
lemma mem_of_append
  given: {x y : List A} (h : x ++ y in T)
  statement: x in T
  proof: by
  induction y generalizing x with
  | nil => simpa using h
  | cons y ys ih => exact T.prop (ih (by simpa))

中文:
引理 mem_of_append
  条件: {x y : 列表 A} (h : x ++ y in T)
  结论: x in T
  证明: by
  induction y generalizing x with
  | nil => simpa using h
  | cons y ys ih => exact T.prop (ih (by simpa))

Depends on / 依赖: T.prop, generalizing
-/
lemma mem_of_append {x y : List A} (h : x ++ y in T) : x in T := by
  induction y generalizing x with
  | nil => simpa using h
  | cons y ys ih => exact T.prop (ih (by simpa))

/--
lemma `mem_of_prefix` / 引理 `mem_of_prefix`

English:
lemma mem_of_prefix
  given: {x y : List A} (h' : x <+: y) (h : y in T)
  statement: x in T
  proof: by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h

中文:
引理 mem_of_prefix
  条件: {x y : 列表 A} (h' : x <+: y) (h : y in T)
  结论: x in T
  证明: by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h

Depends on / 依赖: mem_of_append
-/
lemma mem_of_prefix {x y : List A} (h' : x <+: y) (h : y in T) : x in T := by
  obtain ⟨_, rfl⟩ := h'; exact mem_of_append h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Trans List.IsPrefix (fun x (T : tree A) => x in T) (fun x T => x in T)
  body: mem_of_prefix

中文:
实例 :
  签名: Trans 列表.IsPrefix (fun x (T : tree A) => x in T) (fun x T => x in T)
  定义体: mem_of_prefix

Depends on / 依赖: mem_of_prefix
-/
instance : Trans List.IsPrefix (fun x (T : tree A) => x in T) (fun x T => x in T) where
  trans := mem_of_prefix

/--
lemma `singleton_mem` / 引理 `singleton_mem`

English:
lemma singleton_mem
  given: (T : tree A) {a : A} {x : List A} (h : a :: x in T)
  statement: [a] in T
  proof: mem_of_prefix ⟨x, rfl⟩ h

中文:
引理 singleton_mem
  条件: (T : tree A) {a : A} {x : 列表 A} (h : a :: x in T)
  结论: [a] in T
  证明: mem_of_prefix ⟨x, rfl⟩ h

Depends on / 依赖: mem_of_prefix
-/
lemma singleton_mem (T : tree A) {a : A} {x : List A} (h : a :: x in T) : [a] in T :=
  mem_of_prefix ⟨x, rfl⟩ h

/--
lemma `tree_eq_bot` / 引理 `tree_eq_bot`

English:
lemma tree_eq_bot
  statement: T = ⊥ ↔ [] ∉ T where
  proof: by rintro rfl; simp
mpr h := by ext x; simpa using fun h' => h mem_of_prefix x.nil_prefix h'

中文:
引理 tree_eq_bot
  结论: T = ⊥ ↔ [] ∉ T where
  证明: by rintro rfl; simp
mpr h := by ext x; simpa using fun h' => h mem_of_prefix x.nil_prefix h'
-/
@[simp] lemma tree_eq_bot : T = ⊥ ↔ [] ∉ T where
  mp := by rintro rfl; simp
mpr h := by ext x; simpa using fun h' => h mem_of_prefix x.nil_prefix h'

/--
lemma `take_mem` / 引理 `take_mem`

English:
lemma take_mem
  given: {n : Nat} (x : T)
  statement: x.val.take n in T
  proof: mem_of_prefix (x.val.take_prefix n) x.prop

中文:
引理 take_mem
  条件: {n : 自然数} (x : T)
  结论: x.val.take n in T
  证明: mem_of_prefix (x.val.take_prefix n) x.prop

Depends on / 依赖: mem_of_prefix, take_prefix, x.prop, x.val.take_prefix
-/
lemma take_mem {n : Nat} (x : T) : x.val.take n in T :=
  mem_of_prefix (x.val.take_prefix n) x.prop

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (n : Nat) (x : T)
  body: ⟨x.val.take n, take_mem x⟩

中文:
定义 take
  签名: (n : 自然数) (x : T)
  定义体: ⟨x.val.take n, take_mem x⟩
-/
@[simps] def take (n : Nat) (x : T) : T := ⟨x.val.take n, take_mem x⟩

/--
lemma `take_take` / 引理 `take_take`

English:
lemma take_take
  given: (m n : Nat) (x : T)
  statement: take m (take n x) = take (m ⊓ n) x
  proof: by
  simp [Subtype.ext_iff, List.take_take]

中文:
引理 take_take
  条件: (m n : 自然数) (x : T)
  结论: take m (take n x) = take (m ⊓ n) x
  证明: by
  simp [Subtype.ext_iff, List.take_take]
-/
@[simp] lemma take_take (m n : Nat) (x : T) : take m (take n x) = take (m ⊓ n) x := by
  simp [Subtype.ext_iff, List.take_take]

/--
lemma `take_eq_take` / 引理 `take_eq_take`

English:
lemma take_eq_take
  given: {x : T} {m n : Nat}
  proof: by simp [Subtype.ext_iff]

中文:
引理 take_eq_take
  条件: {x : T} {m n : 自然数}
  证明: by simp [Subtype.ext_iff]
-/
@[simp] lemma take_eq_take {x : T} {m n : Nat} :
    take m x = take n x ↔ m ⊓ x.val.length = n ⊓ x.val.length := by simp [Subtype.ext_iff]

-- ### `subAt`

variable (T) (x y : List A)

/--
Definition of `subAt` / `subAt` 的定义

English:
definition subAt
  signature: : tree A
  body: ⟨(x ++ ·)⁻¹' T, fun _ a _ => mem_of_append (y := [a]) (by rwa [List.append_assoc])⟩

中文:
定义 subAt
  签名: : tree A
  定义体: ⟨(x ++ ·)⁻¹' T, fun _ a _ => mem_of_append (y := [a]) (by rwa [List.append_assoc])⟩

Depends on / 依赖: List.append_assoc, append_assoc, mem_of_append
-/
def subAt : tree A :=
  ⟨(x ++ ·)⁻¹' T, fun _ a _ => mem_of_append (y := [a]) (by rwa [List.append_assoc])⟩

/--
lemma `mem_subAt` / 引理 `mem_subAt`

English:
lemma mem_subAt
  statement: y in subAt T x ↔ x ++ y in T
  proof: Iff.rfl

中文:
引理 mem_subAt
  结论: y in subAt T x ↔ x ++ y in T
  证明: Iff.rfl
-/
@[simp] lemma mem_subAt : y in subAt T x ↔ x ++ y in T := Iff.rfl

/--
lemma `subAt_nil` / 引理 `subAt_nil`

English:
lemma subAt_nil
  statement: subAt T [] = T
  proof: rfl

中文:
引理 subAt_nil
  结论: subAt T [] = T
  证明: rfl
-/
@[simp] lemma subAt_nil : subAt T [] = T := rfl

/--
lemma `subAt_append` / 引理 `subAt_append`

English:
lemma subAt_append
  statement: subAt (subAt T x) y = subAt T (x ++ y)
  proof: by ext; simp

中文:
引理 subAt_append
  结论: subAt (subAt T x) y = subAt T (x ++ y)
  证明: by ext; simp
-/
@[simp] lemma subAt_append : subAt (subAt T x) y = subAt T (x ++ y) := by ext; simp

/--
lemma `subAt_mono` / 引理 `subAt_mono`

English:
lemma subAt_mono
  given: (h : S <= T)
  statement: subAt S x <= subAt T x
  proof: Set.preimage_mono h

中文:
引理 subAt_mono
  条件: (h : S <= T)
  结论: subAt S x <= subAt T x
  证明: Set.preimage_mono h
-/
@[gcongr] lemma subAt_mono (h : S <= T) : subAt S x <= subAt T x :=
  Set.preimage_mono h

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (n : Nat) (x : T)
  body: ⟨x.val.drop n, by simp⟩

中文:
定义 drop
  签名: (n : 自然数) (x : T)
  定义体: ⟨x.val.drop n, by simp⟩
-/
@[simps] def drop (n : Nat) (x : T) : subAt T (Tree.take n x).val :=
  ⟨x.val.drop n, by simp⟩

-- ### `pullSub`

/--
Definition of `pullSub` / `pullSub` 的定义

English:
definition pullSub
  signature: : tree A where
  body: { y | y.take x.length <+: x ∧ y.drop x.length in T }
  property := fun y a ⟨h1, h2⟩ =>
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩

中文:
定义 pullSub
  签名: : tree A where
  定义体: { y | y.take x.length <+: x ∧ y.drop x.length in T }
  property := fun y a ⟨h1, h2⟩ =>
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩

Depends on / 依赖: length, x.length, y.drop, y.take
-/
def pullSub : tree A where
  val := { y | y.take x.length <+: x ∧ y.drop x.length in T }
  property := fun y a ⟨h1, h2⟩ =>
    ⟨((y.prefix_append [a]).take x.length).trans h1,
    mem_of_prefix ((y.prefix_append [a]).drop x.length) h2⟩

variable {T x y}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_pullSub_short` / 引理 `mem_pullSub_short`

English:
lemma mem_pullSub_short
  given: (hl : y.length <= x.length)
  statement: y in pullSub T x ↔ y <+: x ∧ [] in T
  proof: by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]

中文:
引理 mem_pullSub_short
  条件: (hl : y.length <= x.length)
  结论: y in pullSub T x ↔ y <+: x ∧ [] in T
  证明: by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]

Depends on / 依赖: List.drop_eq_nil_iff.mpr, List.take_of_length_le, drop_eq_nil_iff, pullSub, take_of_length_le
-/
lemma mem_pullSub_short (hl : y.length <= x.length) : y in pullSub T x ↔ y <+: x ∧ [] in T := by
  simp [pullSub, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_pullSub_long` / 引理 `mem_pullSub_long`

English:
lemma mem_pullSub_long
  given: (hl : x.length <= y.length)
  statement: y in pullSub T x ↔ exists z in T, y = x ++ z where
  proof: by
    intro ⟨h1, h2⟩; use y.drop x.length, h2
    nth_rw 1 [← List.take_append_drop x.length y]
    simpa [-List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  mpr := by simp +contextual [pullSub]

中文:
引理 mem_pullSub_long
  条件: (hl : x.length <= y.length)
  结论: y in pullSub T x ↔ 存在 z in T, y = x ++ z where
  证明: by
    intro ⟨h1, h2⟩; use y.drop x.length, h2
    nth_rw 1 [← List.take_append_drop x.length y]
    simpa [-List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  mpr := by simp +contextual [pullSub]

Depends on / 依赖: List.prefix_iff_eq_take, List.take_append_drop, contextual, length, nth_rw, prefix_iff_eq_take, pullSub, take_append_drop, x.length, y.drop
-/
lemma mem_pullSub_long (hl : x.length <= y.length) : y in pullSub T x ↔ exists z in T, y = x ++ z where
  mp := by
    intro ⟨h1, h2⟩; use y.drop x.length, h2
    nth_rw 1 [← List.take_append_drop x.length y]
    simpa [-List.take_append_drop, List.prefix_iff_eq_take, hl] using h1
  mpr := by simp +contextual [pullSub]

/--
lemma `mem_pullSub_append` / 引理 `mem_pullSub_append`

English:
lemma mem_pullSub_append
  statement: x ++ y in pullSub T x ↔ y in T
  proof: by simp [mem_pullSub_long]

中文:
引理 mem_pullSub_append
  结论: x ++ y in pullSub T x ↔ y in T
  证明: by simp [mem_pullSub_long]
-/
@[simp] lemma mem_pullSub_append : x ++ y in pullSub T x ↔ y in T := by simp [mem_pullSub_long]

/--
lemma `mem_pullSub_self` / 引理 `mem_pullSub_self`

English:
lemma mem_pullSub_self
  statement: x in pullSub T x ↔ [] in T
  proof: by
  simpa using mem_pullSub_append (y := [])

中文:
引理 mem_pullSub_self
  结论: x in pullSub T x ↔ [] in T
  证明: by
  simpa using mem_pullSub_append (y := [])
-/
@[simp] lemma mem_pullSub_self : x in pullSub T x ↔ [] in T := by
  simpa using mem_pullSub_append (y := [])


variable (T x y)

/--
lemma `pullSub_subAt` / 引理 `pullSub_subAt`

English:
lemma pullSub_subAt
  statement: pullSub (subAt T x) x <= T
  proof: by
  intro y (h : y in pullSub _ x); rcases le_total y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; exact mem_of_prefix h.1 (by simpa using h.2)
  · rw [mem_pullSub_long h'] at h; obtain ⟨_, h, rfl⟩ := h; exact h

中文:
引理 pullSub_subAt
  结论: pullSub (subAt T x) x <= T
  证明: by
  intro y (h : y in pullSub _ x); rcases le_total y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; exact mem_of_prefix h.1 (by simpa using h.2)
  · rw [mem_pullSub_long h'] at h; obtain ⟨_, h, rfl⟩ := h; exact h

Depends on / 依赖: le_total, length, mem_of_prefix, mem_pullSub_long, mem_pullSub_short, pullSub, x.length, y.length
-/
lemma pullSub_subAt : pullSub (subAt T x) x <= T := by
  intro y (h : y in pullSub _ x); rcases le_total y.length x.length with h' | h'
  · rw [mem_pullSub_short h'] at h; exact mem_of_prefix h.1 (by simpa using h.2)
  · rw [mem_pullSub_long h'] at h; obtain ⟨_, h, rfl⟩ := h; exact h

/--
lemma `subAt_pullSub` / 引理 `subAt_pullSub`

English:
lemma subAt_pullSub
  statement: subAt (pullSub T x) x = T
  proof: by
  ext y; simp

中文:
引理 subAt_pullSub
  结论: subAt (pullSub T x) x = T
  证明: by
  ext y; simp
-/
@[simp] lemma subAt_pullSub : subAt (pullSub T x) x = T := by
  ext y; simp

/--
lemma `pullSub_mono` / 引理 `pullSub_mono`

English:
lemma pullSub_mono
  given: (h : S <= T) x
  statement: pullSub S x <= pullSub T x
  proof: fun _ ⟨h1, h2⟩ => ⟨h1, h h2⟩

中文:
引理 pullSub_mono
  条件: (h : S <= T) x
  结论: pullSub S x <= pullSub T x
  证明: fun _ ⟨h1, h2⟩ => ⟨h1, h h2⟩
-/
@[gcongr] lemma pullSub_mono (h : S <= T) x : pullSub S x <= pullSub T x :=
  fun _ ⟨h1, h2⟩ => ⟨h1, h h2⟩

/--
lemma `pullSub_adjunction` / 引理 `pullSub_adjunction`

English:
lemma pullSub_adjunction
  given: (S T : tree A) (x : List A)
  statement: pullSub S x <= T ↔ S <= subAt T x where
  proof: by rw [← subAt_pullSub S x]; gcongr
  mpr _ := le_trans (by gcongr) (pullSub_subAt T x)

中文:
引理 pullSub_adjunction
  条件: (S T : tree A) (x : 列表 A)
  结论: pullSub S x <= T ↔ S <= subAt T x where
  证明: by rw [← subAt_pullSub S x]; gcongr
  mpr _ := le_trans (by gcongr) (pullSub_subAt T x)

Depends on / 依赖: le_trans, pullSub_subAt, subAt_pullSub
-/
lemma pullSub_adjunction (S T : tree A) (x : List A) : pullSub S x <= T ↔ S <= subAt T x where
  mp _ := by rw [← subAt_pullSub S x]; gcongr
  mpr _ := le_trans (by gcongr) (pullSub_subAt T x)

/--
lemma `pullSub_nil` / 引理 `pullSub_nil`

English:
lemma pullSub_nil
  statement: pullSub T [] = T
  proof: by simp [pullSub]

中文:
引理 pullSub_nil
  结论: pullSub T [] = T
  证明: by simp [pullSub]
-/
@[simp] lemma pullSub_nil : pullSub T [] = T := by simp [pullSub]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullSub_append` / 引理 `pullSub_append`

English:
lemma pullSub_append
  statement: pullSub (pullSub T y) x = pullSub T (x ++ y)
  proof: by
  ext z; rcases le_total x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp
      simp [pullSub, List.take_add]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
cases hp List.prefix_iff_eq_take.mpr (h.eq_of_length (by simpa)).symm
  · rw [mem_pullSub_short hl, mem_pullSub_short (by simp), mem_pullSub_short (by simp; lia)]
    simpa using fun _ => (z.isPrefix_append_of_length hl).symm

中文:
引理 pullSub_append
  结论: pullSub (pullSub T y) x = pullSub T (x ++ y)
  证明: by
  ext z; rcases le_total x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp
      simp [pullSub, List.take_add]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
cases hp List.prefix_iff_eq_take.mpr (h.eq_of_length (by simpa)).symm
  · rw [mem_pullSub_short hl, mem_pullSub_short (by simp), mem_pullSub_short (by simp; lia)]
    simpa using fun _ => (z.isPrefix_append_of_length hl).symm
-/
@[simp] lemma pullSub_append : pullSub (pullSub T y) x = pullSub T (x ++ y) := by
  ext z; rcases le_total x.length z.length with hl | hl
  · by_cases hp : x <+: z
    · obtain ⟨z, rfl⟩ := hp
      simp [pullSub, List.take_add]
    · constructor <;> intro ⟨h, _⟩ <;>
        [skip; replace h := by simpa [List.take_take] using h.take x.length] <;>
cases hp List.prefix_iff_eq_take.mpr (h.eq_of_length (by simpa)).symm
  · rw [mem_pullSub_short hl, mem_pullSub_short (by simp), mem_pullSub_short (by simp; lia)]
    simpa using fun _ => (z.isPrefix_append_of_length hl).symm

end Descriptive.Tree
