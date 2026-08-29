/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Util.Delaborators

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `Directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `DirectedOn r s`: Predicate stating that the set `s` is `r`-directed.
* `IsDirected α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `Std.Total`.

## TODO

Define connected orders (the transitive symmetric closure of `≤` is everything) and show that
(co)directed orders are connected.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

@[expose] public section


open Function

variable {α β : Type*} {ι κ : Sort*} (r r' s : α -> α -> Prop)

/-- Local notation for a relation -/
local infixl:50 " ≼ " => r

/--
Definition of `Directed` / `Directed` 的定义

English:
definition Directed
  signature: (f : ι -> α)
  body: forall x y, exists z, f x ≼ f z ∧ f y ≼ f z

中文:
定义 Directed
  签名: (f : ι -> α)
  定义体: forall x y, exists z, f x ≼ f z ∧ f y ≼ f z
-/
def Directed (f : ι -> α) :=
  forall x y, exists z, f x ≼ f z ∧ f y ≼ f z

/--
Definition of `DirectedOn` / `DirectedOn` 的定义

English:
definition DirectedOn
  signature: (s : Set α)
  body: forall x in s, forall y in s, exists z in s, x ≼ z ∧ y ≼ z

中文:
定义 DirectedOn
  签名: (s : 集合 α)
  定义体: forall x in s, forall y in s, exists z in s, x ≼ z ∧ y ≼ z
-/
def DirectedOn (s : Set α) :=
  forall x in s, forall y in s, exists z in s, x ≼ z ∧ y ≼ z

variable {r r'}

/--
theorem `directedOn_iff_directed` / 定理 `directedOn_iff_directed`

English:
theorem directedOn_iff_directed
  given: {s}
  statement: @DirectedOn α r s ↔ Directed r (Subtype.val : s -> α)
  proof: by
  simp only [DirectedOn, Directed, Subtype.exists, exists_and_left, exists_prop, Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed

中文:
定理 directedOn_iff_directed
  条件: {s}
  结论: @DirectedOn α r s ↔ Directed r (子类型.val : s -> α)
  证明: by
  simp only [DirectedOn, Directed, Subtype.exists, exists_and_left, exists_prop, Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed

Depends on / 依赖: And.comm, Directed, DirectedOn, Subtype, Subtype.exists, Subtype.forall, and_assoc, exists_and_left, exists_prop
-/
theorem directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (Subtype.val : s -> α) := by
  simp only [DirectedOn, Directed, Subtype.exists, exists_and_left, exists_prop, Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed

/--
theorem `directedOn_range` / 定理 `directedOn_range`

English:
theorem directedOn_range
  given: {f : ι -> α}
  statement: DirectedOn r (.range f) ↔ Directed r f
  proof: by
  simp_rw [Directed, DirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨_, Directed.directedOn_range⟩ := directedOn_range

中文:
定理 directedOn_range
  条件: {f : ι -> α}
  结论: DirectedOn r (.range f) ↔ Directed r f
  证明: by
  simp_rw [Directed, DirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨_, Directed.directedOn_range⟩ := directedOn_range

Depends on / 依赖: Directed, DirectedOn, Set.exists_range_iff, Set.forall_mem_range, exists_range_iff, forall_mem_range, simp_rw
-/
theorem directedOn_range {f : ι -> α} : DirectedOn r (.range f) ↔ Directed r f := by
  simp_rw [Directed, DirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨_, Directed.directedOn_range⟩ := directedOn_range

/--
theorem `directedOn_image` / 定理 `directedOn_image`

English:
theorem directedOn_image
  given: {s : Set β} {f : β -> α}
  proof: by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]

中文:
定理 directedOn_image
  条件: {s : 集合 β} {f : β -> α}
  证明: by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]

Depends on / 依赖: DirectedOn, Order.Preimage, Preimage, Set.mem_image, and_imp, exists_exists_and_eq_and, forall_exists_index, mem_image
-/
theorem directedOn_image {s : Set β} {f : β -> α} :
    DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]

/--
theorem `DirectedOn.mono'` / 定理 `DirectedOn.mono'`

English:
theorem DirectedOn.mono'
  statement: {s : Set α} (hs : DirectedOn r s)
  proof: fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

中文:
定理 DirectedOn.mono'
  结论: {s : 集合 α} (hs : DirectedOn r s)
  证明: fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩
-/
theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
    (h : forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> r a b -> r' a b) : DirectedOn r' s := fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

/--
theorem `DirectedOn.mono` / 定理 `DirectedOn.mono`

English:
theorem DirectedOn.mono
  given: {s : Set α} (h : DirectedOn r s) (H : forall ⦃a b⦄, r a b -> r' a b)
  proof: h.mono' fun _ _ _ _ h => H h

中文:
定理 DirectedOn.mono
  条件: {s : 集合 α} (h : DirectedOn r s) (H : 对任意 ⦃a b⦄, r a b -> r' a b)
  证明: h.mono' fun _ _ _ _ h => H h

Depends on / 依赖: h.mono
-/
theorem DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : forall ⦃a b⦄, r a b -> r' a b) :
    DirectedOn r' s :=
  h.mono' fun _ _ _ _ h => H h

/--
theorem `directed_comp` / 定理 `directed_comp`

English:
theorem directed_comp
  given: {ι} {f : ι -> β} {g : β -> α}
  statement: Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f
  proof: Iff.rfl

中文:
定理 directed_comp
  条件: {ι} {f : ι -> β} {g : β -> α}
  结论: Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem directed_comp {ι} {f : ι -> β} {g : β -> α} : Directed r (g ∘ f) ↔ Directed (g ⁻¹'o r) f :=
  Iff.rfl

/--
lemma `directed_comp_iff_of_surjective` / 引理 `directed_comp_iff_of_surjective`

English:
lemma directed_comp_iff_of_surjective
  given: {f : ι -> κ} (hf : f.Surjective) {g : κ -> α}
  proof: by simp [Directed, hf.forall, hf.exists]

alias ⟨_, Directed.comp_of_surjective⟩ := directed_comp_iff_of_surjective

中文:
引理 directed_comp_iff_of_surjective
  条件: {f : ι -> κ} (hf : f.满射) {g : κ -> α}
  证明: by simp [Directed, hf.forall, hf.exists]

alias ⟨_, Directed.comp_of_surjective⟩ := directed_comp_iff_of_surjective

Depends on / 依赖: Directed, hf.exists, hf.forall
-/
lemma directed_comp_iff_of_surjective {f : ι -> κ} (hf : f.Surjective) {g : κ -> α} :
    Directed r (g ∘ f) ↔ Directed r g := by simp [Directed, hf.forall, hf.exists]

alias ⟨_, Directed.comp_of_surjective⟩ := directed_comp_iff_of_surjective

/--
theorem `Directed.mono` / 定理 `Directed.mono`

English:
theorem Directed.mono
  statement: {s : α -> α -> Prop} {ι} {f : ι -> α} (H : forall a b, r a b -> s a b)
  proof: fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩

中文:
定理 Directed.mono
  结论: {s : α -> α -> 命题} {ι} {f : ι -> α} (H : 对任意 a b, r a b -> s a b)
  证明: fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩
-/
theorem Directed.mono {s : α -> α -> Prop} {ι} {f : ι -> α} (H : forall a b, r a b -> s a b)
    (h : Directed r f) : Directed s f := fun a b =>
  let ⟨c, h₁, h₂⟩ := h a b
  ⟨c, H _ _ h₁, H _ _ h₂⟩

/--
theorem `Directed.mono_comp` / 定理 `Directed.mono_comp`

English:
theorem Directed.mono_comp
  statement: (r : α -> α -> Prop) {ι} {rb : β -> β -> Prop} {g : α -> β} {f : ι -> α}
  proof: directed_comp.2 hf.mono hg

中文:
定理 Directed.mono_comp
  结论: (r : α -> α -> 命题) {ι} {rb : β -> β -> 命题} {g : α -> β} {f : ι -> α}
  证明: directed_comp.2 hf.mono hg

Depends on / 依赖: directed_comp, hf.mono
-/
theorem Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β -> β -> Prop} {g : α -> β} {f : ι -> α}
    (hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)) (hf : Directed r f) : Directed rb (g ∘ f) :=
directed_comp.2 hf.mono hg

/--
theorem `DirectedOn.mono_comp` / 定理 `DirectedOn.mono_comp`

English:
theorem DirectedOn.mono_comp
  statement: {r : α -> α -> Prop} {rb : β -> β -> Prop} {g : α -> β} {s : Set α}
  proof: directedOn_image.mpr (hf.mono hg)

中文:
定理 DirectedOn.mono_comp
  结论: {r : α -> α -> 命题} {rb : β -> β -> 命题} {g : α -> β} {s : 集合 α}
  证明: directedOn_image.mpr (hf.mono hg)

Depends on / 依赖: directedOn_image, directedOn_image.mpr, hf.mono
-/
theorem DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β -> β -> Prop} {g : α -> β} {s : Set α}
    (hg : forall ⦃x y⦄, r x y -> rb (g x) (g y)) (hf : DirectedOn r s) : DirectedOn rb (g '' s) :=
  directedOn_image.mpr (hf.mono hg)

/--
lemma `directedOn_onFun_iff` / 引理 `directedOn_onFun_iff`

English:
lemma directedOn_onFun_iff
  given: {r : α -> α -> Prop} {f : β -> α} {s : Set β}
  proof: by
  refine ⟨DirectedOn.mono_comp (by simp), fun h x hx y hy => ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := h (f x) (Set.mem_image_of_mem f hx) (f y)
    (Set.mem_image_of_mem f hy)
  grind

中文:
引理 directedOn_onFun_iff
  条件: {r : α -> α -> 命题} {f : β -> α} {s : 集合 β}
  证明: by
  refine ⟨DirectedOn.mono_comp (by simp), fun h x hx y hy => ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := h (f x) (Set.mem_image_of_mem f hx) (f y)
    (Set.mem_image_of_mem f hy)
  grind

Depends on / 依赖: DirectedOn, DirectedOn.mono_comp, Set.mem_image_of_mem, mem_image_of_mem, mono_comp
-/
lemma directedOn_onFun_iff {r : α -> α -> Prop} {f : β -> α} {s : Set β} :
    DirectedOn (r on f) s ↔ DirectedOn r (f '' s) := by
  refine ⟨DirectedOn.mono_comp (by simp), fun h x hx y hy => ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := h (f x) (Set.mem_image_of_mem f hx) (f y)
    (Set.mem_image_of_mem f hy)
  grind

/--
theorem `directedOn_of_sup_mem` / 定理 `directedOn_of_sup_mem`

English:
theorem directedOn_of_sup_mem
  statement: [SemilatticeSup α] {S : Set α}
  proof: fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩

中文:
定理 directedOn_of_sup_mem
  结论: [SemilatticeSup α] {S : 集合 α}
  证明: fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩
-/
theorem directedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : forall ⦃i j⦄, i in S -> j in S -> i ⊔ j in S) : DirectedOn (· <= ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩

/--
theorem `Directed.extend_bot` / 定理 `Directed.extend_bot`

English:
theorem Directed.extend_bot
  statement: [Preorder α] [OrderBot α] {e : ι -> β} {f : ι -> α}
  proof: by
  intro a b
  rcases (em (exists i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (exists i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

中文:
定理 Directed.extend_bot
  结论: [预序 α] [有底序 α] {e : ι -> β} {f : ι -> α}
  证明: by
  intro a b
  rcases (em (exists i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (exists i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

Depends on / 依赖: Function, Function.extend_apply, extend_apply, he.extend_apply, true_and
-/
theorem Directed.extend_bot [Preorder α] [OrderBot α] {e : ι -> β} {f : ι -> α}
    (hf : Directed (· <= ·) f) (he : Function.Injective e) :
    Directed (· <= ·) (Function.extend e f ⊥) := by
  intro a b
  rcases (em (exists i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (exists i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

/--
theorem `directedOn_of_inf_mem` / 定理 `directedOn_of_inf_mem`

English:
theorem directedOn_of_inf_mem
  statement: [SemilatticeInf α] {S : Set α}
  proof: directedOn_of_sup_mem (α := αᵒᵈ) H

中文:
定理 directedOn_of_inf_mem
  结论: [SemilatticeInf α] {S : 集合 α}
  证明: directedOn_of_sup_mem (α := αᵒᵈ) H

Depends on / 依赖: directedOn_of_sup_mem
-/
theorem directedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : forall ⦃i j⦄, i in S -> j in S -> i ⊓ j in S) : DirectedOn (· >= ·) S :=
  directedOn_of_sup_mem (α := αᵒᵈ) H

/--
theorem `Std.Total.directed` / 定理 `Std.Total.directed`

English:
theorem Std.Total.directed
  given: [Std.Total r] (f : ι -> α)
  statement: Directed r f
  proof: fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩

中文:
定理 Std.全.directed
  条件: [Std.全 r] (f : ι -> α)
  结论: Directed r f
  证明: fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩
-/
theorem Std.Total.directed [Std.Total r] (f : ι -> α) : Directed r f := fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩

/--
theorem `Std.Total.directedOn` / 定理 `Std.Total.directedOn`

English:
theorem Std.Total.directedOn
  given: [Std.Total r] (s : Set α)
  statement: DirectedOn r s
  proof: fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

@[simp]

中文:
定理 Std.全.directedOn
  条件: [Std.全 r] (s : 集合 α)
  结论: DirectedOn r s
  证明: fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

@[simp]
-/
theorem Std.Total.directedOn [Std.Total r] (s : Set α) : DirectedOn r s := fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

@[simp]
/--
theorem `DirectedOn.of_linearOrder` / 定理 `DirectedOn.of_linearOrder`

English:
theorem DirectedOn.of_linearOrder
  given: [LinearOrder α] (s : Set α)
  statement: DirectedOn (· <= ·) s
  proof: Std.Total.directedOn s

中文:
定理 DirectedOn.of_linearOrder
  条件: [线性序 α] (s : 集合 α)
  结论: DirectedOn (· <= ·) s
  证明: Std.Total.directedOn s

Depends on / 依赖: Std.Total.directedOn, directedOn
-/
theorem DirectedOn.of_linearOrder [LinearOrder α] (s : Set α) : DirectedOn (· <= ·) s :=
  Std.Total.directedOn s

/--
Definition of `IsDirected` / `IsDirected` 的定义

English:
class IsDirected
  parameters: (α : Sort*) (r : α -> α -> Prop)
  axioms and operations (1):
    - directed((a b : α)) : exists c, r a c ∧ r b c

中文:
类 是Directed
  参数: (α : 类型层*) (r : α -> α -> 命题)
  公理与运算 (1 个):
    - directed((a b : α)) : 存在 c, r a c ∧ r b c
-/
class IsDirected (α : Sort*) (r : α -> α -> Prop) : Prop where
  /-- For every pair of elements `a` and `b` there is a `c` such that `r a c` and `r b c` -/
  directed (a b : α) : exists c, r a c ∧ r b c

/-- A class for an `IsDirected` relation `≤`. -/
@[to_dual /-- A class for an `IsDirected` relation `≥`. -/]
/--
Definition of `IsDirectedOrder` / `IsDirectedOrder` 的定义

English:
abbreviation IsDirectedOrder
  signature: (α : Type*) [LE α]
  body: IsDirected α (· <= ·)

中文:
缩写 IsDirectedOrder
  签名: (α : 类型) [LE α]
  定义体: IsDirected α (· <= ·)

Depends on / 依赖: IsDirected
-/
abbrev IsDirectedOrder (α : Type*) [LE α] : Prop := IsDirected α (· <= ·)

/--
theorem `directed_of` / 定理 `directed_of`

English:
theorem directed_of
  given: (r : α -> α -> Prop) [IsDirected α r] (a b : α)
  statement: exists c, r a c ∧ r b c
  proof: IsDirected.directed _ _

中文:
定理 directed_of
  条件: (r : α -> α -> 命题) [是Directed α r] (a b : α)
  结论: 存在 c, r a c ∧ r b c
  证明: IsDirected.directed _ _

Depends on / 依赖: IsDirected, IsDirected.directed, directed
-/
theorem directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α) : exists c, r a c ∧ r b c :=
  IsDirected.directed _ _

/--
theorem `directed_of₃` / 定理 `directed_of₃`

English:
theorem directed_of₃
  given: (r : α -> α -> Prop) [IsDirected α r] [IsTrans α r] (a b c : α)
  proof: have ⟨e, hae, hbe⟩ := directed_of r a b
  have ⟨f, hef, hcf⟩ := directed_of r e c
  ⟨f, Trans.trans hae hef, Trans.trans hbe hef, hcf⟩

中文:
定理 directed_of₃
  条件: (r : α -> α -> 命题) [是Directed α r] [是Trans α r] (a b c : α)
  证明: have ⟨e, hae, hbe⟩ := directed_of r a b
  have ⟨f, hef, hcf⟩ := directed_of r e c
  ⟨f, Trans.trans hae hef, Trans.trans hbe hef, hcf⟩

Depends on / 依赖: Trans.trans, directed_of
-/
theorem directed_of₃ (r : α -> α -> Prop) [IsDirected α r] [IsTrans α r] (a b c : α) :
    exists d, r a d ∧ r b d ∧ r c d :=
  have ⟨e, hae, hbe⟩ := directed_of r a b
  have ⟨f, hef, hcf⟩ := directed_of r e c
  ⟨f, Trans.trans hae hef, Trans.trans hbe hef, hcf⟩

/--
theorem `isDirected_onFun` / 定理 `isDirected_onFun`

English:
theorem isDirected_onFun
  given: {f : ι -> α}
  statement: IsDirected ι (r on f) ↔ Directed r f
  proof: ⟨(·.directed), (⟨·⟩)⟩

中文:
定理 isDirected_onFun
  条件: {f : ι -> α}
  结论: 是Directed ι (r on f) ↔ Directed r f
  证明: ⟨(·.directed), (⟨·⟩)⟩

Depends on / 依赖: directed
-/
theorem isDirected_onFun {f : ι -> α} : IsDirected ι (r on f) ↔ Directed r f :=
  ⟨(·.directed), (⟨·⟩)⟩

/--
theorem `directed_id` / 定理 `directed_id`

English:
theorem directed_id
  given: [IsDirected α r]
  statement: Directed r id
  proof: directed_of r

中文:
定理 directed_id
  条件: [是Directed α r]
  结论: Directed r id
  证明: directed_of r

Depends on / 依赖: directed_of
-/
theorem directed_id [IsDirected α r] : Directed r id := directed_of r

/--
theorem `directed_id_iff` / 定理 `directed_id_iff`

English:
theorem directed_id_iff
  statement: Directed r id ↔ IsDirected α r
  proof: isDirected_onFun.symm

中文:
定理 directed_id_iff
  结论: Directed r id ↔ 是Directed α r
  证明: isDirected_onFun.symm

Depends on / 依赖: isDirected_onFun, isDirected_onFun.symm
-/
theorem directed_id_iff : Directed r id ↔ IsDirected α r :=
  isDirected_onFun.symm

/--
theorem `directedOn_univ` / 定理 `directedOn_univ`

English:
theorem directedOn_univ
  given: [IsDirected α r]
  statement: DirectedOn r Set.univ
  proof: fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩

中文:
定理 directedOn_univ
  条件: [是Directed α r]
  结论: DirectedOn r 集合.univ
  证明: fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩
-/
theorem directedOn_univ [IsDirected α r] : DirectedOn r Set.univ := fun a _ b _ =>
  let ⟨c, hc⟩ := directed_of r a b
  ⟨c, trivial, hc⟩

/--
theorem `directedOn_univ_iff` / 定理 `directedOn_univ_iff`

English:
theorem directedOn_univ_iff
  statement: DirectedOn r Set.univ ↔ IsDirected α r
  proof: ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩

中文:
定理 directedOn_univ_iff
  结论: DirectedOn r 集合.univ ↔ 是Directed α r
  证明: ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩

Depends on / 依赖: directedOn_univ
-/
theorem directedOn_univ_iff : DirectedOn r Set.univ ↔ IsDirected α r :=
  ⟨fun h =>
    ⟨fun a b =>
      let ⟨c, _, hc⟩ := h a trivial b trivial
      ⟨c, hc⟩⟩,
    @directedOn_univ _ _⟩

-- see Note [lower instance priority]
instance (priority := 100) Std.Total.to_isDirected [Std.Total r] : IsDirected α r :=
directed_id_iff.1 Std.Total.directed _

/--
theorem `isDirected_mono` / 定理 `isDirected_mono`

English:
theorem isDirected_mono
  given: [IsDirected α r] (h : forall ⦃a b⦄, r a b -> s a b)
  statement: IsDirected α s
  proof: ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩

@[to_dual exists_le_le]

中文:
定理 isDirected_mono
  条件: [是Directed α r] (h : 对任意 ⦃a b⦄, r a b -> s a b)
  结论: 是Directed α s
  证明: ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩

@[to_dual exists_le_le]

Depends on / 依赖: IsDirected, IsDirected.directed, directed
-/
theorem isDirected_mono [IsDirected α r] (h : forall ⦃a b⦄, r a b -> s a b) : IsDirected α s :=
  ⟨fun a b =>
    let ⟨c, ha, hb⟩ := IsDirected.directed a b
    ⟨c, h ha, h hb⟩⟩

@[to_dual exists_le_le]
/--
theorem `exists_ge_ge` / 定理 `exists_ge_ge`

English:
theorem exists_ge_ge
  given: [LE α] [IsDirectedOrder α] (a b : α)
  statement: exists c, a <= c ∧ b <= c
  proof: directed_of (· <= ·) a b

@[to_dual isDirected_le]

中文:
定理 存在_ge_ge
  条件: [LE α] [IsDirectedOrder α] (a b : α)
  结论: 存在 c, a <= c ∧ b <= c
  证明: directed_of (· <= ·) a b

@[to_dual isDirected_le]

Depends on / 依赖: directed_of
-/
theorem exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists c, a <= c ∧ b <= c :=
  directed_of (· <= ·) a b

@[to_dual isDirected_le]
/--
Instance `OrderDual.isDirected_ge` / 实例 `OrderDual.isDirected_ge`

English:
instance OrderDual.isDirected_ge
  signature: [LE α] [IsDirectedOrder α]
  body: by
  assumption

中文:
实例 OrderDual.isDirected_ge
  签名: [LE α] [IsDirectedOrder α]
  定义体: by
  assumption
-/
instance OrderDual.isDirected_ge [LE α] [IsDirectedOrder α] : IsCodirectedOrder αᵒᵈ := by
  assumption

/-- A monotone function on an upwards-directed type is directed. -/
@[to_dual (reorder := H (i j)) directed_of_isDirected_ge
/-- An antitone function on a downwards-directed type is directed. -/]
/--
theorem `directed_of_isDirected_le` / 定理 `directed_of_isDirected_le`

English:
theorem directed_of_isDirected_le
  statement: [LE α] [IsDirectedOrder α] {f : α -> β} {r : β -> β -> Prop}
  proof: directed_id.mono_comp _ H

@[to_dual directed_ge]

中文:
定理 directed_of_isDirected_le
  结论: [LE α] [IsDirectedOrder α] {f : α -> β} {r : β -> β -> 命题}
  证明: directed_id.mono_comp _ H

@[to_dual directed_ge]

Depends on / 依赖: directed_id, directed_id.mono_comp, mono_comp
-/
theorem directed_of_isDirected_le [LE α] [IsDirectedOrder α] {f : α -> β} {r : β -> β -> Prop}
    (H : forall ⦃i j⦄, i <= j -> r (f i) (f j)) : Directed r f :=
  directed_id.mono_comp _ H

@[to_dual directed_ge]
/--
theorem `Monotone.directed_le` / 定理 `Monotone.directed_le`

English:
theorem Monotone.directed_le
  given: [Preorder α] [IsDirectedOrder α] [Preorder β] {f : α -> β}
  proof: directed_of_isDirected_le

@[to_dual directed_ge]

中文:
定理 递增.directed_le
  条件: [预序 α] [IsDirectedOrder α] [预序 β] {f : α -> β}
  证明: directed_of_isDirected_le

@[to_dual directed_ge]

Depends on / 依赖: directed_of_isDirected_le
-/
theorem Monotone.directed_le [Preorder α] [IsDirectedOrder α] [Preorder β] {f : α -> β} :
    Monotone f -> Directed (· <= ·) f :=
  directed_of_isDirected_le

@[to_dual directed_ge]
/--
theorem `Antitone.directed_le` / 定理 `Antitone.directed_le`

English:
theorem Antitone.directed_le
  statement: [Preorder α] [IsCodirectedOrder α] [Preorder β] {f : α -> β}
  proof: directed_of_isDirected_ge hf

@[to_dual]

中文:
定理 递减.directed_le
  结论: [预序 α] [IsCodirectedOrder α] [预序 β] {f : α -> β}
  证明: directed_of_isDirected_ge hf

@[to_dual]

Depends on / 依赖: directed_of_isDirected_ge
-/
theorem Antitone.directed_le [Preorder α] [IsCodirectedOrder α] [Preorder β] {f : α -> β}
    (hf : Antitone f) : Directed (· <= ·) f :=
  directed_of_isDirected_ge hf

@[to_dual]
/--
lemma `directedOn_iff_isDirectedOrder` / 引理 `directedOn_iff_isDirectedOrder`

English:
lemma directedOn_iff_isDirectedOrder
  given: [LE α] {s : Set α}
  proof: by
  rw [directedOn_iff_directed]; rw [IsDirectedOrder]
  exact ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

@[to_dual]
alias ⟨DirectedOn.isDirectedOrder, DirectedOn.of_isDirectedOrder⟩ := directedOn_iff_isDirectedOrder

中文:
引理 directedOn_iff_isDirectedOrder
  条件: [LE α] {s : 集合 α}
  证明: by
  rw [directedOn_iff_directed]; rw [IsDirectedOrder]
  exact ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

@[to_dual]
alias ⟨DirectedOn.isDirectedOrder, DirectedOn.of_isDirectedOrder⟩ := directedOn_iff_isDirectedOrder

Depends on / 依赖: IsDirectedOrder, directedOn_iff_directed
-/
lemma directedOn_iff_isDirectedOrder [LE α] {s : Set α} :
    DirectedOn (· <= ·) s ↔ IsDirectedOrder s := by
  rw [directedOn_iff_directed]; rw [IsDirectedOrder]
  exact ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

@[to_dual]
alias ⟨DirectedOn.isDirectedOrder, DirectedOn.of_isDirectedOrder⟩ := directedOn_iff_isDirectedOrder

section Reflexive

/--
theorem `DirectedOn.insert` / 定理 `DirectedOn.insert`

English:
theorem DirectedOn.insert
  statement: [Std.Refl r] (a : α) {s : Set α} (hd : DirectedOn r s)
  proof: by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, refl _, refl _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩

中文:
定理 DirectedOn.insert
  结论: [Std.Refl r] (a : α) {s : 集合 α} (hd : DirectedOn r s)
  证明: by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, refl _, refl _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
-/
protected theorem DirectedOn.insert [Std.Refl r] (a : α) {s : Set α} (hd : DirectedOn r s)
    (ha : forall b in s, exists c in s, a ≼ c ∧ b ≼ c) : DirectedOn r (insert a s) := by
  rintro x (rfl | hx) y (rfl | hy)
  · exact ⟨y, Set.mem_insert _ _, refl _, refl _⟩
  · obtain ⟨w, hws, hwr⟩ := ha y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩
  · obtain ⟨w, hws, hwr⟩ := ha x hx
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr.symm⟩
  · obtain ⟨w, hws, hwr⟩ := hd x hx y hy
    exact ⟨w, Set.mem_insert_of_mem _ hws, hwr⟩

/--
theorem `directedOn_singleton` / 定理 `directedOn_singleton`

English:
theorem directedOn_singleton
  given: [Std.Refl r] (a : α)
  statement: DirectedOn r ({a} : Set α)
  proof: fun x hx _ hy => ⟨x, hx, refl _, hx.symm ▸ hy.symm ▸ refl _⟩

中文:
定理 directedOn_singleton
  条件: [Std.Refl r] (a : α)
  结论: DirectedOn r ({a} : 集合 α)
  证明: fun x hx _ hy => ⟨x, hx, refl _, hx.symm ▸ hy.symm ▸ refl _⟩

Depends on / 依赖: hx.symm, hy.symm
-/
theorem directedOn_singleton [Std.Refl r] (a : α) : DirectedOn r ({a} : Set α) :=
  fun x hx _ hy => ⟨x, hx, refl _, hx.symm ▸ hy.symm ▸ refl _⟩

/--
theorem `directedOn_pair` / 定理 `directedOn_pair`

English:
theorem directedOn_pair
  given: [Std.Refl r] {a b : α} (hab : a ≼ b)
  statement: DirectedOn r ({a, b} : Set α)
  proof: (directedOn_singleton _).insert _ fun c hc => ⟨c, hc, hc.symm ▸ hab, refl _⟩

中文:
定理 directedOn_pair
  条件: [Std.Refl r] {a b : α} (hab : a ≼ b)
  结论: DirectedOn r ({a, b} : 集合 α)
  证明: (directedOn_singleton _).insert _ fun c hc => ⟨c, hc, hc.symm ▸ hab, refl _⟩

Depends on / 依赖: directedOn_singleton, hc.symm, insert
-/
theorem directedOn_pair [Std.Refl r] {a b : α} (hab : a ≼ b) : DirectedOn r ({a, b} : Set α) :=
  (directedOn_singleton _).insert _ fun c hc => ⟨c, hc, hc.symm ▸ hab, refl _⟩

/--
theorem `directedOn_pair'` / 定理 `directedOn_pair'`

English:
theorem directedOn_pair'
  given: [Std.Refl r] {a b : α} (hab : a ≼ b)
  proof: by
  rw [Set.pair_comm]
  apply directedOn_pair hab

中文:
定理 directedOn_pair'
  条件: [Std.Refl r] {a b : α} (hab : a ≼ b)
  证明: by
  rw [Set.pair_comm]
  apply directedOn_pair hab

Depends on / 依赖: Set.pair_comm, directedOn_pair, pair_comm
-/
theorem directedOn_pair' [Std.Refl r] {a b : α} (hab : a ≼ b) :
    DirectedOn r ({b, a} : Set α) := by
  rw [Set.pair_comm]
  apply directedOn_pair hab

end Reflexive

section Preorder

variable [Preorder α] {a : α}

@[to_dual]
/--
theorem `IsMax.isTop` / 定理 `IsMax.isTop`

English:
theorem IsMax.isTop
  given: [IsDirectedOrder α] (h : IsMax a)
  statement: IsTop a
  proof: fun b =>
  let ⟨_, hca, hcb⟩ := exists_ge_ge a b
  hcb.trans (h hca)

@[to_dual]

中文:
定理 IsMax.isTop
  条件: [IsDirectedOrder α] (h : IsMax a)
  结论: IsTop a
  证明: fun b =>
  let ⟨_, hca, hcb⟩ := exists_ge_ge a b
  hcb.trans (h hca)

@[to_dual]
-/
protected theorem IsMax.isTop [IsDirectedOrder α] (h : IsMax a) : IsTop a := fun b =>
  let ⟨_, hca, hcb⟩ := exists_ge_ge a b
  hcb.trans (h hca)

@[to_dual]
/--
lemma `DirectedOn.is_top_of_is_max` / 引理 `DirectedOn.is_top_of_is_max`

English:
lemma DirectedOn.is_top_of_is_max
  statement: {s : Set α} (hd : DirectedOn (· <= ·) s)
  proof: fun a as =>
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  xa.trans (hmax x xs xm)

@[to_dual isBot_or_exists_lt]

中文:
引理 DirectedOn.is_top_of_is_max
  结论: {s : 集合 α} (hd : DirectedOn (· <= ·) s)
  证明: fun a as =>
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  xa.trans (hmax x xs xm)

@[to_dual isBot_or_exists_lt]
-/
lemma DirectedOn.is_top_of_is_max {s : Set α} (hd : DirectedOn (· <= ·) s)
    {m} (hm : m in s) (hmax : forall a in s, m <= a -> a <= m) : forall a in s, a <= m := fun a as =>
  let ⟨x, xs, xm, xa⟩ := hd m hm a as
  xa.trans (hmax x xs xm)

@[to_dual isBot_or_exists_lt]
/--
theorem `isTop_or_exists_gt` / 定理 `isTop_or_exists_gt`

English:
theorem isTop_or_exists_gt
  given: [IsDirectedOrder α] (a : α)
  statement: IsTop a ∨ exists b, a < b
  proof: (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp

@[to_dual]

中文:
定理 isTop_or_存在_gt
  条件: [IsDirectedOrder α] (a : α)
  结论: IsTop a ∨ 存在 b, a < b
  证明: (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp

@[to_dual]

Depends on / 依赖: IsMax.isTop, not_isMax_iff, not_isMax_iff.mp
-/
theorem isTop_or_exists_gt [IsDirectedOrder α] (a : α) : IsTop a ∨ exists b, a < b :=
  (em (IsMax a)).imp IsMax.isTop not_isMax_iff.mp

@[to_dual]
/--
theorem `isTop_iff_isMax` / 定理 `isTop_iff_isMax`

English:
theorem isTop_iff_isMax
  given: [IsDirectedOrder α]
  statement: IsTop a ↔ IsMax a
  proof: ⟨IsTop.isMax, IsMax.isTop⟩

中文:
定理 isTop_iff_isMax
  条件: [IsDirectedOrder α]
  结论: IsTop a ↔ IsMax a
  证明: ⟨IsTop.isMax, IsMax.isTop⟩

Depends on / 依赖: IsMax.isTop, IsTop.isMax
-/
theorem isTop_iff_isMax [IsDirectedOrder α] : IsTop a ↔ IsMax a :=
  ⟨IsTop.isMax, IsMax.isTop⟩

/--
theorem `Monotone.forall_le_of_antitone` / 定理 `Monotone.forall_le_of_antitone`

English:
theorem Monotone.forall_le_of_antitone
  statement: [IsDirectedOrder α] [Preorder β] {f g : α -> β}
  proof: by
  obtain ⟨k, hkm, hkn⟩ := exists_ge_ge m n
  calc
    f m <= f k := hf hkm
    _ <= g k := h _
    _ <= g n := hg hkn

中文:
定理 递增.对任意_le_of_antitone
  结论: [IsDirectedOrder α] [预序 β] {f g : α -> β}
  证明: by
  obtain ⟨k, hkm, hkn⟩ := exists_ge_ge m n
  calc
    f m <= f k := hf hkm
    _ <= g k := h _
    _ <= g n := hg hkn

Depends on / 依赖: exists_ge_ge
-/
theorem Monotone.forall_le_of_antitone [IsDirectedOrder α] [Preorder β] {f g : α -> β}
    (hf : Monotone f) (hg : Antitone g) (h : f <= g) (m n : α) : f m <= g n := by
  obtain ⟨k, hkm, hkn⟩ := exists_ge_ge m n
  calc
    f m <= f k := hf hkm
    _ <= g k := h _
    _ <= g n := hg hkn

end Preorder

section PartialOrder

variable [PartialOrder β]

section Nontrivial

variable [Nontrivial β]

variable (β) in
@[to_dual exists_lt_of_directed_le]
/--
theorem `exists_lt_of_directed_ge` / 定理 `exists_lt_of_directed_ge`

English:
theorem exists_lt_of_directed_ge
  given: [IsCodirectedOrder β]
  proof: by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

@[to_dual]

中文:
定理 存在_lt_of_directed_ge
  条件: [IsCodirectedOrder β]
  证明: by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

@[to_dual]

Depends on / 依赖: exacts, exists_pair_ne, isBot_or_exists_lt, lt_of_ne
-/
theorem exists_lt_of_directed_ge [IsCodirectedOrder β] :
    exists a b : β, a < b := by
  rcases exists_pair_ne β with ⟨a, b, hne⟩
  rcases isBot_or_exists_lt a with (ha | ⟨c, hc⟩)
  exacts [⟨a, b, (ha b).lt_of_ne hne⟩, ⟨_, _, hc⟩]

@[to_dual]
/--
theorem `IsMax.not_isMin` / 定理 `IsMax.not_isMin`

English:
theorem IsMax.not_isMin
  given: [IsDirectedOrder β] {b : β} (hb : IsMax b)
  statement: ¬ IsMin b
  proof: by
  intro hb'
  obtain ⟨a, c, hac⟩ := exists_lt_of_directed_le β
  have := hb.isTop a
  obtain rfl := (hb' <| this).antisymm this
  exact hb'.not_lt hac

@[to_dual]

中文:
定理 IsMax.not_isMin
  条件: [IsDirectedOrder β] {b : β} (hb : IsMax b)
  结论: ¬ IsMin b
  证明: by
  intro hb'
  obtain ⟨a, c, hac⟩ := exists_lt_of_directed_le β
  have := hb.isTop a
  obtain rfl := (hb' <| this).antisymm this
  exact hb'.not_lt hac

@[to_dual]
-/
protected theorem IsMax.not_isMin [IsDirectedOrder β] {b : β} (hb : IsMax b) : ¬ IsMin b := by
  intro hb'
  obtain ⟨a, c, hac⟩ := exists_lt_of_directed_le β
  have := hb.isTop a
  obtain rfl := (hb' <| this).antisymm this
  exact hb'.not_lt hac

@[to_dual]
/--
theorem `IsMin.not_isMax'` / 定理 `IsMin.not_isMax'`

English:
theorem IsMin.not_isMax'
  given: [IsDirectedOrder β] {b : β} (hb : IsMin b)
  statement: ¬ IsMax b
  proof: fun hb' => hb'.toDual.not_isMax hb.toDual

中文:
定理 IsMin.not_isMax'
  条件: [IsDirectedOrder β] {b : β} (hb : IsMin b)
  结论: ¬ IsMax b
  证明: fun hb' => hb'.toDual.not_isMax hb.toDual
-/
protected theorem IsMin.not_isMax' [IsDirectedOrder β] {b : β} (hb : IsMin b) : ¬ IsMax b :=
  fun hb' => hb'.toDual.not_isMax hb.toDual

end Nontrivial

variable [Preorder α] {f : α -> β} {s : Set α}

-- TODO: Generalise the following two lemmas to connected orders

/--
lemma `constant_of_monotone_antitone` / 引理 `constant_of_monotone_antitone`

English:
lemma constant_of_monotone_antitone
  statement: [IsDirectedOrder α] (hf : Monotone f) (hf' : Antitone f)
  proof: by
  have := hf.forall_le_of_antitone hf' le_rfl
  exact le_antisymm (this a b) (this b a)

中文:
引理 constant_of_monotone_antitone
  结论: [IsDirectedOrder α] (hf : 递增 f) (hf' : 递减 f)
  证明: by
  have := hf.forall_le_of_antitone hf' le_rfl
  exact le_antisymm (this a b) (this b a)

Depends on / 依赖: forall_le_of_antitone, hf.forall_le_of_antitone, le_antisymm, le_rfl
-/
lemma constant_of_monotone_antitone [IsDirectedOrder α] (hf : Monotone f) (hf' : Antitone f)
    (a b : α) : f a = f b := by
  have := hf.forall_le_of_antitone hf' le_rfl
  exact le_antisymm (this a b) (this b a)

/--
lemma `constant_of_monotoneOn_antitoneOn` / 引理 `constant_of_monotoneOn_antitoneOn`

English:
lemma constant_of_monotoneOn_antitoneOn
  statement: (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
  proof: by
  rintro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans <| hf' hb hc hbc) ((hf hb hc hbc).trans <| hf' ha hc hac)

中文:
引理 constant_of_monotoneOn_antitoneOn
  结论: (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
  证明: by
  rintro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans <| hf' hb hc hbc) ((hf hb hc hbc).trans <| hf' ha hc hac)

Depends on / 依赖: le_antisymm
-/
lemma constant_of_monotoneOn_antitoneOn (hf : MonotoneOn f s) (hf' : AntitoneOn f s)
    (hs : DirectedOn (· <= ·) s) : forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> f a = f b := by
  rintro a ha b hb
  obtain ⟨c, hc, hac, hbc⟩ := hs _ ha _ hb
  exact le_antisymm ((hf ha hc hac).trans <| hf' hb hc hbc) ((hf hb hc hbc).trans <| hf' ha hc hac)

end PartialOrder

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) SemilatticeSup.instIsDirectedOrder [SemilatticeSup α] :
    IsDirectedOrder α :=
  ⟨fun a b => ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderTop.instIsDirectedOrder [LE α] [OrderTop α] : IsDirectedOrder α :=
  ⟨fun _ _ => ⟨⊤, le_top _, le_top _⟩⟩

namespace DirectedOn

section Pi

variable {ι : Type*} {α : ι -> Type*} {r : (i : ι) -> α i -> α i -> Prop}

/--
lemma `proj` / 引理 `proj`

English:
lemma proj
  given: {d : Set (Π i, α i)} (hd : DirectedOn (fun x y => forall i, r i (x i) (y i)) d) (i : ι)
  proof: DirectedOn.mono_comp (fun _ _ h => h) (mono hd fun ⦃_ _⦄ h => h i)

中文:
引理 proj
  条件: {d : 集合 (Π i, α i)} (hd : DirectedOn (fun x y => 对任意 i, r i (x i) (y i)) d) (i : ι)
  证明: DirectedOn.mono_comp (fun _ _ h => h) (mono hd fun ⦃_ _⦄ h => h i)

Depends on / 依赖: DirectedOn, DirectedOn.mono_comp, mono_comp
-/
lemma proj {d : Set (Π i, α i)} (hd : DirectedOn (fun x y => forall i, r i (x i) (y i)) d) (i : ι) :
    DirectedOn (r i) ((fun a => a i) '' d) :=
  DirectedOn.mono_comp (fun _ _ h => h) (mono hd fun ⦃_ _⦄ h => h i)

/--
lemma `pi` / 引理 `pi`

English:
lemma pi
  given: {d : (i : ι) -> Set (α i)} (hd : forall (i : ι), DirectedOn (r i) (d i))
  proof: by
  intro a ha b hb
  choose f hfd haf hbf using fun i => hd i (a i) (ha i trivial) (b i) (hb i trivial)
  exact ⟨f, fun i _ => hfd i, haf, hbf⟩

中文:
引理 pi
  条件: {d : (i : ι) -> 集合 (α i)} (hd : 对任意 (i : ι), DirectedOn (r i) (d i))
  证明: by
  intro a ha b hb
  choose f hfd haf hbf using fun i => hd i (a i) (ha i trivial) (b i) (hb i trivial)
  exact ⟨f, fun i _ => hfd i, haf, hbf⟩
-/
lemma pi {d : (i : ι) -> Set (α i)} (hd : forall (i : ι), DirectedOn (r i) (d i)) :
    DirectedOn (fun x y => forall i, r i (x i) (y i)) (Set.pi Set.univ d) := by
  intro a ha b hb
  choose f hfd haf hbf using fun i => hd i (a i) (ha i trivial) (b i) (hb i trivial)
  exact ⟨f, fun i _ => hfd i, haf, hbf⟩

end Pi

section Prod

variable {r₂ : β -> β -> Prop}

/-- Local notation for a relation -/
local infixl:50 " ≼₁ " => r
/-- Local notation for a relation -/
local infixl:50 " ≼₂ " => r₂

/--
lemma `fst` / 引理 `fst`

English:
lemma fst
  given: {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d)
  proof: DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.1)

中文:
引理 fst
  条件: {d : 集合 (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d)
  证明: DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.1)

Depends on / 依赖: DirectedOn, DirectedOn.mono_comp, mono_comp
-/
lemma fst {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    DirectedOn (· ≼₁ ·) (Prod.fst '' d) :=
  DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.1)

/--
lemma `snd` / 引理 `snd`

English:
lemma snd
  given: {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d)
  proof: DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.2)

中文:
引理 snd
  条件: {d : 集合 (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d)
  证明: DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.2)

Depends on / 依赖: DirectedOn, DirectedOn.mono_comp, mono_comp
-/
lemma snd {d : Set (α × β)} (hd : DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) d) :
    DirectedOn (· ≼₂ ·) (Prod.snd '' d) :=
  DirectedOn.mono_comp (fun ⦃_ _⦄ h => h) (mono hd fun ⦃_ _⦄ h => h.2)

/--
lemma `prod` / 引理 `prod`

English:
lemma prod
  given: {d₁ : Set α} {d₂ : Set β} (h₁ : DirectedOn (· ≼₁ ·) d₁) (h₂ : DirectedOn (· ≼₂ ·) d₂)
  proof: fun _ hpd _ hqd => by
  obtain ⟨r₁, hdr₁, hpr₁, hqr₁⟩ := h₁ _ hpd.1 _ hqd.1
  obtain ⟨r₂, hdr₂, hpr₂, hqr₂⟩ := h₂ _ hpd.2 _ hqd.2
  exact ⟨⟨r₁, r₂⟩, ⟨hdr₁, hdr₂⟩, ⟨hpr₁, hpr₂⟩, ⟨hqr₁, hqr₂⟩⟩

中文:
引理 乘积
  条件: {d₁ : 集合 α} {d₂ : 集合 β} (h₁ : DirectedOn (· ≼₁ ·) d₁) (h₂ : DirectedOn (· ≼₂ ·) d₂)
  证明: fun _ hpd _ hqd => by
  obtain ⟨r₁, hdr₁, hpr₁, hqr₁⟩ := h₁ _ hpd.1 _ hqd.1
  obtain ⟨r₂, hdr₂, hpr₂, hqr₂⟩ := h₂ _ hpd.2 _ hqd.2
  exact ⟨⟨r₁, r₂⟩, ⟨hdr₁, hdr₂⟩, ⟨hpr₁, hpr₂⟩, ⟨hqr₁, hqr₂⟩⟩
-/
lemma prod {d₁ : Set α} {d₂ : Set β} (h₁ : DirectedOn (· ≼₁ ·) d₁) (h₂ : DirectedOn (· ≼₂ ·) d₂) :
    DirectedOn (fun p q => p.1 ≼₁ q.1 ∧ p.2 ≼₂ q.2) (d₁ ×ˢ d₂) := fun _ hpd _ hqd => by
  obtain ⟨r₁, hdr₁, hpr₁, hqr₁⟩ := h₁ _ hpd.1 _ hqd.1
  obtain ⟨r₂, hdr₂, hpr₂, hqr₂⟩ := h₂ _ hpd.2 _ hqd.2
  exact ⟨⟨r₁, r₂⟩, ⟨hdr₁, hdr₂⟩, ⟨hpr₁, hpr₂⟩, ⟨hqr₁, hqr₂⟩⟩

end Prod

end DirectedOn
