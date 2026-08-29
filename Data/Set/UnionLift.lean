/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Directed

/-!
# Union lift

This file defines `Set.iUnionLift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `Set.iUnionLift` - Given a Union of sets `iUnion S`, define a function on any subset of the Union
  by defining it on each component, and proving that it agrees on the intersections.
* `Set.liftCover` - Version of `Set.iUnionLift` for the special case that the sets cover the
  entire type.

## Main statements

There are proofs of the obvious properties of `iUnionLift`, i.e. what it does to elements of
each of the sets in the `iUnion`, stated in different ways.

There are also three lemmas about `iUnionLift` intended to aid with proving that `iUnionLift` is a
homomorphism when defined on a Union of substructures. There is one lemma each to show that
constants, unary functions, or binary functions are preserved. These lemmas are:

* `Set.iUnionLift_const`
* `Set.iUnionLift_unary`
* `Set.iUnionLift_binary`

## Tags

directed union, directed supremum, glue, gluing
-/

@[expose] public section

variable {α : Type*} {ι β : Sort _}

namespace Set

section UnionLift

/- The unused argument is left in the definition so that the `simp` lemmas
`iUnionLift_inclusion` will work without the user having to provide it explicitly to
simplify terms involving `iUnionLift`. -/
/-- Given a union of sets `iUnion S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unusedArguments]
/--
Definition of `iUnionLift` / `iUnionLift` 的定义

English:
definition iUnionLift
  signature: (S : ι -> Set α) (f : forall i, S i -> β)
  body: let i := Classical.indefiniteDescription _ (mem_iUnion.1 (hT x.prop))
  f i ⟨x, i.prop⟩

中文:
定义 iUnionLift
  签名: (S : ι -> 集合 α) (f : 对任意 i, S i -> β)
  定义体: let i := Classical.indefiniteDescription _ (mem_iUnion.1 (hT x.prop))
  f i ⟨x, i.prop⟩

Depends on / 依赖: Classical, Classical.indefiniteDescription, i.prop, indefiniteDescription, mem_iUnion, x.prop
-/
noncomputable def iUnionLift (S : ι -> Set α) (f : forall i, S i -> β)
    (_ : forall (i j) (x : α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α)
    (hT : T subseteq iUnion S) (x : T) : β :=
  let i := Classical.indefiniteDescription _ (mem_iUnion.1 (hT x.prop))
  f i ⟨x, i.prop⟩

variable {S : ι -> Set α} {f : forall i, S i -> β}
  {hf : forall (i j) (x : α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α}
  {hT : T subseteq iUnion S} (hT' : T = iUnion S)

@[simp]
/--
theorem `iUnionLift_mk` / 定理 `iUnionLift_mk`

English:
theorem iUnionLift_mk
  given: {i : ι} (x : S i) (hx : (x : α) in T)
  proof: hf _ i x _ _

中文:
定理 iUnionLift_mk
  条件: {i : ι} (x : S i) (hx : (x : α) in T)
  证明: hf _ i x _ _
-/
theorem iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) :
    iUnionLift S f hf T hT ⟨x, hx⟩ = f i x := hf _ i x _ _

/--
theorem `iUnionLift_inclusion` / 定理 `iUnionLift_inclusion`

English:
theorem iUnionLift_inclusion
  given: {i : ι} (x : S i) (h : S i subseteq T)
  proof: iUnionLift_mk x _

中文:
定理 iUnionLift_inclusion
  条件: {i : ι} (x : S i) (h : S i subseteq T)
  证明: iUnionLift_mk x _

Depends on / 依赖: iUnionLift_mk
-/
theorem iUnionLift_inclusion {i : ι} (x : S i) (h : S i subseteq T) :
    iUnionLift S f hf T hT (Set.inclusion h x) = f i x :=
  iUnionLift_mk x _

/--
theorem `iUnionLift_of_mem` / 定理 `iUnionLift_of_mem`

English:
theorem iUnionLift_of_mem
  given: (x : T) {i : ι} (hx : (x : α) in S i)
  proof: by obtain ⟨x, hx⟩ := x; exact hf _ _ _ _ _

中文:
定理 iUnionLift_of_mem
  条件: (x : T) {i : ι} (hx : (x : α) in S i)
  证明: by obtain ⟨x, hx⟩ := x; exact hf _ _ _ _ _
-/
theorem iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) in S i) :
    iUnionLift S f hf T hT x = f i ⟨x, hx⟩ := by obtain ⟨x, hx⟩ := x; exact hf _ _ _ _ _

/--
theorem `preimage_iUnionLift` / 定理 `preimage_iUnionLift`

English:
theorem preimage_iUnionLift
  given: (t : Set β)
  proof: by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_image]
  constructor
  · rcases mem_iUnion.1 (hT x.prop) with ⟨i, hi⟩
    refine fun h => ⟨i, ⟨x, hi⟩, ?_, rfl⟩
    rwa [iUnionLift_of_mem x hi] at h
  · rintro ⟨i, ⟨y, hi⟩, h, hxy⟩
    obtain rfl : y = x := congr_arg Subtype.val hxy
    rwa [iUn

中文:
定理 preimage_iUnionLift
  条件: (t : 集合 β)
  证明: by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_image]
  constructor
  · rcases mem_iUnion.1 (hT x.prop) with ⟨i, hi⟩
    refine fun h => ⟨i, ⟨x, hi⟩, ?_, rfl⟩
    rwa [iUnionLift_of_mem x hi] at h
  · rintro ⟨i, ⟨y, hi⟩, h, hxy⟩
    obtain rfl : y = x := congr_arg Subtype.val hxy
    rwa [iUn

Depends on / 依赖: Subtype, Subtype.val, congr_arg, iUnionLift_of_mem, mem_iUnion, mem_image, mem_preimage, x.prop
-/
theorem preimage_iUnionLift (t : Set β) :
    iUnionLift S f hf T hT ⁻¹' t =
      inclusion hT ⁻¹' (⋃ i, inclusion (subset_iUnion S i) '' f i ⁻¹' t) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_image]
  constructor
  · rcases mem_iUnion.1 (hT x.prop) with ⟨i, hi⟩
    refine fun h => ⟨i, ⟨x, hi⟩, ?_, rfl⟩
    rwa [iUnionLift_of_mem x hi] at h
  · rintro ⟨i, ⟨y, hi⟩, h, hxy⟩
    obtain rfl : y = x := congr_arg Subtype.val hxy
    rwa [iUnionLift_of_mem x hi]

/--
theorem `iUnionLift_const` / 定理 `iUnionLift_const`

English:
theorem iUnionLift_const
  statement: (c : T) (ci : forall i, S i) (hci : forall i, (ci i : α) = c) (cβ : β)
  proof: by
  let ⟨i, hi⟩ := Set.mem_iUnion.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [iUnionLift_of_mem _ hi]; rw [← this]; rw [h]

中文:
定理 iUnionLift_const
  结论: (c : T) (ci : 对任意 i, S i) (hci : 对任意 i, (ci i : α) = c) (cβ : β)
  证明: by
  let ⟨i, hi⟩ := Set.mem_iUnion.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [iUnionLift_of_mem _ hi]; rw [← this]; rw [h]

Depends on / 依赖: Set.mem_iUnion, Subtype, Subtype.ext, c.prop, iUnionLift_of_mem, mem_iUnion
-/
theorem iUnionLift_const (c : T) (ci : forall i, S i) (hci : forall i, (ci i : α) = c) (cβ : β)
    (h : forall i, f i (ci i) = cβ) : iUnionLift S f hf T hT c = cβ := by
  let ⟨i, hi⟩ := Set.mem_iUnion.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [iUnionLift_of_mem _ hi]; rw [← this]; rw [h]

/--
theorem `iUnionLift_unary` / 定理 `iUnionLift_unary`

English:
theorem iUnionLift_unary
  statement: (u : T -> T) (ui : forall i, S i -> S i)
  proof: by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  rw [iUnionLift_of_mem x hi]; rw [← h i]
  have : x = Set.inclusion (Set.subset_iUnion S i) ⟨x, hi⟩ := by
    cases x
    rfl
  conv_lhs => rw [this, hui, iUnionLift_inclusion]

中文:
定理 iUnionLift_unary
  结论: (u : T -> T) (ui : 对任意 i, S i -> S i)
  证明: by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  rw [iUnionLift_of_mem x hi]; rw [← h i]
  have : x = Set.inclusion (Set.subset_iUnion S i) ⟨x, hi⟩ := by
    cases x
    rfl
  conv_lhs => rw [this, hui, iUnionLift_inclusion]

Depends on / 依赖: Set.inclusion, Set.mem_iUnion, Set.subset_iUnion, conv_lhs, iUnionLift_inclusion, iUnionLift_of_mem, inclusion, mem_iUnion, subset_iUnion, x.prop
-/
theorem iUnionLift_unary (u : T -> T) (ui : forall i, S i -> S i)
    (hui :
      forall (i) (x : S i),
        u (Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) x) =
          Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) (ui i x))
    (uβ : β -> β) (h : forall (i) (x : S i), f i (ui i x) = uβ (f i x)) (x : T) :
    iUnionLift S f hf T (le_of_eq hT') (u x) = uβ (iUnionLift S f hf T (le_of_eq hT') x) := by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  rw [iUnionLift_of_mem x hi]; rw [← h i]
  have : x = Set.inclusion (Set.subset_iUnion S i) ⟨x, hi⟩ := by
    cases x
    rfl
  conv_lhs => rw [this, hui, iUnionLift_inclusion]

/--
theorem `iUnionLift_binary` / 定理 `iUnionLift_binary`

English:
theorem iUnionLift_binary
  statement: (dir : Directed (· <= ·) S) (op : T -> T -> T) (opi : forall i, S i -> S i -> S i)
  proof: by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 y.prop
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [iUnionLift_of_mem x (hik hi)]; rw [iUnionLift_of_mem y (hjk hj)]; rw [← h k]
  have hx : x = Set.inclusion (Set.subset_iUnion S k) ⟨x, hik hi⟩ := by
    ca

中文:
定理 iUnionLift_binary
  结论: (dir : Directed (· <= ·) S) (op : T -> T -> T) (opi : 对任意 i, S i -> S i -> S i)
  证明: by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 y.prop
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [iUnionLift_of_mem x (hik hi)]; rw [iUnionLift_of_mem y (hjk hj)]; rw [← h k]
  have hx : x = Set.inclusion (Set.subset_iUnion S k) ⟨x, hik hi⟩ := by
    ca

Depends on / 依赖: Set.inclusion, Set.mem_iUnion, Set.subset_iUnion, iUnionLift_of_mem, inclusion, mem_iUnion, subset_iUnion, x.prop, y.prop
-/
theorem iUnionLift_binary (dir : Directed (· <= ·) S) (op : T -> T -> T) (opi : forall i, S i -> S i -> S i)
    (hopi :
      forall i x y,
        Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) (opi i x y) =
          op (Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) x)
            (Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) y))
    (opβ : β -> β -> β) (h : forall (i) (x y : S i), f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) :
    iUnionLift S f hf T (le_of_eq hT') (op x y) =
      opβ (iUnionLift S f hf T (le_of_eq hT') x) (iUnionLift S f hf T (le_of_eq hT') y) := by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 y.prop
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [iUnionLift_of_mem x (hik hi)]; rw [iUnionLift_of_mem y (hjk hj)]; rw [← h k]
  have hx : x = Set.inclusion (Set.subset_iUnion S k) ⟨x, hik hi⟩ := by
    cases x
    rfl
  have hy : y = Set.inclusion (Set.subset_iUnion S k) ⟨y, hjk hj⟩ := by
    cases y
    rfl
  have hxy : (Set.inclusion (Set.subset_iUnion S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) in S k :=
    (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).prop
  conv_lhs => rw [hx, hy, ← hopi, iUnionLift_of_mem _ hxy]

end UnionLift

variable {S : ι -> Set α} {f : forall i, S i -> β}
  {hf : forall (i j) (x : α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {hS : iUnion S = univ}

/--
Definition of `liftCover` / `liftCover` 的定义

English:
definition liftCover
  signature: (S : ι -> Set α) (f : forall i, S i -> β)
  body: iUnionLift S f hf univ hS.symm.subset ⟨a, trivial⟩

@[simp]

中文:
定义 liftCover
  签名: (S : ι -> 集合 α) (f : 对任意 i, S i -> β)
  定义体: iUnionLift S f hf univ hS.symm.subset ⟨a, trivial⟩

@[simp]

Depends on / 依赖: hS.symm.subset, iUnionLift, subset
-/
noncomputable def liftCover (S : ι -> Set α) (f : forall i, S i -> β)
    (hf : forall (i j) (x : α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hS : iUnion S = univ) (a : α) : β :=
  iUnionLift S f hf univ hS.symm.subset ⟨a, trivial⟩

@[simp]
/--
theorem `liftCover_coe` / 定理 `liftCover_coe`

English:
theorem liftCover_coe
  given: {i : ι} (x : S i)
  statement: liftCover S f hf hS x = f i x
  proof: iUnionLift_mk x _

中文:
定理 liftCover_coe
  条件: {i : ι} (x : S i)
  结论: liftCover S f hf hS x = f i x
  证明: iUnionLift_mk x _

Depends on / 依赖: iUnionLift_mk
-/
theorem liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS x = f i x :=
  iUnionLift_mk x _

/--
theorem `liftCover_of_mem` / 定理 `liftCover_of_mem`

English:
theorem liftCover_of_mem
  given: {i : ι} {x : α} (hx : (x : α) in S i)
  proof: iUnionLift_of_mem ⟨x, mem_univ x⟩ hx

中文:
定理 liftCover_of_mem
  条件: {i : ι} {x : α} (hx : (x : α) in S i)
  证明: iUnionLift_of_mem ⟨x, mem_univ x⟩ hx

Depends on / 依赖: iUnionLift_of_mem, mem_univ
-/
theorem liftCover_of_mem {i : ι} {x : α} (hx : (x : α) in S i) :
    liftCover S f hf hS x = f i ⟨x, hx⟩ :=
  iUnionLift_of_mem ⟨x, mem_univ x⟩ hx

/--
theorem `preimage_liftCover` / 定理 `preimage_liftCover`

English:
theorem preimage_liftCover
  given: (t : Set β)
  statement: liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t
  proof: by
  change (iUnionLift S f hf univ hS.symm.subset ∘ fun a => ⟨a, mem_univ a⟩) ⁻¹' t = _
  rw [preimage_comp]; rw [preimage_iUnionLift]
  ext; simp

中文:
定理 preimage_liftCover
  条件: (t : 集合 β)
  结论: liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t
  证明: by
  change (iUnionLift S f hf univ hS.symm.subset ∘ fun a => ⟨a, mem_univ a⟩) ⁻¹' t = _
  rw [preimage_comp]; rw [preimage_iUnionLift]
  ext; simp

Depends on / 依赖: hS.symm.subset, iUnionLift, mem_univ, preimage_comp, preimage_iUnionLift, subset
-/
theorem preimage_liftCover (t : Set β) : liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t := by
  change (iUnionLift S f hf univ hS.symm.subset ∘ fun a => ⟨a, mem_univ a⟩) ⁻¹' t = _
  rw [preimage_comp]; rw [preimage_iUnionLift]
  ext; simp

end Set
