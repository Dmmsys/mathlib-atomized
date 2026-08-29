/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.Defs

/-!
# Locus of unequal values of finitely supported dependent functions

Let `N : α → Type*` be a type family, assume that `N a` has a `0` for all `a : α` and let
`f g : Π₀ a, N a` be finitely supported dependent functions.

## Main definition

* `DFinsupp.neLocus f g : Finset α`, the finite subset of `α` where `f` and `g` differ.
  In the case in which `N a` is an additive group for all `a`, `DFinsupp.neLocus f g` coincides with
  `DFinsupp.support (f - g)`.
-/

@[expose] public section


variable {α : Type*} {N : α -> Type*}

namespace DFinsupp

variable [DecidableEq α]

section NHasZero

variable [forall a, DecidableEq (N a)] [forall a, Zero (N a)] (f g : Π₀ a, N a)

/--
Definition of `neLocus` / `neLocus` 的定义

English:
definition neLocus
  signature: (f g : Π₀ a, N a)
  body: (f.support union g.support).filter fun x => f x != g x

@[simp]

中文:
定义 neLocus
  签名: (f g : Π₀ a, N a)
  定义体: (f.support union g.support).filter fun x => f x != g x

@[simp]

Depends on / 依赖: f.support, filter, g.support, support
-/
def neLocus (f g : Π₀ a, N a) : Finset α :=
  (f.support union g.support).filter fun x => f x != g x

@[simp]
/--
theorem `mem_neLocus` / 定理 `mem_neLocus`

English:
theorem mem_neLocus
  given: {f g : Π₀ a, N a} {a : α}
  statement: a in f.neLocus g ↔ f a != g a
  proof: by
  simpa only [neLocus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _

中文:
定理 mem_neLocus
  条件: {f g : Π₀ a, N a} {a : α}
  结论: a in f.neLocus g ↔ f a != g a
  证明: by
  simpa only [neLocus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_union, Ne.ne_or_ne, and_iff_right_iff_imp, mem_filter, mem_support_iff, mem_union, neLocus, ne_or_ne
-/
theorem mem_neLocus {f g : Π₀ a, N a} {a : α} : a in f.neLocus g ↔ f a != g a := by
  simpa only [neLocus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _

/--
theorem `notMem_neLocus` / 定理 `notMem_neLocus`

English:
theorem notMem_neLocus
  given: {f g : Π₀ a, N a} {a : α}
  statement: a ∉ f.neLocus g ↔ f a = g a
  proof: mem_neLocus.not.trans not_ne_iff

@[simp]

中文:
定理 notMem_neLocus
  条件: {f g : Π₀ a, N a} {a : α}
  结论: a ∉ f.neLocus g ↔ f a = g a
  证明: mem_neLocus.not.trans not_ne_iff

@[simp]

Depends on / 依赖: mem_neLocus, mem_neLocus.not.trans, not_ne_iff
-/
theorem notMem_neLocus {f g : Π₀ a, N a} {a : α} : a ∉ f.neLocus g ↔ f a = g a :=
  mem_neLocus.not.trans not_ne_iff

@[simp]
/--
theorem `coe_neLocus` / 定理 `coe_neLocus`

English:
theorem coe_neLocus
  statement: ↑(f.neLocus g) = { x | f x != g x }
  proof: Set.ext fun _x => mem_neLocus

@[simp]

中文:
定理 coe_neLocus
  结论: ↑(f.neLocus g) = { x | f x != g x }
  证明: Set.ext fun _x => mem_neLocus

@[simp]

Depends on / 依赖: Set.ext, mem_neLocus
-/
theorem coe_neLocus : ↑(f.neLocus g) = { x | f x != g x } :=
  Set.ext fun _x => mem_neLocus

@[simp]
/--
theorem `neLocus_eq_empty` / 定理 `neLocus_eq_empty`

English:
theorem neLocus_eq_empty
  given: {f g : Π₀ a, N a}
  statement: f.neLocus g = ∅ ↔ f = g
  proof: ⟨fun h =>
    ext fun a => not_not.mp (mem_neLocus.not.mp (Finset.eq_empty_iff_forall_notMem.mp h a)),
    fun h => h ▸ by simp only [neLocus, Ne, not_true, Finset.filter_false]⟩

@[simp]

中文:
定理 neLocus_eq_empty
  条件: {f g : Π₀ a, N a}
  结论: f.neLocus g = ∅ ↔ f = g
  证明: ⟨fun h =>
    ext fun a => not_not.mp (mem_neLocus.not.mp (Finset.eq_empty_iff_forall_notMem.mp h a)),
    fun h => h ▸ by simp only [neLocus, Ne, not_true, Finset.filter_false]⟩

@[simp]

Depends on / 依赖: Finset, Finset.eq_empty_iff_forall_notMem.mp, Finset.filter_false, eq_empty_iff_forall_notMem, filter_false, mem_neLocus, mem_neLocus.not.mp, neLocus, not_not, not_not.mp, not_true
-/
theorem neLocus_eq_empty {f g : Π₀ a, N a} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h =>
    ext fun a => not_not.mp (mem_neLocus.not.mp (Finset.eq_empty_iff_forall_notMem.mp h a)),
    fun h => h ▸ by simp only [neLocus, Ne, not_true, Finset.filter_false]⟩

@[simp]
/--
theorem `nonempty_neLocus_iff` / 定理 `nonempty_neLocus_iff`

English:
theorem nonempty_neLocus_iff
  given: {f g : Π₀ a, N a}
  statement: (f.neLocus g).Nonempty ↔ f != g
  proof: Finset.nonempty_iff_ne_empty.trans neLocus_eq_empty.not

中文:
定理 nonempty_neLocus_iff
  条件: {f g : Π₀ a, N a}
  结论: (f.neLocus g).Nonempty ↔ f != g
  证明: Finset.nonempty_iff_ne_empty.trans neLocus_eq_empty.not

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty.trans, neLocus_eq_empty, neLocus_eq_empty.not, nonempty_iff_ne_empty
-/
theorem nonempty_neLocus_iff {f g : Π₀ a, N a} : (f.neLocus g).Nonempty ↔ f != g :=
  Finset.nonempty_iff_ne_empty.trans neLocus_eq_empty.not

/--
theorem `neLocus_comm` / 定理 `neLocus_comm`

English:
theorem neLocus_comm
  statement: f.neLocus g = g.neLocus f
  proof: by
  simp_rw [neLocus, Finset.union_comm, ne_comm]

@[simp]

中文:
定理 neLocus_comm
  结论: f.neLocus g = g.neLocus f
  证明: by
  simp_rw [neLocus, Finset.union_comm, ne_comm]

@[simp]

Depends on / 依赖: Finset, Finset.union_comm, neLocus, ne_comm, simp_rw, union_comm
-/
theorem neLocus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [neLocus, Finset.union_comm, ne_comm]

@[simp]
/--
theorem `neLocus_zero_right` / 定理 `neLocus_zero_right`

English:
theorem neLocus_zero_right
  statement: f.neLocus 0 = f.support
  proof: by
  ext
  rw [mem_neLocus]; rw [mem_support_iff]; rw [coe_zero]; rw [Pi.zero_apply]

@[simp]

中文:
定理 neLocus_zero_right
  结论: f.neLocus 0 = f.support
  证明: by
  ext
  rw [mem_neLocus]; rw [mem_support_iff]; rw [coe_zero]; rw [Pi.zero_apply]

@[simp]

Depends on / 依赖: Pi.zero_apply, coe_zero, mem_neLocus, mem_support_iff, zero_apply
-/
theorem neLocus_zero_right : f.neLocus 0 = f.support := by
  ext
  rw [mem_neLocus]; rw [mem_support_iff]; rw [coe_zero]; rw [Pi.zero_apply]

@[simp]
/--
theorem `neLocus_zero_left` / 定理 `neLocus_zero_left`

English:
theorem neLocus_zero_left
  statement: (0 : Π₀ a, N a).neLocus f = f.support
  proof: (neLocus_comm _ _).trans (neLocus_zero_right _)

中文:
定理 neLocus_zero_left
  结论: (0 : Π₀ a, N a).neLocus f = f.support
  证明: (neLocus_comm _ _).trans (neLocus_zero_right _)

Depends on / 依赖: neLocus_comm, neLocus_zero_right
-/
theorem neLocus_zero_left : (0 : Π₀ a, N a).neLocus f = f.support :=
  (neLocus_comm _ _).trans (neLocus_zero_right _)

end NHasZero

section NeLocusAndMaps

variable {M P : α -> Type*} [forall a, Zero (N a)] [forall a, Zero (M a)] [forall a, Zero (P a)]

/--
theorem `subset_mapRange_neLocus` / 定理 `subset_mapRange_neLocus`

English:
theorem subset_mapRange_neLocus
  statement: [forall a, DecidableEq (N a)] [forall a, DecidableEq (M a)] (f g : Π₀ a, N a)
  proof: fun a => by
  simpa only [mem_neLocus, mapRange_apply, not_imp_not] using congr_arg (F a)

中文:
定理 subset_mapRange_neLocus
  结论: [对任意 a, DecidableEq (N a)] [对任意 a, DecidableEq (M a)] (f g : Π₀ a, N a)
  证明: fun a => by
  simpa only [mem_neLocus, mapRange_apply, not_imp_not] using congr_arg (F a)

Depends on / 依赖: congr_arg, mapRange_apply, mem_neLocus, not_imp_not
-/
theorem subset_mapRange_neLocus [forall a, DecidableEq (N a)] [forall a, DecidableEq (M a)] (f g : Π₀ a, N a)
    {F : forall a, N a -> M a} (F0 : forall a, F a 0 = 0) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) subseteq f.neLocus g := fun a => by
  simpa only [mem_neLocus, mapRange_apply, not_imp_not] using congr_arg (F a)

/--
theorem `zipWith_neLocus_eq_left` / 定理 `zipWith_neLocus_eq_left`

English:
theorem zipWith_neLocus_eq_left
  statement: [forall a, DecidableEq (N a)] [forall a, DecidableEq (P a)]
  proof: by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

中文:
定理 zipWith_neLocus_eq_left
  结论: [对任意 a, DecidableEq (N a)] [对任意 a, DecidableEq (P a)]
  证明: by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

Depends on / 依赖: mem_neLocus, ne_iff
-/
theorem zipWith_neLocus_eq_left [forall a, DecidableEq (N a)] [forall a, DecidableEq (P a)]
    {F : forall a, M a -> N a -> P a} (F0 : forall a, F a 0 0 = 0) (f : Π₀ a, M a) (g₁ g₂ : Π₀ a, N a)
    (hF : forall a f, Function.Injective fun g => F a f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ := by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

/--
theorem `zipWith_neLocus_eq_right` / 定理 `zipWith_neLocus_eq_right`

English:
theorem zipWith_neLocus_eq_right
  statement: [forall a, DecidableEq (M a)] [forall a, DecidableEq (P a)]
  proof: by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

中文:
定理 zipWith_neLocus_eq_right
  结论: [对任意 a, DecidableEq (M a)] [对任意 a, DecidableEq (P a)]
  证明: by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

Depends on / 依赖: mem_neLocus, ne_iff
-/
theorem zipWith_neLocus_eq_right [forall a, DecidableEq (M a)] [forall a, DecidableEq (P a)]
    {F : forall a, M a -> N a -> P a} (F0 : forall a, F a 0 0 = 0) (f₁ f₂ : Π₀ a, M a) (g : Π₀ a, N a)
    (hF : forall a g, Function.Injective fun f => F a f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ := by
  ext a
  simpa only [mem_neLocus] using! (hF a _).ne_iff

/--
theorem `mapRange_neLocus_eq` / 定理 `mapRange_neLocus_eq`

English:
theorem mapRange_neLocus_eq
  statement: [forall a, DecidableEq (N a)] [forall a, DecidableEq (M a)] (f g : Π₀ a, N a)
  proof: by
  ext a
  simpa only [mem_neLocus] using! (hF a).ne_iff

中文:
定理 mapRange_neLocus_eq
  结论: [对任意 a, DecidableEq (N a)] [对任意 a, DecidableEq (M a)] (f g : Π₀ a, N a)
  证明: by
  ext a
  simpa only [mem_neLocus] using! (hF a).ne_iff

Depends on / 依赖: mem_neLocus, ne_iff
-/
theorem mapRange_neLocus_eq [forall a, DecidableEq (N a)] [forall a, DecidableEq (M a)] (f g : Π₀ a, N a)
    {F : forall a, N a -> M a} (F0 : forall a, F a 0 = 0) (hF : forall a, Function.Injective (F a)) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) = f.neLocus g := by
  ext a
  simpa only [mem_neLocus] using! (hF a).ne_iff

end NeLocusAndMaps

variable [forall a, DecidableEq (N a)]

@[simp]
/--
theorem `neLocus_add_left` / 定理 `neLocus_add_left`

English:
theorem neLocus_add_left
  given: [forall a, AddLeftCancelMonoid (N a)] (f g h : Π₀ a, N a)
  proof: zipWith_neLocus_eq_left _ _ _ _ fun _a => add_right_injective

@[simp]

中文:
定理 neLocus_add_left
  条件: [对任意 a, AddLeftCancelMonoid (N a)] (f g h : Π₀ a, N a)
  证明: zipWith_neLocus_eq_left _ _ _ _ fun _a => add_right_injective

@[simp]

Depends on / 依赖: add_right_injective, zipWith_neLocus_eq_left
-/
theorem neLocus_add_left [forall a, AddLeftCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + g).neLocus (f + h) = g.neLocus h :=
  zipWith_neLocus_eq_left _ _ _ _ fun _a => add_right_injective

@[simp]
/--
theorem `neLocus_add_right` / 定理 `neLocus_add_right`

English:
theorem neLocus_add_right
  given: [forall a, AddRightCancelMonoid (N a)] (f g h : Π₀ a, N a)
  proof: zipWith_neLocus_eq_right _ _ _ _ fun _a => add_left_injective

中文:
定理 neLocus_add_right
  条件: [对任意 a, AddRightCancelMonoid (N a)] (f g h : Π₀ a, N a)
  证明: zipWith_neLocus_eq_right _ _ _ _ fun _a => add_left_injective

Depends on / 依赖: add_left_injective, zipWith_neLocus_eq_right
-/
theorem neLocus_add_right [forall a, AddRightCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + h).neLocus (g + h) = f.neLocus g :=
  zipWith_neLocus_eq_right _ _ _ _ fun _a => add_left_injective

section AddGroup

variable [forall a, AddGroup (N a)] (f f₁ f₂ g g₁ g₂ : Π₀ a, N a)

@[simp]
/--
theorem `neLocus_neg_neg` / 定理 `neLocus_neg_neg`

English:
theorem neLocus_neg_neg
  statement: neLocus (-f) (-g) = f.neLocus g
  proof: mapRange_neLocus_eq _ _ (fun _a => neg_zero) fun _a => neg_injective

中文:
定理 neLocus_neg_neg
  结论: neLocus (-f) (-g) = f.neLocus g
  证明: mapRange_neLocus_eq _ _ (fun _a => neg_zero) fun _a => neg_injective

Depends on / 依赖: mapRange_neLocus_eq, neg_injective, neg_zero
-/
theorem neLocus_neg_neg : neLocus (-f) (-g) = f.neLocus g :=
  mapRange_neLocus_eq _ _ (fun _a => neg_zero) fun _a => neg_injective

/--
theorem `neLocus_neg` / 定理 `neLocus_neg`

English:
theorem neLocus_neg
  statement: neLocus (-f) g = f.neLocus (-g)
  proof: by rw [← neLocus_neg_neg, neg_neg]

中文:
定理 neLocus_neg
  结论: neLocus (-f) g = f.neLocus (-g)
  证明: by rw [← neLocus_neg_neg, neg_neg]

Depends on / 依赖: neLocus_neg_neg, neg_neg
-/
theorem neLocus_neg : neLocus (-f) g = f.neLocus (-g) := by rw [← neLocus_neg_neg, neg_neg]

/--
theorem `neLocus_eq_support_sub` / 定理 `neLocus_eq_support_sub`

English:
theorem neLocus_eq_support_sub
  statement: f.neLocus g = (f - g).support
  proof: by
  rw [← @neLocus_add_right α N _ _ _ _ _ (-g)]; rw [add_neg_cancel]; rw [neLocus_zero_right]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 neLocus_eq_support_sub
  结论: f.neLocus g = (f - g).support
  证明: by
  rw [← @neLocus_add_right α N _ _ _ _ _ (-g)]; rw [add_neg_cancel]; rw [neLocus_zero_right]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: add_neg_cancel, neLocus_add_right, neLocus_zero_right, sub_eq_add_neg
-/
theorem neLocus_eq_support_sub : f.neLocus g = (f - g).support := by
  rw [← @neLocus_add_right α N _ _ _ _ _ (-g)]; rw [add_neg_cancel]; rw [neLocus_zero_right]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `neLocus_sub_left` / 定理 `neLocus_sub_left`

English:
theorem neLocus_sub_left
  statement: neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂
  proof: by
  simp only [sub_eq_add_neg, @neLocus_add_left α N _ _ _, neLocus_neg_neg]

@[simp]

中文:
定理 neLocus_sub_left
  结论: neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂
  证明: by
  simp only [sub_eq_add_neg, @neLocus_add_left α N _ _ _, neLocus_neg_neg]

@[simp]

Depends on / 依赖: neLocus_add_left, neLocus_neg_neg, sub_eq_add_neg
-/
theorem neLocus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂ := by
  simp only [sub_eq_add_neg, @neLocus_add_left α N _ _ _, neLocus_neg_neg]

@[simp]
/--
theorem `neLocus_sub_right` / 定理 `neLocus_sub_right`

English:
theorem neLocus_sub_right
  statement: neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂
  proof: by
  simpa only [sub_eq_add_neg] using @neLocus_add_right α N _ _ _ _ _ _

@[simp]

中文:
定理 neLocus_sub_right
  结论: neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂
  证明: by
  simpa only [sub_eq_add_neg] using @neLocus_add_right α N _ _ _ _ _ _

@[simp]

Depends on / 依赖: neLocus_add_right, sub_eq_add_neg
-/
theorem neLocus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂ := by
  simpa only [sub_eq_add_neg] using @neLocus_add_right α N _ _ _ _ _ _

@[simp]
/--
theorem `neLocus_self_add_right` / 定理 `neLocus_self_add_right`

English:
theorem neLocus_self_add_right
  statement: neLocus f (f + g) = g.support
  proof: by
  rw [← neLocus_zero_left]; rw [← @neLocus_add_left α N _ _ _ f 0 g]; rw [add_zero]

@[simp]

中文:
定理 neLocus_self_add_right
  结论: neLocus f (f + g) = g.support
  证明: by
  rw [← neLocus_zero_left]; rw [← @neLocus_add_left α N _ _ _ f 0 g]; rw [add_zero]

@[simp]

Depends on / 依赖: add_zero, neLocus_add_left, neLocus_zero_left
-/
theorem neLocus_self_add_right : neLocus f (f + g) = g.support := by
  rw [← neLocus_zero_left]; rw [← @neLocus_add_left α N _ _ _ f 0 g]; rw [add_zero]

@[simp]
/--
theorem `neLocus_self_add_left` / 定理 `neLocus_self_add_left`

English:
theorem neLocus_self_add_left
  statement: neLocus (f + g) f = g.support
  proof: by
  rw [neLocus_comm]; rw [neLocus_self_add_right]

@[simp]

中文:
定理 neLocus_self_add_left
  结论: neLocus (f + g) f = g.support
  证明: by
  rw [neLocus_comm]; rw [neLocus_self_add_right]

@[simp]

Depends on / 依赖: neLocus_comm, neLocus_self_add_right
-/
theorem neLocus_self_add_left : neLocus (f + g) f = g.support := by
  rw [neLocus_comm]; rw [neLocus_self_add_right]

@[simp]
/--
theorem `neLocus_self_sub_right` / 定理 `neLocus_self_sub_right`

English:
theorem neLocus_self_sub_right
  statement: neLocus f (f - g) = g.support
  proof: by
  rw [sub_eq_add_neg]; rw [neLocus_self_add_right]; rw [support_neg]

@[simp]

中文:
定理 neLocus_self_sub_right
  结论: neLocus f (f - g) = g.support
  证明: by
  rw [sub_eq_add_neg]; rw [neLocus_self_add_right]; rw [support_neg]

@[simp]

Depends on / 依赖: neLocus_self_add_right, sub_eq_add_neg, support_neg
-/
theorem neLocus_self_sub_right : neLocus f (f - g) = g.support := by
  rw [sub_eq_add_neg]; rw [neLocus_self_add_right]; rw [support_neg]

@[simp]
/--
theorem `neLocus_self_sub_left` / 定理 `neLocus_self_sub_left`

English:
theorem neLocus_self_sub_left
  statement: neLocus (f - g) f = g.support
  proof: by
  rw [neLocus_comm]; rw [neLocus_self_sub_right]

中文:
定理 neLocus_self_sub_left
  结论: neLocus (f - g) f = g.support
  证明: by
  rw [neLocus_comm]; rw [neLocus_self_sub_right]

Depends on / 依赖: neLocus_comm, neLocus_self_sub_right
-/
theorem neLocus_self_sub_left : neLocus (f - g) f = g.support := by
  rw [neLocus_comm]; rw [neLocus_self_sub_right]

end AddGroup

end DFinsupp
