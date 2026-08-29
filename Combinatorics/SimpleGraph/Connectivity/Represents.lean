/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Set.Card

/-!
# Representation of components by a set of vertices

## Main definition

* `SimpleGraph.ConnectedComponent.Represents` says that a set of vertices represents a set of
  components if it contains exactly one vertex from each component.
-/

@[expose] public section

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

namespace SimpleGraph.ConnectedComponent

/--
Definition of `Represents` / `Represents` 的定义

English:
definition Represents
  signature: (s : Set V) (C : Set G.ConnectedComponent)
  body: Set.BijOn G.connectedComponentMk s C

中文:
定义 Represents
  签名: (s : 集合 V) (C : 集合 G.ConnectedComponent)
  定义体: Set.BijOn G.connectedComponentMk s C

Depends on / 依赖: G.connectedComponentMk, Set.BijOn, connectedComponentMk
-/
def Represents (s : Set V) (C : Set G.ConnectedComponent) : Prop :=
  Set.BijOn G.connectedComponentMk s C

namespace Represents

variable {C : Set G.ConnectedComponent} {s : Set V} {c : G.ConnectedComponent}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `image_out` / 引理 `image_out`

English:
lemma image_out
  given: (C : Set G.ConnectedComponent)
  proof: Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all [connectedComponentMk]) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    simp only [connectedComponentMk] at hxy
    aesop) (fun _ _ => by simpa [connectedComponentMk])

中文:
引理 image_out
  条件: (C : 集合 G.ConnectedComponent)
  证明: Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all [connectedComponentMk]) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    simp only [connectedComponentMk] at hxy
    aesop) (fun _ _ => by simpa [connectedComponentMk])

Depends on / 依赖: Set.BijOn.mk, connectedComponentMk
-/
lemma image_out (C : Set G.ConnectedComponent) :
    Represents (Quot.out '' C) C :=
  Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all [connectedComponentMk]) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    simp only [connectedComponentMk] at hxy
    aesop) (fun _ _ => by simpa [connectedComponentMk])

/--
lemma `existsUnique_rep` / 引理 `existsUnique_rep`

English:
lemma existsUnique_rep
  given: (hrep : Represents s C) (h : c in C)
  statement: exists! x, x in s inter c.supp
  proof: by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [Set.mem_inter_iff, hx, mem_supp_iff, and_self, and_imp, true_and]
  exact fun y hy hyx => hrep.2.1 hy hx hyx

中文:
引理 存在Unique_rep
  条件: (hrep : Represents s C) (h : c in C)
  结论: 存在! x, x in s inter c.supp
  证明: by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [Set.mem_inter_iff, hx, mem_supp_iff, and_self, and_imp, true_and]
  exact fun y hy hyx => hrep.2.1 hy hx hyx

Depends on / 依赖: Set.mem_inter_iff, and_imp, and_self, mem_inter_iff, mem_supp_iff, true_and
-/
lemma existsUnique_rep (hrep : Represents s C) (h : c in C) : exists! x, x in s inter c.supp := by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [Set.mem_inter_iff, hx, mem_supp_iff, and_self, and_imp, true_and]
  exact fun y hy hyx => hrep.2.1 hy hx hyx

/--
lemma `exists_inter_eq_singleton` / 引理 `exists_inter_eq_singleton`

English:
lemma exists_inter_eq_singleton
  given: (hrep : Represents s C) (h : c in C)
  statement: exists x, s inter c.supp = {x}
  proof: by
  obtain ⟨a, ha⟩ := existsUnique_rep hrep h
  aesop

中文:
引理 存在_inter_eq_singleton
  条件: (hrep : Represents s C) (h : c in C)
  结论: 存在 x, s inter c.supp = {x}
  证明: by
  obtain ⟨a, ha⟩ := existsUnique_rep hrep h
  aesop

Depends on / 依赖: existsUnique_rep
-/
lemma exists_inter_eq_singleton (hrep : Represents s C) (h : c in C) : exists x, s inter c.supp = {x} := by
  obtain ⟨a, ha⟩ := existsUnique_rep hrep h
  aesop

/--
lemma `disjoint_supp_of_notMem` / 引理 `disjoint_supp_of_notMem`

English:
lemma disjoint_supp_of_notMem
  given: (hrep : Represents s C) (h : c ∉ C)
  statement: Disjoint s c.supp
  proof: by
  rw [Set.disjoint_left]
  intro a ha hc
  simp only [mem_supp_iff] at hc
  subst hc
  exact h (hrep.1 ha)

中文:
引理 disjoint_supp_of_notMem
  条件: (hrep : Represents s C) (h : c ∉ C)
  结论: Disjoint s c.supp
  证明: by
  rw [Set.disjoint_left]
  intro a ha hc
  simp only [mem_supp_iff] at hc
  subst hc
  exact h (hrep.1 ha)

Depends on / 依赖: Set.disjoint_left, disjoint_left, mem_supp_iff
-/
lemma disjoint_supp_of_notMem (hrep : Represents s C) (h : c ∉ C) : Disjoint s c.supp := by
  rw [Set.disjoint_left]
  intro a ha hc
  simp only [mem_supp_iff] at hc
  subst hc
  exact h (hrep.1 ha)

/--
lemma `ncard_inter` / 引理 `ncard_inter`

English:
lemma ncard_inter
  given: (hrep : Represents s C) (h : c in C)
  statement: (s inter c.supp).ncard = 1
  proof: by
  rw [Set.ncard_eq_one]
  exact exists_inter_eq_singleton hrep h

中文:
引理 ncard_inter
  条件: (hrep : Represents s C) (h : c in C)
  结论: (s inter c.supp).ncard = 1
  证明: by
  rw [Set.ncard_eq_one]
  exact exists_inter_eq_singleton hrep h

Depends on / 依赖: Set.ncard_eq_one, exists_inter_eq_singleton, ncard_eq_one
-/
lemma ncard_inter (hrep : Represents s C) (h : c in C) : (s inter c.supp).ncard = 1 := by
  rw [Set.ncard_eq_one]
  exact exists_inter_eq_singleton hrep h

/--
lemma `ncard_eq` / 引理 `ncard_eq`

English:
lemma ncard_eq
  given: (hrep : Represents s C)
  statement: s.ncard = C.ncard
  proof: hrep.image_eq ▸ hrep.injOn.ncard_image.symm

中文:
引理 ncard_eq
  条件: (hrep : Represents s C)
  结论: s.ncard = C.ncard
  证明: hrep.image_eq ▸ hrep.injOn.ncard_image.symm

Depends on / 依赖: hrep.image_eq, hrep.injOn.ncard_image.symm, image_eq, ncard_image
-/
lemma ncard_eq (hrep : Represents s C) : s.ncard = C.ncard :=
  hrep.image_eq ▸ hrep.injOn.ncard_image.symm

/--
lemma `ncard_sdiff_of_mem` / 引理 `ncard_sdiff_of_mem`

English:
lemma ncard_sdiff_of_mem
  given: (hrep : Represents s C) (h : c in C)
  proof: by
  obtain ⟨a, ha⟩ := exists_inter_eq_singleton hrep h
  rw [← Set.sdiff_inter_self_eq_sdiff]; rw [ha]; rw [Set.ncard_sdiff]; rw [Set.ncard_singleton]
  simp [← ha]

中文:
引理 ncard_sdiff_of_mem
  条件: (hrep : Represents s C) (h : c in C)
  证明: by
  obtain ⟨a, ha⟩ := exists_inter_eq_singleton hrep h
  rw [← Set.sdiff_inter_self_eq_sdiff]; rw [ha]; rw [Set.ncard_sdiff]; rw [Set.ncard_singleton]
  simp [← ha]

Depends on / 依赖: Set.ncard_sdiff, Set.ncard_singleton, Set.sdiff_inter_self_eq_sdiff, exists_inter_eq_singleton, ncard_sdiff, ncard_singleton, sdiff_inter_self_eq_sdiff
-/
lemma ncard_sdiff_of_mem (hrep : Represents s C) (h : c in C) :
    (c.supp \ s).ncard = c.supp.ncard - 1 := by
  obtain ⟨a, ha⟩ := exists_inter_eq_singleton hrep h
  rw [← Set.sdiff_inter_self_eq_sdiff]; rw [ha]; rw [Set.ncard_sdiff]; rw [Set.ncard_singleton]
  simp [← ha]

/--
lemma `ncard_sdiff_of_notMem` / 引理 `ncard_sdiff_of_notMem`

English:
lemma ncard_sdiff_of_notMem
  given: (hrep : Represents s C) (h : c ∉ C)
  proof: by
  rw [(disjoint_supp_of_notMem hrep h).sdiff_eq_right]

中文:
引理 ncard_sdiff_of_notMem
  条件: (hrep : Represents s C) (h : c ∉ C)
  证明: by
  rw [(disjoint_supp_of_notMem hrep h).sdiff_eq_right]

Depends on / 依赖: disjoint_supp_of_notMem, sdiff_eq_right
-/
lemma ncard_sdiff_of_notMem (hrep : Represents s C) (h : c ∉ C) :
    (c.supp \ s).ncard = c.supp.ncard := by
  rw [(disjoint_supp_of_notMem hrep h).sdiff_eq_right]

end ConnectedComponent.Represents

/--
lemma `ConnectedComponent.even_ncard_supp_sdiff_rep` / 引理 `ConnectedComponent.even_ncard_supp_sdiff_rep`

English:
lemma ConnectedComponent.even_ncard_supp_sdiff_rep
  statement: {s : Set V} (K : G.ConnectedComponent)
  proof: by
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_notMem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard != 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h)]; rw [Nat.even_sub (by lia)]
    simpa [Nat.even_sub] using Nat.not_even_iff_odd.mp h

中文:
引理 ConnectedComponent.even_ncard_supp_sdiff_rep
  结论: {s : 集合 V} (K : G.ConnectedComponent)
  证明: by
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_notMem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard != 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h)]; rw [Nat.even_sub (by lia)]
    simpa [Nat.even_sub] using Nat.not_even_iff_odd.mp h

Depends on / 依赖: K.supp.ncard, Nat.even_sub, Nat.ne_of_odd_add, Nat.not_even_iff_odd.mp, Nat.not_odd_iff_even, Set.ncard_image_of_injective, even_sub, hrep.ncard_sdiff_of_mem, hrep.ncard_sdiff_of_notMem, ncard_image_of_injective, ncard_sdiff_of_mem, ncard_sdiff_of_notMem, ne_of_odd_add, not_even_iff_odd, not_odd_iff_even
-/
lemma ConnectedComponent.even_ncard_supp_sdiff_rep {s : Set V} (K : G.ConnectedComponent)
    (hrep : ConnectedComponent.Represents s G.oddComponents) :
    Even (K.supp \ s).ncard := by
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_notMem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard != 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h)]; rw [Nat.even_sub (by lia)]
    simpa [Nat.even_sub] using Nat.not_even_iff_odd.mp h

end SimpleGraph
