/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Order.Directed

/-!
# Finsets of ordered types
-/

public section


universe u v w

variable {α : Type u}

/--
theorem `Directed.finset_le` / 定理 `Directed.finset_le`

English:
theorem Directed.finset_le
  statement: {r : α -> α -> Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι -> α}
  proof: show exists z, forall i in s.1, r (f i) (f z) from
    Multiset.induction_on s.1 (let ⟨z⟩ := hι; ⟨z, fun _ => by simp⟩)
      fun i _ ⟨j, H⟩ =>
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun _ h => (Multiset.mem_cons.1 h).casesOn (fun h => h.symm ▸ h₁)
        fun h => _root_.trans (H _ h) h₂⟩

中文:
定理 Directed.finset_le
  结论: {r : α -> α -> 命题} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι -> α}
  证明: show exists z, forall i in s.1, r (f i) (f z) from
    Multiset.induction_on s.1 (let ⟨z⟩ := hι; ⟨z, fun _ => by simp⟩)
      fun i _ ⟨j, H⟩ =>
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun _ h => (Multiset.mem_cons.1 h).casesOn (fun h => h.symm ▸ h₁)
        fun h => _root_.trans (H _ h) h₂⟩

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.mem_cons, _root_, _root_.trans, casesOn, h.symm, induction_on, mem_cons
-/
theorem Directed.finset_le {r : α -> α -> Prop} [IsTrans α r] {ι} [hι : Nonempty ι] {f : ι -> α}
    (D : Directed r f) (s : Finset ι) : exists z, forall i in s, r (f i) (f z) :=
  show exists z, forall i in s.1, r (f i) (f z) from
    Multiset.induction_on s.1 (let ⟨z⟩ := hι; ⟨z, fun _ => by simp⟩)
      fun i _ ⟨j, H⟩ =>
      let ⟨k, h₁, h₂⟩ := D i j
      ⟨k, fun _ h => (Multiset.mem_cons.1 h).casesOn (fun h => h.symm ▸ h₁)
        fun h => _root_.trans (H _ h) h₂⟩

/--
theorem `Finset.exists_le` / 定理 `Finset.exists_le`

English:
theorem Finset.exists_le
  given: [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α)
  proof: directed_id.finset_le _

中文:
定理 Finset.exists_le
  条件: [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α)
  证明: directed_id.finset_le _

Depends on / 依赖: directed_id, directed_id.finset_le, finset_le
-/
theorem Finset.exists_le [Nonempty α] [Preorder α] [IsDirectedOrder α] (s : Finset α) :
    exists M, forall i in s, i <= M :=
  directed_id.finset_le _
