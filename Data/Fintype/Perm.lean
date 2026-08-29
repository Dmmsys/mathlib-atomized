/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# `Fintype` instances for `Equiv` and `Perm`

Main declarations:
* `permsOfFinset s`: The finset of permutations of the finset `s`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset List Equiv Equiv.Perm

variable [DecidableEq α] [DecidableEq β]

/--
Definition of `permsOfList` / `permsOfList` 的定义

English:
definition permsOfList
  signature: : List α -> List (Perm α)

中文:
定义 permsOfList
  签名: : 列表 α -> 列表 (置换 α)
-/
def permsOfList : List α -> List (Perm α)
  | [] => [1]
  | a :: l => permsOfList l ++ l.flatMap fun b => (permsOfList l).map fun f => Equiv.swap a b * f

/--
theorem `length_permsOfList` / 定理 `length_permsOfList`

English:
theorem length_permsOfList
  statement: forall l : List α, length (permsOfList l) = l.length !

中文:
定理 length_permsOfList
  结论: 对任意 l : 列表 α, length (permsOfList l) = l.length !
-/
theorem length_permsOfList : forall l : List α, length (permsOfList l) = l.length !
  | [] => rfl
  | a :: l => by
    simp [Nat.factorial_succ, permsOfList, length_permsOfList, succ_mul, add_comm]

/--
theorem `mem_permsOfList_of_mem` / 定理 `mem_permsOfList_of_mem`

English:
theorem mem_permsOfList_of_mem
  given: {l : List α} {f : Perm α} (h : forall x, f x != x -> x in l)
  proof: by
  induction l generalizing f with
  | nil =>
    simp only [not_mem_nil] at h
    exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.byContradiction <| h x)
  | cons a l IH =>
  by_cases hfa : f a = a
  · refine mem_append_left _ (IH fun x hx => mem_of_ne_of_mem ?_ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) != f a := mt (fun h => f.injective h) hfa
  have : forall x : α, (Equiv.swap a (f a) * f) x != x -> x in l := by
    simp
    grind
  suffices f in permsOfList l ∨ exists b in l, exists g in permsOfList l, Equiv.swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map, mem_append, List.mem_flatMap]
  refine or_iff_not_imp_left.2 fun _hfl => ⟨f a, ?_, Equiv.swap a (f a) * f, IH this, ?_⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (Equiv.swap a (f a)) (Equiv.swap a (f a)), Equiv.swap_swap,
      ← Perm.one_def, one_mul]

中文:
定理 mem_permsOfList_of_mem
  条件: {l : 列表 α} {f : 置换 α} (h : 对任意 x, f x != x -> x in l)
  证明: by
  induction l generalizing f with
  | nil =>
    simp only [not_mem_nil] at h
    exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.byContradiction <| h x)
  | cons a l IH =>
  by_cases hfa : f a = a
  · refine mem_append_left _ (IH fun x hx => mem_of_ne_of_mem ?_ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) != f a := mt (fun h => f.injective h) hfa
  have : forall x : α, (Equiv.swap a (f a) * f) x != x -> x in l := by
    simp
    grind
  suffices f in permsOfList l ∨ exists b in l, exists g in permsOfList l, Equiv.swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map, mem_append, List.mem_flatMap]
  refine or_iff_not_imp_left.2 fun _hfl => ⟨f a, ?_, Equiv.swap a (f a) * f, IH this, ?_⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (Equiv.swap a (f a)) (Equiv.swap a (f a)), Equiv.swap_swap,
      ← Perm.one_def, one_mul]

Depends on / 依赖: Decidable, Decidable.byContradiction, Equiv.ext, Equiv.swap, List.mem_singleton, byContradiction, f.injective, generalizing, injective, mem_append_left, mem_of_ne_of_mem, mem_singleton, not_mem_nil, permsOfLis, permsOfList
-/
theorem mem_permsOfList_of_mem {l : List α} {f : Perm α} (h : forall x, f x != x -> x in l) :
    f in permsOfList l := by
  induction l generalizing f with
  | nil =>
    simp only [not_mem_nil] at h
    exact List.mem_singleton.2 (Equiv.ext fun x => Decidable.byContradiction <| h x)
  | cons a l IH =>
  by_cases hfa : f a = a
  · refine mem_append_left _ (IH fun x hx => mem_of_ne_of_mem ?_ (h x hx))
    rintro rfl
    exact hx hfa
  have hfa' : f (f a) != f a := mt (fun h => f.injective h) hfa
  have : forall x : α, (Equiv.swap a (f a) * f) x != x -> x in l := by
    simp
    grind
  suffices f in permsOfList l ∨ exists b in l, exists g in permsOfList l, Equiv.swap a b * g = f by
    simpa only [permsOfList, exists_prop, List.mem_map, mem_append, List.mem_flatMap]
  refine or_iff_not_imp_left.2 fun _hfl => ⟨f a, ?_, Equiv.swap a (f a) * f, IH this, ?_⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
  · rw [← mul_assoc, mul_def (Equiv.swap a (f a)) (Equiv.swap a (f a)), Equiv.swap_swap,
      ← Perm.one_def, one_mul]

/--
theorem `mem_of_mem_permsOfList` / 定理 `mem_of_mem_permsOfList`

English:
theorem mem_of_mem_permsOfList
  proof: by simpa [permsOfList] using h
    rw [this]; simp
  | a :: l, f, h, x =>
    (mem_append.1 h).elim (fun h hx => mem_cons_of_mem _ (mem_of_mem_permsOfList h hx))
      fun h hx =>
      let ⟨y, hy, hy'⟩ := List.mem_flatMap.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map.1 hy'
      if hxa : x = a then by simp [hxa]
      else
if hxy : x = y then mem_cons_of_mem _ by rwa [hxy]
else mem_cons_of_mem a mem_of_mem_permsOfList hg₁ by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂]; rw [mul_apply]; rw [swap_inv]; rw [swap_apply_def]
              split_ifs <;> [exact Ne.symm hxy; exact Ne.symm hxa; exact hx]

中文:
定理 mem_of_mem_permsOfList
  证明: by simpa [permsOfList] using h
    rw [this]; simp
  | a :: l, f, h, x =>
    (mem_append.1 h).elim (fun h hx => mem_cons_of_mem _ (mem_of_mem_permsOfList h hx))
      fun h hx =>
      let ⟨y, hy, hy'⟩ := List.mem_flatMap.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map.1 hy'
      if hxa : x = a then by simp [hxa]
      else
if hxy : x = y then mem_cons_of_mem _ by rwa [hxy]
else mem_cons_of_mem a mem_of_mem_permsOfList hg₁ by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂]; rw [mul_apply]; rw [swap_inv]; rw [swap_apply_def]
              split_ifs <;> [exact Ne.symm hxy; exact Ne.symm hxa; exact hx]

Depends on / 依赖: List.mem_flatMap, List.mem_map, Ne.sym, eq_inv_mul_iff_mul_eq, mem_append, mem_cons_of_mem, mem_flatMap, mem_map, mem_of_mem_permsOfList, mul_apply, permsOfList, split_ifs, swap_apply_def, swap_inv
-/
theorem mem_of_mem_permsOfList :
    forall {l : List α} {f : Perm α}, f in permsOfList l -> {x : α} -> f x != x -> x in l
  | [], f, h, heq_iff_eq => by
    have : f = 1 := by simpa [permsOfList] using h
    rw [this]; simp
  | a :: l, f, h, x =>
    (mem_append.1 h).elim (fun h hx => mem_cons_of_mem _ (mem_of_mem_permsOfList h hx))
      fun h hx =>
      let ⟨y, hy, hy'⟩ := List.mem_flatMap.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_map.1 hy'
      if hxa : x = a then by simp [hxa]
      else
if hxy : x = y then mem_cons_of_mem _ by rwa [hxy]
else mem_cons_of_mem a mem_of_mem_permsOfList hg₁ by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂]; rw [mul_apply]; rw [swap_inv]; rw [swap_apply_def]
              split_ifs <;> [exact Ne.symm hxy; exact Ne.symm hxa; exact hx]

/--
theorem `mem_permsOfList_iff` / 定理 `mem_permsOfList_iff`

English:
theorem mem_permsOfList_iff
  given: {l : List α} {f : Perm α}
  proof: ⟨mem_of_mem_permsOfList, mem_permsOfList_of_mem⟩

中文:
定理 mem_permsOfList_iff
  条件: {l : 列表 α} {f : 置换 α}
  证明: ⟨mem_of_mem_permsOfList, mem_permsOfList_of_mem⟩

Depends on / 依赖: mem_of_mem_permsOfList, mem_permsOfList_of_mem
-/
theorem mem_permsOfList_iff {l : List α} {f : Perm α} :
    f in permsOfList l ↔ forall {x}, f x != x -> x in l :=
  ⟨mem_of_mem_permsOfList, mem_permsOfList_of_mem⟩

/--
theorem `nodup_permsOfList` / 定理 `nodup_permsOfList`

English:
theorem nodup_permsOfList
  statement: forall {l : List α}, l.Nodup -> (permsOfList l).Nodup
  proof: hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_permsOfList hl'
    have hmeml : forall {f : Perm α}, f in permsOfList l -> f a = a := fun {f} hf =>
      not_not.1 (mt (mem_of_mem_permsOfList hf) (nodup_cons.1 hl).1)
    rw [permsOfList]; rw [List.nodup_append']; rw [List.nodup_flatMap]; rw [pairwise_iff_getElem]
    refine ⟨?_, ⟨⟨?_,?_ ⟩, ?_⟩⟩
    · exact hln'
    · exact fun _ _ => hln'.map fun _ _ => mul_left_cancel
    · intro i j hi hj hij x hx₁ hx₂
      let ⟨f, hf⟩ := List.mem_map.1 hx₁
      let ⟨g, hg⟩ := List.mem_map.1 hx₂
      have hix : x a = l[i] := by
        rw [← hf.2]; rw [mul_apply]; rw [hmeml hf.1]; rw [swap_apply_left]
      have hiy : x a = l[j] := by
        rw [← hg.2]; rw [mul_apply]; rw [hmeml hg.1]; rw [swap_apply_left]
      have hieqj : i = j := hl'.getElem_inj_iff.1 (hix.symm.trans hiy)
      exact absurd hieqj (_root_.ne_of_lt hij)
    · intro f hf₁ hf₂
      let ⟨x, hx, hx'⟩ := List.mem_flatMap.1 hf₂
      let ⟨g, hg⟩ := List.mem_map.1 hx'
obtain rfl : g.symm x = a := f.injective by rw [hmeml hf₁, ← hg.2]; simp
      have hxa : x != g.symm x := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
exact (List.nodup_cons.1 hl).1 mem_of_mem_permsOfList hg.1 (by simpa using hxa)

中文:
定理 nodup_permsOfList
  结论: 对任意 {l : 列表 α}, l.Nodup -> (permsOfList l).Nodup
  证明: hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_permsOfList hl'
    have hmeml : forall {f : Perm α}, f in permsOfList l -> f a = a := fun {f} hf =>
      not_not.1 (mt (mem_of_mem_permsOfList hf) (nodup_cons.1 hl).1)
    rw [permsOfList]; rw [List.nodup_append']; rw [List.nodup_flatMap]; rw [pairwise_iff_getElem]
    refine ⟨?_, ⟨⟨?_,?_ ⟩, ?_⟩⟩
    · exact hln'
    · exact fun _ _ => hln'.map fun _ _ => mul_left_cancel
    · intro i j hi hj hij x hx₁ hx₂
      let ⟨f, hf⟩ := List.mem_map.1 hx₁
      let ⟨g, hg⟩ := List.mem_map.1 hx₂
      have hix : x a = l[i] := by
        rw [← hf.2]; rw [mul_apply]; rw [hmeml hf.1]; rw [swap_apply_left]
      have hiy : x a = l[j] := by
        rw [← hg.2]; rw [mul_apply]; rw [hmeml hg.1]; rw [swap_apply_left]
      have hieqj : i = j := hl'.getElem_inj_iff.1 (hix.symm.trans hiy)
      exact absurd hieqj (_root_.ne_of_lt hij)
    · intro f hf₁ hf₂
      let ⟨x, hx, hx'⟩ := List.mem_flatMap.1 hf₂
      let ⟨g, hg⟩ := List.mem_map.1 hx'
obtain rfl : g.symm x = a := f.injective by rw [hmeml hf₁, ← hg.2]; simp
      have hxa : x != g.symm x := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
exact (List.nodup_cons.1 hl).1 mem_of_mem_permsOfList hg.1 (by simpa using hxa)

Depends on / 依赖: hl.of_cons, of_cons
-/
theorem nodup_permsOfList : forall {l : List α}, l.Nodup -> (permsOfList l).Nodup
  | [], _ => by simp [permsOfList]
  | a :: l, hl => by
    have hl' : l.Nodup := hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_permsOfList hl'
    have hmeml : forall {f : Perm α}, f in permsOfList l -> f a = a := fun {f} hf =>
      not_not.1 (mt (mem_of_mem_permsOfList hf) (nodup_cons.1 hl).1)
    rw [permsOfList]; rw [List.nodup_append']; rw [List.nodup_flatMap]; rw [pairwise_iff_getElem]
    refine ⟨?_, ⟨⟨?_,?_ ⟩, ?_⟩⟩
    · exact hln'
    · exact fun _ _ => hln'.map fun _ _ => mul_left_cancel
    · intro i j hi hj hij x hx₁ hx₂
      let ⟨f, hf⟩ := List.mem_map.1 hx₁
      let ⟨g, hg⟩ := List.mem_map.1 hx₂
      have hix : x a = l[i] := by
        rw [← hf.2]; rw [mul_apply]; rw [hmeml hf.1]; rw [swap_apply_left]
      have hiy : x a = l[j] := by
        rw [← hg.2]; rw [mul_apply]; rw [hmeml hg.1]; rw [swap_apply_left]
      have hieqj : i = j := hl'.getElem_inj_iff.1 (hix.symm.trans hiy)
      exact absurd hieqj (_root_.ne_of_lt hij)
    · intro f hf₁ hf₂
      let ⟨x, hx, hx'⟩ := List.mem_flatMap.1 hf₂
      let ⟨g, hg⟩ := List.mem_map.1 hx'
obtain rfl : g.symm x = a := f.injective by rw [hmeml hf₁, ← hg.2]; simp
      have hxa : x != g.symm x := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
exact (List.nodup_cons.1 hl).1 mem_of_mem_permsOfList hg.1 (by simpa using hxa)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `permsOfFinset` / `permsOfFinset` 的定义

English:
definition permsOfFinset
  signature: (s : Finset α)
  body: Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_permsOfList hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
heq_of_eq Finset.ext by simp [mem_permsOfList_iff, hab.mem_iff])
    s.2

中文:
定义 permsOfFinset
  签名: (s : 有限集 α)
  定义体: Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_permsOfList hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
heq_of_eq Finset.ext by simp [mem_permsOfList_iff, hab.mem_iff])
    s.2

Depends on / 依赖: Finset, Finset.ext, Quotient, Quotient.hrecOn, Quotient.sound, congr_arg, hab.mem_iff, heq_of_eq, hfunext, hrecOn, mem_iff, mem_permsOfList_iff, nodup_permsOfList, permsOfList
-/
def permsOfFinset (s : Finset α) : Finset (Perm α) :=
  Quotient.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_permsOfList hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotient.sound hab)) fun ha hb _ =>
heq_of_eq Finset.ext by simp [mem_permsOfList_iff, hab.mem_iff])
    s.2

/--
theorem `mem_perms_of_finset_iff` / 定理 `mem_perms_of_finset_iff`

English:
theorem mem_perms_of_finset_iff
  proof: by
  rintro ⟨⟨l⟩, hs⟩ f; exact mem_permsOfList_iff

中文:
定理 mem_perms_of_finset_iff
  证明: by
  rintro ⟨⟨l⟩, hs⟩ f; exact mem_permsOfList_iff

Depends on / 依赖: _zipWith, mem_permsOfList_iff
-/
theorem mem_perms_of_finset_iff :
    forall {s : Finset α} {f : Perm α}, f in permsOfFinset s ↔ forall {x}, f x != x -> x in s := by
  rintro ⟨⟨l⟩, hs⟩ f; exact mem_permsOfList_iff

/--
theorem `card_perms_of_finset` / 定理 `card_perms_of_finset`

English:
theorem card_perms_of_finset
  statement: forall s : Finset α, #(permsOfFinset s) = (#s)!
  proof: by
  rintro ⟨⟨l⟩, hs⟩; exact length_permsOfList l

中文:
定理 card_perms_of_finset
  结论: 对任意 s : 有限集 α, #(permsOfFinset s) = (#s)!
  证明: by
  rintro ⟨⟨l⟩, hs⟩; exact length_permsOfList l

Depends on / 依赖: length_permsOfList
-/
theorem card_perms_of_finset : forall s : Finset α, #(permsOfFinset s) = (#s)! := by
  rintro ⟨⟨l⟩, hs⟩; exact length_permsOfList l

/-- The collection of permutations of a fintype is a fintype. -/
@[instance_reducible]
/--
Definition of `fintypePerm` / `fintypePerm` 的定义

English:
definition fintypePerm
  signature: [Fintype α]
  body: ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

中文:
定义 fintypePerm
  签名: [有限类型 α]
  定义体: ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

Depends on / 依赖: Finset, Finset.univ, _zip, mem_perms_of_finset_iff, permsOfFinset
-/
def fintypePerm [Fintype α] : Fintype (Perm α) :=
  ⟨permsOfFinset (@Finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

/--
Instance `Equiv.instFintype` / 实例 `Equiv.instFintype`

English:
instance Equiv.instFintype
  signature: [Fintype α] [Fintype β]
  body: if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

@[to_additive]

中文:
实例 等价.instFintype
  签名: [有限类型 α] [有限类型 β]
  定义体: if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

@[to_additive]

Depends on / 依赖: Eq.recOn, Equiv.refl, False.elim, Fintype, Fintype.card, Fintype.card_eq, Fintype.ofEquiv, Fintype.truncEquivFin, Trunc.recOnSubsingleton, card_eq, equivCongr, fintypePerm, ofEquiv, recOnSubsingleton, truncEquivFin, x.symm
-/
instance Equiv.instFintype [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equiv.refl α) (eα.trans (Eq.recOn h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

@[to_additive]
/--
Instance `MulEquiv.instFintype` / 实例 `MulEquiv.instFintype`

English:
instance MulEquiv.instFintype
  body: Equiv.instFintype.elems.filterMap
    (fun e => if h : forall a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none) (by aesop)
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩

中文:
实例 乘法等价.instFintype
  定义体: Equiv.instFintype.elems.filterMap
    (fun e => if h : forall a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none) (by aesop)
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩

Depends on / 依赖: Equiv.instFintype.elems.filterMap, filterMap, instFintype
-/
instance MulEquiv.instFintype
    {α β : Type*} [Mul α] [Mul β] [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α ≃* β) where
  elems := Equiv.instFintype.elems.filterMap
    (fun e => if h : forall a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none) (by aesop)
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩

/--
theorem `Fintype.card_perm` / 定理 `Fintype.card_perm`

English:
theorem Fintype.card_perm
  given: [Fintype α]
  statement: Fintype.card (Perm α) = (Fintype.card α)!
  proof: Subsingleton.elim (@fintypePerm α _ _) (@Equiv.instFintype α α _ _ _ _) ▸ card_perms_of_finset _

中文:
定理 有限类型.card_perm
  条件: [有限类型 α]
  结论: 有限类型.card (置换 α) = (有限类型.card α)!
  证明: Subsingleton.elim (@fintypePerm α _ _) (@Equiv.instFintype α α _ _ _ _) ▸ card_perms_of_finset _

Depends on / 依赖: Equiv.instFintype, Subsingleton, Subsingleton.elim, card_perms_of_finset, fintypePerm, instFintype
-/
theorem Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)! :=
  Subsingleton.elim (@fintypePerm α _ _) (@Equiv.instFintype α α _ _ _ _) ▸ card_perms_of_finset _

/--
theorem `Fintype.card_equiv` / 定理 `Fintype.card_equiv`

English:
theorem Fintype.card_equiv
  given: [Fintype α] [Fintype β] (e : α ≃ β)
  proof: Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm

中文:
定理 有限类型.card_equiv
  条件: [有限类型 α] [有限类型 β] (e : α ≃ β)
  证明: Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm

Depends on / 依赖: Equiv.refl, Fintype, Fintype.card_congr, Fintype.card_perm, card_congr, card_perm, equivCongr
-/
theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equivCongr (Equiv.refl α) e) ▸ Fintype.card_perm
