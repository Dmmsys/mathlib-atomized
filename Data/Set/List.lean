/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Defs

/-!
# Lemmas about `List`s and `Set.range`

In this file we prove lemmas about range of some operations on lists.
-/

public section


open List

variable {α β : Type*} (l : List α)

namespace Set

/--
theorem `range_list_map` / 定理 `range_list_map`

English:
theorem range_list_map
  given: (f : α -> β)
  statement: range (map f) = { l | forall x in l, x in range f }
  proof: by
  refine antisymm (range_subset_iff.2 fun l => forall_mem_map.2 fun y _ => mem_range_self _)
      fun l hl => ?_
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ihl =>
rcases ihl fun x hx => hl x subset_cons_self _ _ hx with ⟨l, rfl⟩
    rcases hl a mem_cons_self with ⟨a, rfl⟩
    exa

中文:
定理 range_list_map
  条件: (f : α -> β)
  结论: range (map f) = { l | 对任意 x in l, x in range f }
  证明: by
  refine antisymm (range_subset_iff.2 fun l => forall_mem_map.2 fun y _ => mem_range_self _)
      fun l hl => ?_
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ihl =>
rcases ihl fun x hx => hl x subset_cons_self _ _ hx with ⟨l, rfl⟩
    rcases hl a mem_cons_self with ⟨a, rfl⟩
    exa

Depends on / 依赖: antisymm, forall_mem_map, map_cons, mem_cons_self, mem_range_self, range_subset_iff, subset_cons_self
-/
theorem range_list_map (f : α -> β) : range (map f) = { l | forall x in l, x in range f } := by
  refine antisymm (range_subset_iff.2 fun l => forall_mem_map.2 fun y _ => mem_range_self _)
      fun l hl => ?_
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ihl =>
rcases ihl fun x hx => hl x subset_cons_self _ _ hx with ⟨l, rfl⟩
    rcases hl a mem_cons_self with ⟨a, rfl⟩
    exact ⟨a :: l, map_cons⟩

/--
theorem `range_list_map_coe` / 定理 `range_list_map_coe`

English:
theorem range_list_map_coe
  given: (s : Set α)
  statement: range (map ((↑) : s -> α)) = { l | forall x in l, x in s }
  proof: by
  rw [range_list_map]; rw [Subtype.range_coe]

@[simp]

中文:
定理 range_list_map_coe
  条件: (s : Set α)
  结论: range (map ((↑) : s -> α)) = { l | 对任意 x in l, x in s }
  证明: by
  rw [range_list_map]; rw [Subtype.range_coe]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe, range_coe, range_list_map
-/
theorem range_list_map_coe (s : Set α) : range (map ((↑) : s -> α)) = { l | forall x in l, x in s } := by
  rw [range_list_map]; rw [Subtype.range_coe]

@[simp]
/--
theorem `range_list_get` / 定理 `range_list_get`

English:
theorem range_list_get
  statement: range l.get = { x | x in l }
  proof: by
  ext x
  rw [mem_ofPred_eq]; rw [mem_iff_get]; rw [mem_range]

中文:
定理 range_list_get
  结论: range l.get = { x | x in l }
  证明: by
  ext x
  rw [mem_ofPred_eq]; rw [mem_iff_get]; rw [mem_range]

Depends on / 依赖: mem_iff_get, mem_ofPred_eq, mem_range
-/
theorem range_list_get : range l.get = { x | x in l } := by
  ext x
  rw [mem_ofPred_eq]; rw [mem_iff_get]; rw [mem_range]

/--
theorem `range_list_getElem?` / 定理 `range_list_getElem?`

English:
theorem range_list_getElem?
  proof: by
  rw [← range_list_get]; rw [← range_comp]
  refine (range_subset_iff.2 fun n => ?_).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · exact (le_or_gt l.length n).imp getElem?_eq_none_iff.mpr
      (fun hlt => ⟨⟨_, hlt⟩, (getElem?_eq_getElem hlt).symm⟩)
  · exact ⟨_, getElem?_eq_none_iff.mpr le_rfl⟩
  

中文:
定理 range_list_getElem?
  证明: by
  rw [← range_list_get]; rw [← range_comp]
  refine (range_subset_iff.2 fun n => ?_).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · exact (le_or_gt l.length n).imp getElem?_eq_none_iff.mpr
      (fun hlt => ⟨⟨_, hlt⟩, (getElem?_eq_getElem hlt).symm⟩)
  · exact ⟨_, getElem?_eq_none_iff.mpr le_rfl⟩
  

Depends on / 依赖: _eq_getElem, _eq_none_iff, _eq_none_iff.mpr, antisymm, getElem, insert_subset_iff, l.length, le_or_gt, le_rfl, length, range_comp, range_list_get, range_subset_iff
-/
theorem range_list_getElem? :
    range (l[·]? : Nat -> Option α) = insert none (some '' { x | x in l }) := by
  rw [← range_list_get]; rw [← range_comp]
  refine (range_subset_iff.2 fun n => ?_).antisymm (insert_subset_iff.2 ⟨?_, ?_⟩)
  · exact (le_or_gt l.length n).imp getElem?_eq_none_iff.mpr
      (fun hlt => ⟨⟨_, hlt⟩, (getElem?_eq_getElem hlt).symm⟩)
  · exact ⟨_, getElem?_eq_none_iff.mpr le_rfl⟩
  · exact range_subset_iff.2 fun k => ⟨_, getElem?_eq_getElem _⟩

@[simp]
/--
theorem `range_list_getD` / 定理 `range_list_getD`

English:
theorem range_list_getD
  given: (d : α)
  statement: (range fun n : Nat => l[n]?.getD d) = insert d { x | x in l }
  proof: calc
    (range fun n => l[n]?.getD d) = (fun o : Option α => o.getD d) '' range (l[·]?) := by
      simp only [← range_comp, Function.comp_def]
      rfl
    _ = insert d { x | x in l } := by
      simp only [Option.getD, range_list_getElem?, image_insert_eq, image_image, image_id']

@[simp]

中文:
定理 range_list_getD
  条件: (d : α)
  结论: (range fun n : 自然数 => l[n]?.getD d) = insert d { x | x in l }
  证明: calc
    (range fun n => l[n]?.getD d) = (fun o : Option α => o.getD d) '' range (l[·]?) := by
      simp only [← range_comp, Function.comp_def]
      rfl
    _ = insert d { x | x in l } := by
      simp only [Option.getD, range_list_getElem?, image_insert_eq, image_image, image_id']

@[simp]

Depends on / 依赖: Function, Function.comp_def, Option.getD, comp_def, image_id, image_image, image_insert_eq, insert, o.getD, range_comp, range_list_getElem
-/
theorem range_list_getD (d : α) : (range fun n : Nat => l[n]?.getD d) = insert d { x | x in l } :=
  calc
    (range fun n => l[n]?.getD d) = (fun o : Option α => o.getD d) '' range (l[·]?) := by
      simp only [← range_comp, Function.comp_def]
      rfl
    _ = insert d { x | x in l } := by
      simp only [Option.getD, range_list_getElem?, image_insert_eq, image_image, image_id']

@[simp]
/--
theorem `range_list_getI` / 定理 `range_list_getI`

English:
theorem range_list_getI
  given: [Inhabited α] (l : List α)
  proof: by
  unfold List.getI
  simp

中文:
定理 range_list_getI
  条件: [Inhabited α] (l : List α)
  证明: by
  unfold List.getI
  simp

Depends on / 依赖: List.getI
-/
theorem range_list_getI [Inhabited α] (l : List α) :
    range l.getI = insert default { x | x in l } := by
  unfold List.getI
  simp

end Set

/--
Instance `List.canLift` / 实例 `List.canLift`

English:
instance List.canLift
  signature: (c) (p) [CanLift α β c p]
  body: by
    rw [← Set.mem_range]; rw [Set.range_list_map]
    exact fun a ha => CanLift.prf a (H a ha)

中文:
实例 List.canLift
  签名: (c) (p) [CanLift α β c p]
  定义体: by
    rw [← Set.mem_range]; rw [Set.range_list_map]
    exact fun a ha => CanLift.prf a (H a ha)

Depends on / 依赖: CanLift, CanLift.prf, Set.mem_range, Set.range_list_map, mem_range, range_list_map
-/
instance List.canLift (c) (p) [CanLift α β c p] :
    CanLift (List α) (List β) (List.map c) fun l => forall x in l, p x where
  prf l H := by
    rw [← Set.mem_range]; rw [Set.range_list_map]
    exact fun a ha => CanLift.prf a (H a ha)
