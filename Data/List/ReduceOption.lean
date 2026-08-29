/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Anthony DeRossi
-/
module

public import Mathlib.Data.List.Basic

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

public section

namespace List

variable {α β : Type*}

@[simp]
/--
theorem `reduceOption_cons_of_some` / 定理 `reduceOption_cons_of_some`

English:
theorem reduceOption_cons_of_some
  given: (x : α) (l : List (Option α))
  proof: by
  simp only [reduceOption, filterMap, id]

@[simp]

中文:
定理 reduceOption_cons_of_some
  条件: (x : α) (l : List (Option α))
  证明: by
  simp only [reduceOption, filterMap, id]

@[simp]

Depends on / 依赖: filterMap, reduceOption
-/
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id]

@[simp]
/--
theorem `reduceOption_cons_of_none` / 定理 `reduceOption_cons_of_none`

English:
theorem reduceOption_cons_of_none
  given: (l : List (Option α))
  proof: by simp only [reduceOption, filterMap, id]

@[simp]

中文:
定理 reduceOption_cons_of_none
  条件: (l : List (Option α))
  证明: by simp only [reduceOption, filterMap, id]

@[simp]

Depends on / 依赖: filterMap, reduceOption
-/
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]

@[simp]
/--
theorem `reduceOption_nil` / 定理 `reduceOption_nil`

English:
theorem reduceOption_nil
  statement: @reduceOption α [] = []
  proof: rfl

@[simp]

中文:
定理 reduceOption_nil
  结论: @reduceOption α [] = []
  证明: rfl

@[simp]
-/
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl

@[simp]
/--
theorem `reduceOption_map` / 定理 `reduceOption_map`

English:
theorem reduceOption_map
  given: {l : List (Option α)} {f : α -> β}
  proof: by
  induction l with
  | nil => simp only [reduceOption_nil, map_nil]
  | cons hd tl hl =>
    cases hd <;> simpa [Option.map_some, map, eq_self_iff_true, reduceOption_cons_of_some] using hl

中文:
定理 reduceOption_map
  条件: {l : List (Option α)} {f : α -> β}
  证明: by
  induction l with
  | nil => simp only [reduceOption_nil, map_nil]
  | cons hd tl hl =>
    cases hd <;> simpa [Option.map_some, map, eq_self_iff_true, reduceOption_cons_of_some] using hl

Depends on / 依赖: Option.map_some, eq_self_iff_true, map_nil, map_some, reduceOption_cons_of_some, reduceOption_nil
-/
theorem reduceOption_map {l : List (Option α)} {f : α -> β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction l with
  | nil => simp only [reduceOption_nil, map_nil]
  | cons hd tl hl =>
    cases hd <;> simpa [Option.map_some, map, eq_self_iff_true, reduceOption_cons_of_some] using hl

/--
theorem `reduceOption_append` / 定理 `reduceOption_append`

English:
theorem reduceOption_append
  given: (l l' : List (Option α))
  proof: filterMap_append

@[simp]

中文:
定理 reduceOption_append
  条件: (l l' : List (Option α))
  证明: filterMap_append

@[simp]

Depends on / 依赖: filterMap_append
-/
theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append

@[simp]
/--
theorem `reduceOption_replicate_none` / 定理 `reduceOption_replicate_none`

English:
theorem reduceOption_replicate_none
  given: {n : Nat}
  statement: (replicate n (@none α)).reduceOption = []
  proof: by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]

中文:
定理 reduceOption_replicate_none
  条件: {n : 自然数}
  结论: (replicate n (@none α)).reduceOption = []
  证明: by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]

Depends on / 依赖: filterMap_replicate_of_none, id_def, reduceOption
-/
theorem reduceOption_replicate_none {n : Nat} : (replicate n (@none α)).reduceOption = [] := by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]

/--
theorem `reduceOption_eq_nil_iff` / 定理 `reduceOption_eq_nil_iff`

English:
theorem reduceOption_eq_nil_iff
  given: (l : List (Option α))
  proof: by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · grind

中文:
定理 reduceOption_eq_nil_iff
  条件: (l : List (Option α))
  证明: by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · grind

Depends on / 依赖: eq_replicate_of_mem, filterMap_eq_nil_iff, l.length, length, reduceOption
-/
theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ exists n, l = replicate n none := by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · grind

/--
theorem `reduceOption_eq_singleton_iff` / 定理 `reduceOption_eq_singleton_iff`

English:
theorem reduceOption_eq_singleton_iff
  given: (l : List (Option α)) (a : α)
  proof: by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h]; rw [hl₁]; rw [hl₂]
    use l₁.length, l₂.len

中文:
定理 reduceOption_eq_singleton_iff
  条件: (l : List (Option α)) (a : α)
  证明: by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h]; rw [hl₁]; rw [hl₂]
    use l₁.length, l₂.len

Depends on / 依赖: Option.some.injEq, eq_replicate_of_mem, filterMap_append, filterMap_cons_some, filterMap_eq_cons_iff, filterMap_eq_nil_iff, filterMap_replicate_of_none, id_eq, length, nil_append, reduceOption
-/
theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ exists m n, l = replicate m none ++ some a :: replicate n none := by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h]; rw [hl₁]; rw [hl₂]
    use l₁.length, l₂.length
  · intro ⟨_, _, h⟩
    simp only [h, filterMap_append, filterMap_cons_some, filterMap_replicate_of_none, id_eq,
      nil_append, Option.some.injEq]

/--
theorem `reduceOption_eq_append_iff` / 定理 `reduceOption_eq_append_iff`

English:
theorem reduceOption_eq_append_iff
  given: (l : List (Option α)) (l'₁ l'₂ : List α)
  proof: by
  dsimp [reduceOption]
  exact filterMap_eq_append_iff

中文:
定理 reduceOption_eq_append_iff
  条件: (l : List (Option α)) (l'₁ l'₂ : List α)
  证明: by
  dsimp [reduceOption]
  exact filterMap_eq_append_iff

Depends on / 依赖: filterMap_eq_append_iff, reduceOption
-/
theorem reduceOption_eq_append_iff (l : List (Option α)) (l'₁ l'₂ : List α) :
    l.reduceOption = l'₁ ++ l'₂ ↔
      exists l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l₂.reduceOption = l'₂ := by
  dsimp [reduceOption]
  exact filterMap_eq_append_iff

/--
theorem `reduceOption_eq_concat_iff` / 定理 `reduceOption_eq_concat_iff`

English:
theorem reduceOption_eq_concat_iff
  given: (l : List (Option α)) (l' : List α) (a : α)
  proof: by
  rw [concat_eq_append]
  constructor
  · intro h
    rw [reduceOption_eq_append_iff] at h
    obtain ⟨l₁, _, h, hl₁, hl₂⟩ := h
    rw [reduceOption_eq_singleton_iff] at hl₂
    obtain ⟨m, n, hl₂⟩ := hl₂
    use l₁ ++ replicate m none, replicate n none
    simp_rw [h, reduceOption_append, reduceO

中文:
定理 reduceOption_eq_concat_iff
  条件: (l : List (Option α)) (l' : List α) (a : α)
  证明: by
  rw [concat_eq_append]
  constructor
  · intro h
    rw [reduceOption_eq_append_iff] at h
    obtain ⟨l₁, _, h, hl₁, hl₂⟩ := h
    rw [reduceOption_eq_singleton_iff] at hl₂
    obtain ⟨m, n, hl₂⟩ := hl₂
    use l₁ ++ replicate m none, replicate n none
    simp_rw [h, reduceOption_append, reduceO

Depends on / 依赖: and_self, append_assoc, append_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some, reduceOption_eq_append_iff, reduceOption_eq_singleton_iff, reduceOption_replicate_none, replicate, simp_rw
-/
theorem reduceOption_eq_concat_iff (l : List (Option α)) (l' : List α) (a : α) :
    l.reduceOption = l'.concat a ↔
      exists l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = [] := by
  rw [concat_eq_append]
  constructor
  · intro h
    rw [reduceOption_eq_append_iff] at h
    obtain ⟨l₁, _, h, hl₁, hl₂⟩ := h
    rw [reduceOption_eq_singleton_iff] at hl₂
    obtain ⟨m, n, hl₂⟩ := hl₂
    use l₁ ++ replicate m none, replicate n none
    simp_rw [h, reduceOption_append, reduceOption_replicate_none, append_assoc, append_nil, hl₁,
      hl₂, and_self]
  · intro ⟨_, _, h, hl₁, hl₂⟩
    rw [h]; rw [reduceOption_append]; rw [reduceOption_cons_of_some]; rw [hl₁]; rw [hl₂]

/--
theorem `reduceOption_length_eq` / 定理 `reduceOption_length_eq`

English:
theorem reduceOption_length_eq
  given: {l : List (Option α)}
  proof: by
  induction l with
  | nil => simp_rw [reduceOption_nil, filter_nil, length]
  | cons hd tl hl => cases hd <;> simp [hl]

中文:
定理 reduceOption_length_eq
  条件: {l : List (Option α)}
  证明: by
  induction l with
  | nil => simp_rw [reduceOption_nil, filter_nil, length]
  | cons hd tl hl => cases hd <;> simp [hl]

Depends on / 依赖: filter_nil, length, reduceOption_nil, simp_rw
-/
theorem reduceOption_length_eq {l : List (Option α)} :
    l.reduceOption.length = (l.filter Option.isSome).length := by
  induction l with
  | nil => simp_rw [reduceOption_nil, filter_nil, length]
  | cons hd tl hl => cases hd <;> simp [hl]

/--
theorem `length_eq_reduceOption_length_add_filter_none` / 定理 `length_eq_reduceOption_length_add_filter_none`

English:
theorem length_eq_reduceOption_length_add_filter_none
  given: {l : List (Option α)}
  proof: by
  simp_rw [reduceOption_length_eq, l.length_eq_length_filter_add Option.isSome, Option.not_isSome]

中文:
定理 length_eq_reduceOption_length_add_filter_none
  条件: {l : List (Option α)}
  证明: by
  simp_rw [reduceOption_length_eq, l.length_eq_length_filter_add Option.isSome, Option.not_isSome]

Depends on / 依赖: Option.isSome, Option.not_isSome, isSome, l.length_eq_length_filter_add, length_eq_length_filter_add, not_isSome, reduceOption_length_eq, simp_rw
-/
theorem length_eq_reduceOption_length_add_filter_none {l : List (Option α)} :
    l.length = l.reduceOption.length + (l.filter Option.isNone).length := by
  simp_rw [reduceOption_length_eq, l.length_eq_length_filter_add Option.isSome, Option.not_isSome]

/--
theorem `reduceOption_length_le` / 定理 `reduceOption_length_le`

English:
theorem reduceOption_length_le
  given: (l : List (Option α))
  statement: l.reduceOption.length <= l.length
  proof: by
  rw [length_eq_reduceOption_length_add_filter_none]
  apply Nat.le_add_right

中文:
定理 reduceOption_length_le
  条件: (l : List (Option α))
  结论: l.reduceOption.length <= l.length
  证明: by
  rw [length_eq_reduceOption_length_add_filter_none]
  apply Nat.le_add_right

Depends on / 依赖: Nat.le_add_right, le_add_right, length_eq_reduceOption_length_add_filter_none
-/
theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length <= l.length := by
  rw [length_eq_reduceOption_length_add_filter_none]
  apply Nat.le_add_right

/--
theorem `reduceOption_length_eq_iff` / 定理 `reduceOption_length_eq_iff`

English:
theorem reduceOption_length_eq_iff
  given: {l : List (Option α)}
  proof: by
  rw [reduceOption_length_eq]; rw [List.length_filter_eq_length_iff]

中文:
定理 reduceOption_length_eq_iff
  条件: {l : List (Option α)}
  证明: by
  rw [reduceOption_length_eq]; rw [List.length_filter_eq_length_iff]

Depends on / 依赖: List.length_filter_eq_length_iff, length_filter_eq_length_iff, reduceOption_length_eq
-/
theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ forall x in l, Option.isSome x := by
  rw [reduceOption_length_eq]; rw [List.length_filter_eq_length_iff]

/--
theorem `reduceOption_length_lt_iff` / 定理 `reduceOption_length_lt_iff`

English:
theorem reduceOption_length_lt_iff
  given: {l : List (Option α)}
  proof: by
  rw [Nat.lt_iff_le_and_ne]; rw [and_iff_right (reduceOption_length_le l)]; rw [Ne]; rw [reduceOption_length_eq_iff]
  induction l
  · simp
  · grind [cases Option]

中文:
定理 reduceOption_length_lt_iff
  条件: {l : List (Option α)}
  证明: by
  rw [Nat.lt_iff_le_and_ne]; rw [and_iff_right (reduceOption_length_le l)]; rw [Ne]; rw [reduceOption_length_eq_iff]
  induction l
  · simp
  · grind [cases Option]

Depends on / 依赖: Nat.lt_iff_le_and_ne, and_iff_right, lt_iff_le_and_ne, reduceOption_length_eq_iff, reduceOption_length_le
-/
theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none in l := by
  rw [Nat.lt_iff_le_and_ne]; rw [and_iff_right (reduceOption_length_le l)]; rw [Ne]; rw [reduceOption_length_eq_iff]
  induction l
  · simp
  · grind [cases Option]

/--
theorem `reduceOption_singleton` / 定理 `reduceOption_singleton`

English:
theorem reduceOption_singleton
  given: (x : Option α)
  statement: [x].reduceOption = x.toList
  proof: by cases x <;> rfl

中文:
定理 reduceOption_singleton
  条件: (x : Option α)
  结论: [x].reduceOption = x.toList
  证明: by cases x <;> rfl
-/
theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl

/--
theorem `reduceOption_concat` / 定理 `reduceOption_concat`

English:
theorem reduceOption_concat
  given: (l : List (Option α)) (x : Option α)
  proof: by
  induction l generalizing x with
  | nil => cases x <;> simp [Option.toList]
  | cons hd tl hl =>
    simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]

中文:
定理 reduceOption_concat
  条件: (l : List (Option α)) (x : Option α)
  证明: by
  induction l generalizing x with
  | nil => cases x <;> simp [Option.toList]
  | cons hd tl hl =>
    simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]

Depends on / 依赖: Option.toList, concat_eq_append, generalizing, reduceOption_append, toList
-/
theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction l generalizing x with
  | nil => cases x <;> simp [Option.toList]
  | cons hd tl hl =>
    simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]

/--
theorem `reduceOption_concat_of_some` / 定理 `reduceOption_concat_of_some`

English:
theorem reduceOption_concat_of_some
  given: (l : List (Option α)) (x : α)
  proof: by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]

中文:
定理 reduceOption_concat_of_some
  条件: (l : List (Option α)) (x : α)
  证明: by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]

Depends on / 依赖: concat_eq_append, reduceOption_append, reduceOption_cons_of_some, reduceOption_nil
-/
theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]

/--
theorem `reduceOption_mem_iff` / 定理 `reduceOption_mem_iff`

English:
theorem reduceOption_mem_iff
  given: {l : List (Option α)} {x : α}
  statement: x in l.reduceOption ↔ some x in l
  proof: by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]

中文:
定理 reduceOption_mem_iff
  条件: {l : List (Option α)} {x : α}
  结论: x in l.reduceOption ↔ some x in l
  证明: by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]

Depends on / 依赖: exists_eq_right, mem_filterMap, reduceOption
-/
theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x in l.reduceOption ↔ some x in l := by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]

/--
theorem `reduceOption_getElem?_iff` / 定理 `reduceOption_getElem?_iff`

English:
theorem reduceOption_getElem?_iff
  given: {l : List (Option α)} {x : α}
  proof: by
  rw [← mem_iff_getElem?]; rw [← mem_iff_getElem?]; rw [reduceOption_mem_iff]

中文:
定理 reduceOption_getElem?_iff
  条件: {l : List (Option α)} {x : α}
  证明: by
  rw [← mem_iff_getElem?]; rw [← mem_iff_getElem?]; rw [reduceOption_mem_iff]

Depends on / 依赖: mem_iff_getElem, reduceOption_mem_iff
-/
theorem reduceOption_getElem?_iff {l : List (Option α)} {x : α} :
    (exists i : Nat, l[i]? = some (some x)) ↔ exists i : Nat, l.reduceOption[i]? = some x := by
  rw [← mem_iff_getElem?]; rw [← mem_iff_getElem?]; rw [reduceOption_mem_iff]

end List
