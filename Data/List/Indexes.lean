/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
module

public import Mathlib.Data.List.Defs

/-!
# Lemmas about `List.*Idx` functions.

Some specification lemmas for `List.mapIdx`, `List.mapIdxM`, `List.foldlIdx` and `List.foldrIdx`.

As of 2025-01-29, these are not used anywhere in Mathlib. Moreover, with
`List.enum` and `List.enumFrom` being replaced by `List.zipIdx`
in Lean's `nightly-2025-01-29` release, they now use deprecated functions and theorems.
Rather than updating this unused material, we are deprecating it.
Anyone wanting to restore this material is welcome to do so, but will need to update uses of
`List.enum` and `List.enumFrom` to use `List.zipIdx` instead.
However, note that this material will later be implemented in the Lean standard library.
-/

public section

assert_not_exists MonoidWithZero

universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapIdx

/--
theorem `mapIdx_append_one` / 定理 `mapIdx_append_one`

English:
theorem mapIdx_append_one
  statement: forall {f : Nat -> α -> β} {l : List α} {e : α},
  proof: mapIdx_concat

中文:
定理 mapIdx_append_one
  结论: 对任意 {f : 自然数 -> α -> β} {l : List α} {e : α},
  证明: mapIdx_concat

Depends on / 依赖: mapIdx_concat
-/
theorem mapIdx_append_one : forall {f : Nat -> α -> β} {l : List α} {e : α},
    mapIdx f (l ++ [e]) = mapIdx f l ++ [f l.length e] :=
  mapIdx_concat

/--
theorem `mapIdx_eq_ofFn` / 定理 `mapIdx_eq_ofFn`

English:
theorem mapIdx_eq_ofFn
  given: (l : List α) (f : Nat -> α -> β)
  proof: by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

中文:
定理 mapIdx_eq_ofFn
  条件: (l : List α) (f : 自然数 -> α -> β)
  证明: by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

Depends on / 依赖: generalizing
-/
theorem mapIdx_eq_ofFn (l : List α) (f : Nat -> α -> β) :
    l.mapIdx f = ofFn fun i : Fin l.length => f (i : Nat) (l.get i) := by
  induction l generalizing f with
  | nil => simp
  | cons _ _ IH => simp [IH]

end MapIdx

section MapIdxM'

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m]

/--
theorem `mapIdxMAux'_eq_mapIdxMGo` / 定理 `mapIdxMAux'_eq_mapIdxMGo`

English:
theorem mapIdxMAux'_eq_mapIdxMGo
  given: {α} (f : Nat -> α -> m PUnit) (as : List α) (arr : Array PUnit)
  proof: by
  induction as generalizing arr with
  | nil => simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  | cons head tail ih =>
    simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind_map, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go]
    genera

中文:
定理 mapIdxMAux'_eq_mapIdxMGo
  条件: {α} (f : 自然数 -> α -> m PUnit) (as : List α) (arr : Array PUnit)
  证明: by
  induction as generalizing arr with
  | nil => simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  | cons head tail ih =>
    simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind_map, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go]
    genera

Depends on / 依赖: Array.size, Array.size_push, LawfulMonad, LawfulMonad.bind_assoc, arr.push, arr.size, bind_assoc, bind_pure_unit, generalize, generalizing, mapIdxM, mapIdxM.go, mapIdxMAux, map_eq_pure_bind, map_pure, pure_bind, seqRight_eq, seq_eq_bind_map, seq_pure, size_push
-/
theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : Nat -> α -> m PUnit) (as : List α) (arr : Array PUnit) :
    mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.unit := by
  induction as generalizing arr with
  | nil => simp only [mapIdxMAux', mapIdxM.go, seqRight_eq, map_pure, seq_pure]
  | cons head tail ih =>
    simp only [mapIdxMAux', seqRight_eq, map_eq_pure_bind, seq_eq_bind_map, bind_pure_unit,
      LawfulMonad.bind_assoc, pure_bind, mapIdxM.go]
    generalize (f (Array.size arr) head) = head
    have : (arr.push ⟨⟩).size = arr.size + 1 := Array.size_push _
    rw [← this]; rw [ih]
    simp only [seqRight_eq, map_eq_pure_bind, seq_pure, LawfulMonad.bind_assoc, pure_bind]

/--
theorem `mapIdxM'_eq_mapIdxM` / 定理 `mapIdxM'_eq_mapIdxM`

English:
theorem mapIdxM'_eq_mapIdxM
  given: {α} (f : Nat -> α -> m PUnit) (as : List α)
  proof: mapIdxMAux'_eq_mapIdxMGo f as #[]

中文:
定理 mapIdxM'_eq_mapIdxM
  条件: {α} (f : 自然数 -> α -> m PUnit) (as : List α)
  证明: mapIdxMAux'_eq_mapIdxMGo f as #[]
-/
theorem mapIdxM'_eq_mapIdxM {α} (f : Nat -> α -> m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit :=
  mapIdxMAux'_eq_mapIdxMGo f as #[]

end MapIdxM'

end List
