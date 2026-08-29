/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Uniquely Decodable Codes

This file defines uniquely decodable codes and proves basic properties.

## Main definitions

* `UniquelyDecodable`: A set of codewords is uniquely decodable if distinct concatenations
  of codewords yield distinct strings.

## Main results

* `UniquelyDecodable.epsilon_not_mem`: Uniquely decodable codes cannot contain the empty
  string.
* `UniquelyDecodable.flatten_injective`: The flatten function is injective on lists of
  codewords from a uniquely decodable code.
-/

@[expose] public section

namespace InformationTheory

variable {α : Type*}

/--
Definition of `UniquelyDecodable` / `UniquelyDecodable` 的定义

English:
definition UniquelyDecodable
  signature: (S : Set (List α))
  body: forall (L₁ L₂ : List (List α)),
    (forall w in L₁, w in S) -> (forall w in L₂, w in S) ->
    L₁.flatten = L₂.flatten -> L₁ = L₂

中文:
定义 UniquelyDecodable
  签名: (S : 集合 (列表 α))
  定义体: forall (L₁ L₂ : List (List α)),
    (forall w in L₁, w in S) -> (forall w in L₂, w in S) ->
    L₁.flatten = L₂.flatten -> L₁ = L₂

Depends on / 依赖: flatten
-/
def UniquelyDecodable (S : Set (List α)) : Prop :=
  forall (L₁ L₂ : List (List α)),
    (forall w in L₁, w in S) -> (forall w in L₂, w in S) ->
    L₁.flatten = L₂.flatten -> L₁ = L₂

variable {S : Set (List α)}

/--
lemma `UniquelyDecodable.epsilon_not_mem` / 引理 `UniquelyDecodable.epsilon_not_mem`

English:
lemma UniquelyDecodable.epsilon_not_mem
  proof: by
  simpa using h [[]] [[], []]

中文:
引理 UniquelyDecodable.epsilon_not_mem
  证明: by
  simpa using h [[]] [[], []]
-/
lemma UniquelyDecodable.epsilon_not_mem
    (h : UniquelyDecodable S) :
    [] ∉ S := by
  simpa using h [[]] [[], []]

/--
lemma `UniquelyDecodable.flatten_injective` / 引理 `UniquelyDecodable.flatten_injective`

English:
lemma UniquelyDecodable.flatten_injective
  given: (h : UniquelyDecodable S)
  proof: by
  intro L₁ L₂ hflat
  apply Subtype.ext
  exact h L₁.val L₂.val L₁.prop L₂.prop hflat

中文:
引理 UniquelyDecodable.flatten_injective
  条件: (h : UniquelyDecodable S)
  证明: by
  intro L₁ L₂ hflat
  apply Subtype.ext
  exact h L₁.val L₂.val L₁.prop L₂.prop hflat

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma UniquelyDecodable.flatten_injective (h : UniquelyDecodable S) :
    Function.Injective (fun (L : {L : List (List α) // forall x in L, x in S}) => L.val.flatten) := by
  intro L₁ L₂ hflat
  apply Subtype.ext
  exact h L₁.val L₂.val L₁.prop L₂.prop hflat

end InformationTheory
