/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableSeparatingOn
public import Mathlib.Topology.Separation.Basic

/-!
# Countable separating families of sets in topological spaces

In this file we show that a T₀ topological space with second countable
topology has a countable family of open (or closed) sets separating the points.
-/

public section

variable {X : Type*}

open Set TopologicalSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: X] {s
  body: by
  suffices HasCountableSeparatingOn s IsOpen univ from .of_subtype fun _ => isOpen_induced_iff.1
  refine ⟨⟨countableBasis s, countable_countableBasis _, fun _ => isOpen_of_mem_countableBasis,
    fun x _ y _ h => ?_⟩⟩
  exact ((isBasis_countableBasis _).inseparable_iff.2 h).eq

中文:
实例 [TopologicalSpace
  签名: X] {s
  定义体: by
  suffices HasCountableSeparatingOn s IsOpen univ from .of_subtype fun _ => isOpen_induced_iff.1
  refine ⟨⟨countableBasis s, countable_countableBasis _, fun _ => isOpen_of_mem_countableBasis,
    fun x _ y _ h => ?_⟩⟩
  exact ((isBasis_countableBasis _).inseparable_iff.2 h).eq

Depends on / 依赖: HasCountableSeparatingOn, IsOpen, countableBasis, countable_countableBasis, inseparable_iff, isBasis_countableBasis, isOpen_induced_iff, isOpen_of_mem_countableBasis, of_subtype
-/
instance [TopologicalSpace X] {s : Set X} [T0Space s] [SecondCountableTopology s] :
    HasCountableSeparatingOn X IsOpen s := by
  suffices HasCountableSeparatingOn s IsOpen univ from .of_subtype fun _ => isOpen_induced_iff.1
  refine ⟨⟨countableBasis s, countable_countableBasis _, fun _ => isOpen_of_mem_countableBasis,
    fun x _ y _ h => ?_⟩⟩
  exact ((isBasis_countableBasis _).inseparable_iff.2 h).eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: X] {s
  body: let ⟨S, hSc, hSo, hS⟩ := h.1
  ⟨compl '' S, hSc.image _, forall_mem_image.2 fun U hU => (hSo U hU).isClosed_compl,
fun x hx y hy h => hS x hx y hy fun _U hU => not_iff_not.1 h _ (mem_image_of_mem _ hU)⟩

中文:
实例 [TopologicalSpace
  签名: X] {s
  定义体: let ⟨S, hSc, hSo, hS⟩ := h.1
  ⟨compl '' S, hSc.image _, forall_mem_image.2 fun U hU => (hSo U hU).isClosed_compl,
fun x hx y hy h => hS x hx y hy fun _U hU => not_iff_not.1 h _ (mem_image_of_mem _ hU)⟩

Depends on / 依赖: forall_mem_image, hSc.image, isClosed_compl, mem_image_of_mem, not_iff_not
-/
instance [TopologicalSpace X] {s : Set X} [h : HasCountableSeparatingOn X IsOpen s] :
    HasCountableSeparatingOn X IsClosed s :=
  let ⟨S, hSc, hSo, hS⟩ := h.1
  ⟨compl '' S, hSc.image _, forall_mem_image.2 fun U hU => (hSo U hU).isClosed_compl,
fun x hx y hy h => hS x hx y hy fun _U hU => not_iff_not.1 h _ (mem_image_of_mem _ hU)⟩
