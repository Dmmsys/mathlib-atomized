/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.List.FinRange

/-!
# Instances for finite types

This file is a collection of basic `Fintype` instances for types such as `Fin`, `Prod` and pi types.
-/

@[expose] public section

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

/--
Instance `Fin.fintype` / 实例 `Fin.fintype`

English:
instance Fin.fintype
  signature: (n : Nat)
  body: ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

中文:
实例 有限集.fintype
  签名: (n : 自然数)
  定义体: ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

Depends on / 依赖: LawfulOfScientific, LawfulOfScientific.ofScientific_def, List.finRange, List.mem_finRange, List.nodup_finRange, NNRat.cast_ofScientific, NNRatCast, NNRatCast.toOfScientific_def, cast_ofScientific, finRange, mem_finRange, nodup_finRange, ofScientific_def, toOfScientific_def
-/
instance Fin.fintype (n : Nat) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, List.nodup_finRange n⟩, List.mem_finRange⟩

/--
theorem `Fin.univ_def` / 定理 `Fin.univ_def`

English:
theorem Fin.univ_def
  given: (n : Nat)
  statement: (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩
  proof: rfl

中文:
定理 有限集.univ_def
  条件: (n : 自然数)
  结论: (univ : 有限集 (有限集 n)) = ⟨列表.finRange n, 列表.nodup_finRange n⟩
  证明: rfl
-/
theorem Fin.univ_def (n : Nat) : (univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ :=
  rfl

/--
theorem `Finset.univ_fin2` / 定理 `Finset.univ_fin2`

English:
theorem Finset.univ_fin2
  statement: (univ : Finset (Fin 2)) = {0, 1}
  proof: rfl

中文:
定理 有限集.univ_fin2
  结论: (univ : 有限集 (有限集 2)) = {0, 1}
  证明: rfl
-/
theorem Finset.univ_fin2 : (univ : Finset (Fin 2)) = {0, 1} := rfl

/--
theorem `Finset.val_univ_fin` / 定理 `Finset.val_univ_fin`

English:
theorem Finset.val_univ_fin
  given: (n : Nat)
  statement: (Finset.univ : Finset (Fin n)).val = List.finRange n
  proof: rfl

中文:
定理 有限集.val_univ_fin
  条件: (n : 自然数)
  结论: (有限集.univ : 有限集 (有限集 n)).val = 列表.finRange n
  证明: rfl
-/
theorem Finset.val_univ_fin (n : Nat) : (Finset.univ : Finset (Fin n)).val = List.finRange n := rfl

/--
theorem `nonempty_fintype` / 定理 `nonempty_fintype`

English:
theorem nonempty_fintype
  given: (α : Type*) [Finite α]
  statement: Nonempty (Fintype α)
  proof: by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩

中文:
定理 nonempty_fintype
  条件: (α : 类型) [有限 α]
  结论: 非空 (有限类型 α)
  证明: by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩

Depends on / 依赖: Finite, Finite.exists_equiv_fin, e.symm, exists_equiv_fin, ofEquiv
-/
theorem nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α) := by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩

/--
theorem `List.toFinset_finRange` / 定理 `List.toFinset_finRange`

English:
theorem List.toFinset_finRange
  given: (n : Nat)
  statement: (List.finRange n).toFinset = Finset.univ
  proof: by
  ext; simp

中文:
定理 列表.toFinset_finRange
  条件: (n : 自然数)
  结论: (列表.finRange n).toFinset = 有限集.univ
  证明: by
  ext; simp
-/
@[simp] theorem List.toFinset_finRange (n : Nat) : (List.finRange n).toFinset = Finset.univ := by
  ext; simp

/--
theorem `Fin.univ_val_map` / 定理 `Fin.univ_val_map`

English:
theorem Fin.univ_val_map
  given: {n : Nat} (f : Fin n -> α)
  proof: by
  simp [List.ofFn_eq_map, univ_def]

中文:
定理 有限集.univ_val_map
  条件: {n : 自然数} (f : 有限集 n -> α)
  证明: by
  simp [List.ofFn_eq_map, univ_def]
-/
@[simp] theorem Fin.univ_val_map {n : Nat} (f : Fin n -> α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]

/--
theorem `Fin.univ_image_def` / 定理 `Fin.univ_image_def`

English:
theorem Fin.univ_image_def
  given: {n : Nat} [DecidableEq α] (f : Fin n -> α)
  proof: by
  simp [Finset.image]

中文:
定理 有限集.univ_image_def
  条件: {n : 自然数} [DecidableEq α] (f : 有限集 n -> α)
  证明: by
  simp [Finset.image]

Depends on / 依赖: Finset, Finset.image
-/
theorem Fin.univ_image_def {n : Nat} [DecidableEq α] (f : Fin n -> α) :
    Finset.univ.image f = (List.ofFn f).toFinset := by
  simp [Finset.image]

/--
theorem `Fin.univ_map_def` / 定理 `Fin.univ_map_def`

English:
theorem Fin.univ_map_def
  given: {n : Nat} (f : Fin n ↪ α)
  proof: by
  simp [Finset.map]

@[simp]

中文:
定理 有限集.univ_map_def
  条件: {n : 自然数} (f : 有限集 n ↪ α)
  证明: by
  simp [Finset.map]

@[simp]

Depends on / 依赖: Finset, Finset.map
-/
theorem Fin.univ_map_def {n : Nat} (f : Fin n ↪ α) :
    Finset.univ.map f = ⟨List.ofFn f, List.nodup_ofFn.mpr f.injective⟩ := by
  simp [Finset.map]

@[simp]
/--
theorem `Fin.image_succAbove_univ` / 定理 `Fin.image_succAbove_univ`

English:
theorem Fin.image_succAbove_univ
  given: {n : Nat} (i : Fin (n + 1))
  statement: univ.image i.succAbove = {i}ᶜ
  proof: by
  ext m
  simp

@[simp]

中文:
定理 有限集.image_succAbove_univ
  条件: {n : 自然数} (i : 有限集 (n + 1))
  结论: univ.像 i.succAbove = {i}ᶜ
  证明: by
  ext m
  simp

@[simp]
-/
theorem Fin.image_succAbove_univ {n : Nat} (i : Fin (n + 1)) : univ.image i.succAbove = {i}ᶜ := by
  ext m
  simp

@[simp]
/--
theorem `Fin.image_succ_univ` / 定理 `Fin.image_succ_univ`

English:
theorem Fin.image_succ_univ
  given: (n : Nat)
  statement: (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ
  proof: by
  rw [← Fin.succAbove_zero]; rw [Fin.image_succAbove_univ]

@[simp]

中文:
定理 有限集.image_succ_univ
  条件: (n : 自然数)
  结论: (univ : 有限集 (有限集 n)).像 有限集.succ = {0}ᶜ
  证明: by
  rw [← Fin.succAbove_zero]; rw [Fin.image_succAbove_univ]

@[simp]

Depends on / 依赖: Fin.image_succAbove_univ, Fin.succAbove_zero, image_succAbove_univ, succAbove_zero
-/
theorem Fin.image_succ_univ (n : Nat) : (univ : Finset (Fin n)).image Fin.succ = {0}ᶜ := by
  rw [← Fin.succAbove_zero]; rw [Fin.image_succAbove_univ]

@[simp]
/--
theorem `Fin.image_castSucc` / 定理 `Fin.image_castSucc`

English:
theorem Fin.image_castSucc
  given: (n : Nat)
  proof: by
  rw [← Fin.succAbove_last]; rw [Fin.image_succAbove_univ]

中文:
定理 有限集.image_castSucc
  条件: (n : 自然数)
  证明: by
  rw [← Fin.succAbove_last]; rw [Fin.image_succAbove_univ]

Depends on / 依赖: Fin.image_succAbove_univ, Fin.succAbove_last, image_succAbove_univ, succAbove_last
-/
theorem Fin.image_castSucc (n : Nat) :
    (univ : Finset (Fin n)).image Fin.castSucc = {Fin.last n}ᶜ := by
  rw [← Fin.succAbove_last]; rw [Fin.image_succAbove_univ]

/- The following three lemmas use `Finset.cons` instead of `insert` and `Finset.map` instead of
`Finset.image` to reduce proof obligations downstream. -/
/--
theorem `Fin.univ_succ` / 定理 `Fin.univ_succ`

English:
theorem Fin.univ_succ
  given: (n : Nat)
  proof: by
  simp [map_eq_image]

中文:
定理 有限集.univ_succ
  条件: (n : 自然数)
  证明: by
  simp [map_eq_image]

Depends on / 依赖: map_eq_image
-/
theorem Fin.univ_succ (n : Nat) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons 0 (univ.map ⟨Fin.succ, Fin.succ_injective _⟩) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/--
theorem `Fin.univ_castSuccEmb` / 定理 `Fin.univ_castSuccEmb`

English:
theorem Fin.univ_castSuccEmb
  given: (n : Nat)
  proof: by
  simp [map_eq_image]

中文:
定理 有限集.univ_castSuccEmb
  条件: (n : 自然数)
  证明: by
  simp [map_eq_image]

Depends on / 依赖: map_eq_image
-/
theorem Fin.univ_castSuccEmb (n : Nat) :
    (univ : Finset (Fin (n + 1))) =
      Finset.cons (Fin.last n) (univ.map Fin.castSuccEmb) (by simp [map_eq_image]) := by
  simp [map_eq_image]

/--
theorem `Fin.univ_succAbove` / 定理 `Fin.univ_succAbove`

English:
theorem Fin.univ_succAbove
  given: (n : Nat) (p : Fin (n + 1))
  proof: by
  simp [map_eq_image]

中文:
定理 有限集.univ_succAbove
  条件: (n : 自然数) (p : 有限集 (n + 1))
  证明: by
  simp [map_eq_image]

Depends on / 依赖: map_eq_image
-/
theorem Fin.univ_succAbove (n : Nat) (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))) = Finset.cons p (univ.map <| Fin.succAboveEmb p) (by simp) := by
  simp [map_eq_image]

/--
theorem `Fin.univ_image_get` / 定理 `Fin.univ_image_get`

English:
theorem Fin.univ_image_get
  given: [DecidableEq α] (l : List α)
  proof: by
  simp [univ_image_def]

中文:
定理 有限集.univ_image_get
  条件: [DecidableEq α] (l : 列表 α)
  证明: by
  simp [univ_image_def]
-/
@[simp] theorem Fin.univ_image_get [DecidableEq α] (l : List α) :
    Finset.univ.image l.get = l.toFinset := by
  simp [univ_image_def]

/--
theorem `Fin.univ_image_getElem'` / 定理 `Fin.univ_image_getElem'`

English:
theorem Fin.univ_image_getElem'
  given: [DecidableEq β] (l : List α) (f : α -> β)
  proof: by
  simp only [univ_image_def, List.ofFn_getElem_eq_map]

中文:
定理 有限集.univ_image_getElem'
  条件: [DecidableEq β] (l : 列表 α) (f : α -> β)
  证明: by
  simp only [univ_image_def, List.ofFn_getElem_eq_map]
-/
@[simp] theorem Fin.univ_image_getElem' [DecidableEq β] (l : List α) (f : α -> β) :
    Finset.univ.image (fun i : Fin l.length => f <| l[(i : Nat)]) = (l.map f).toFinset := by
  simp only [univ_image_def, List.ofFn_getElem_eq_map]

/--
theorem `Fin.univ_image_get'` / 定理 `Fin.univ_image_get'`

English:
theorem Fin.univ_image_get'
  given: [DecidableEq β] (l : List α) (f : α -> β)
  proof: by
  simp

中文:
定理 有限集.univ_image_get'
  条件: [DecidableEq β] (l : 列表 α) (f : α -> β)
  证明: by
  simp
-/
theorem Fin.univ_image_get' [DecidableEq β] (l : List α) (f : α -> β) :
    Finset.univ.image (f <| l.get ·) = (l.map f).toFinset := by
  simp

/--
lemma `Fin.eq_iff_eq_zero_iff` / 引理 `Fin.eq_iff_eq_zero_iff`

English:
lemma Fin.eq_iff_eq_zero_iff
  given: (a b : Fin 2)
  statement: a = b ↔ (a = 0 ↔ b = 0)
  proof: ⟨by rintro rfl; rfl, fin_two_eq_of_eq_zero_iff⟩

中文:
引理 有限集.eq_iff_eq_zero_iff
  条件: (a b : 有限集 2)
  结论: a = b ↔ (a = 0 ↔ b = 0)
  证明: ⟨by rintro rfl; rfl, fin_two_eq_of_eq_zero_iff⟩

Depends on / 依赖: fin_two_eq_of_eq_zero_iff
-/
lemma Fin.eq_iff_eq_zero_iff (a b : Fin 2) : a = b ↔ (a = 0 ↔ b = 0) :=
  ⟨by rintro rfl; rfl, fin_two_eq_of_eq_zero_iff⟩

/--
Instance `Unique.fintype` / 实例 `Unique.fintype`

English:
instance Unique.fintype
  signature: {α : Type*} [Unique α]
  body: Fintype.ofSubsingleton default

中文:
实例 唯一.fintype
  签名: {α : 类型} [唯一 α]
  定义体: Fintype.ofSubsingleton default

Depends on / 依赖: Fintype, Fintype.ofSubsingleton, ofSubsingleton
-/
instance Unique.fintype {α : Type*} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default

/--
Instance `Fintype.subtypeEq` / 实例 `Fintype.subtypeEq`

English:
instance Fintype.subtypeEq
  signature: (y : α)
  body: Fintype.subtype {y} (by simp)

中文:
实例 有限类型.subtypeEq
  签名: (y : α)
  定义体: Fintype.subtype {y} (by simp)

Depends on / 依赖: Fintype, Fintype.subtype, subtype
-/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y} (by simp)

/--
Instance `Fintype.subtypeEq'` / 实例 `Fintype.subtypeEq'`

English:
instance Fintype.subtypeEq'
  signature: (y : α)
  body: Fintype.subtype {y} (by simp [eq_comm])

中文:
实例 有限类型.subtypeEq'
  签名: (y : α)
  定义体: Fintype.subtype {y} (by simp [eq_comm])

Depends on / 依赖: Fintype, Fintype.subtype, eq_comm, subtype
-/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y} (by simp [eq_comm])

/--
theorem `Fintype.univ_empty` / 定理 `Fintype.univ_empty`

English:
theorem Fintype.univ_empty
  statement: @univ Empty _ = ∅
  proof: rfl

中文:
定理 有限类型.univ_empty
  结论: @univ 空 _ = ∅
  证明: rfl
-/
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl

/--
theorem `Fintype.univ_pempty` / 定理 `Fintype.univ_pempty`

English:
theorem Fintype.univ_pempty
  statement: @univ PEmpty _ = ∅
  proof: rfl

中文:
定理 有限类型.univ_pempty
  结论: @univ 命题空 _ = ∅
  证明: rfl
-/
theorem Fintype.univ_pempty : @univ PEmpty _ = ∅ :=
  rfl

/--
Instance `Unit.fintype` / 实例 `Unit.fintype`

English:
instance Unit.fintype
  signature: : Fintype Unit
  body: Fintype.ofSubsingleton ()

中文:
实例 单元.fintype
  签名: : 有限类型 单元
  定义体: Fintype.ofSubsingleton ()

Depends on / 依赖: Fintype, Fintype.ofSubsingleton, ofSubsingleton
-/
instance Unit.fintype : Fintype Unit :=
  Fintype.ofSubsingleton ()

/--
theorem `Fintype.univ_unit` / 定理 `Fintype.univ_unit`

English:
theorem Fintype.univ_unit
  statement: @univ Unit _ = {()}
  proof: rfl

中文:
定理 有限类型.univ_unit
  结论: @univ 单元 _ = {()}
  证明: rfl
-/
theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl

/--
Instance `PUnit.fintype` / 实例 `PUnit.fintype`

English:
instance PUnit.fintype
  signature: : Fintype PUnit
  body: Fintype.ofSubsingleton PUnit.unit

中文:
实例 命题单元.fintype
  签名: : 有限类型 命题单元
  定义体: Fintype.ofSubsingleton PUnit.unit

Depends on / 依赖: Fintype, Fintype.ofSubsingleton, PUnit.unit, ofSubsingleton
-/
instance PUnit.fintype : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

/--
theorem `Fintype.univ_punit` / 定理 `Fintype.univ_punit`

English:
theorem Fintype.univ_punit
  statement: @univ PUnit _ = {PUnit.unit}
  proof: rfl

@[simp]

中文:
定理 有限类型.univ_punit
  结论: @univ 命题单元 _ = {命题单元.unit}
  证明: rfl

@[simp]
-/
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

@[simp]
/--
theorem `Fintype.univ_bool` / 定理 `Fintype.univ_bool`

English:
theorem Fintype.univ_bool
  statement: @univ Bool _ = {true, false}
  proof: rfl

中文:
定理 有限类型.univ_bool
  结论: @univ 布尔值 _ = {true, false}
  证明: rfl
-/
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
@[instance_reducible]
/--
Definition of `Fintype.prodLeft` / `Fintype.prodLeft` 的定义

English:
definition Fintype.prodLeft
  signature: {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β]
  body: ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

中文:
定义 有限类型.prodLeft
  签名: {α β} [DecidableEq α] [有限类型 (α × β)] [非空 β]
  定义体: ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

Depends on / 依赖: Prod.fst
-/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(@univ (α × β) _).image Prod.fst, fun a => by simp⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
@[instance_reducible]
/--
Definition of `Fintype.prodRight` / `Fintype.prodRight` 的定义

English:
definition Fintype.prodRight
  signature: {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α]
  body: ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩

中文:
定义 有限类型.prodRight
  签名: {α β} [DecidableEq β] [有限类型 (α × β)] [非空 α]
  定义体: ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩

Depends on / 依赖: Prod.snd
-/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(@univ (α × β) _).image Prod.snd, fun b => by simp⟩

/--
Instance `ULift.fintype` / 实例 `ULift.fintype`

English:
instance ULift.fintype
  signature: (α : Type*) [Fintype α]
  body: Fintype.ofEquiv _ Equiv.ulift.symm

中文:
实例 类型层提升.fintype
  签名: (α : 类型) [有限类型 α]
  定义体: Fintype.ofEquiv _ Equiv.ulift.symm

Depends on / 依赖: Equiv.ulift.symm, Fintype, Fintype.ofEquiv, ofEquiv
-/
instance ULift.fintype (α : Type*) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm

/--
Instance `PLift.fintype` / 实例 `PLift.fintype`

English:
instance PLift.fintype
  signature: (α : Type*) [Fintype α]
  body: Fintype.ofEquiv _ Equiv.plift.symm

中文:
实例 命题层提升.fintype
  签名: (α : 类型) [有限类型 α]
  定义体: Fintype.ofEquiv _ Equiv.plift.symm

Depends on / 依赖: Equiv.plift.symm, Fintype, Fintype.ofEquiv, ofEquiv
-/
instance PLift.fintype (α : Type*) [Fintype α] : Fintype (PLift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm

/--
Instance `PLift.fintypeProp` / 实例 `PLift.fintypeProp`

English:
instance PLift.fintypeProp
  signature: (p : Prop) [Decidable p]
  body: ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩

中文:
实例 命题层提升.fintypeProp
  签名: (p : 命题) [可判定 p]
  定义体: ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩
-/
instance PLift.fintypeProp (p : Prop) [Decidable p] : Fintype (PLift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by simp [h]⟩

/--
Instance `Quotient.fintype` / 实例 `Quotient.fintype`

English:
instance Quotient.fintype
  signature: [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α -> α -> Prop)]
  body: Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective

中文:
实例 商.fintype
  签名: [有限类型 α] (s : 集合等价关系 α) [DecidableRel ((· ≈ ·) : α -> α -> 命题)]
  定义体: Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective

Depends on / 依赖: Fintype, Fintype.ofSurjective, Quotient, Quotient.mk, _surjective, ofSurjective
-/
instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α -> α -> Prop)] :
    Fintype (Quotient s) :=
  Fintype.ofSurjective Quotient.mk'' Quotient.mk''_surjective

/--
Instance `PSigma.fintypePropLeft` / 实例 `PSigma.fintypePropLeft`

English:
instance PSigma.fintypePropLeft
  signature: {α : Prop} {β : α -> Type*} [Decidable α] [forall a, Fintype (β a)]
  body: if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩

中文:
实例 命题和类型.fintypePropLeft
  签名: {α : 命题} {β : α -> 类型} [可判定 α] [对任意 a, 有限类型 (β a)]
  定义体: if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩

Depends on / 依赖: Fintype, Fintype.ofEquiv, PSigma, PSigma.snd, ofEquiv
-/
instance PSigma.fintypePropLeft {α : Prop} {β : α -> Type*} [Decidable α] [forall a, Fintype (β a)] :
    Fintype (Σ' a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => (h x.1).elim⟩

/--
Instance `PSigma.fintypePropRight` / 实例 `PSigma.fintypePropRight`

English:
instance PSigma.fintypePropRight
  signature: {α : Type*} {β : α -> Prop} [forall a, Decidable (β a)] [Fintype α]
  body: Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

中文:
实例 命题和类型.fintypePropRight
  签名: {α : 类型} {β : α -> 命题} [对任意 a, 可判定 (β a)] [有限类型 α]
  定义体: Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

Depends on / 依赖: Fintype, Fintype.ofEquiv, ofEquiv
-/
instance PSigma.fintypePropRight {α : Type*} {β : α -> Prop} [forall a, Decidable (β a)] [Fintype α] :
    Fintype (Σ' a, β a) :=
  Fintype.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

/--
Instance `PSigma.fintypePropProp` / 实例 `PSigma.fintypePropProp`

English:
instance PSigma.fintypePropProp
  signature: {α : Prop} {β : α -> Prop} [Decidable α] [forall a, Decidable (β a)]
  body: if h : exists a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩

中文:
实例 命题和类型.fintypePropProp
  签名: {α : 命题} {β : α -> 命题} [可判定 α] [对任意 a, 可判定 (β a)]
  定义体: if h : exists a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩

Depends on / 依赖: h.fst, h.snd
-/
instance PSigma.fintypePropProp {α : Prop} {β : α -> Prop} [Decidable α] [forall a, Decidable (β a)] :
    Fintype (Σ' a, β a) :=
  if h : exists a, β a then ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by simp⟩ else ⟨∅, fun ⟨x, y⟩ =>
    (h ⟨x, y⟩).elim⟩

/--
Instance `pfunFintype` / 实例 `pfunFintype`

English:
instance pfunFintype
  signature: (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, Fintype (α hp)]
  body: if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩

中文:
实例 pfunFintype
  签名: (p : 命题) [可判定 p] (α : p -> 类型) [对任意 hp, 有限类型 (α hp)]
  定义体: if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩

Depends on / 依赖: Fintype, Fintype.ofEquiv, mem_singleton, ofEquiv, singleton
-/
instance pfunFintype (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, Fintype (α hp)] :
    Fintype (forall hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else ⟨singleton fun h => (hp h).elim, fun h => mem_singleton.2
    (funext fun x => by contradiction)⟩

section Trunc

/--
Definition of `truncOfMultisetExistsMem` / `truncOfMultisetExistsMem` 的定义

English:
definition truncOfMultisetExistsMem
  signature: {α} (s : Multiset α)
  body: Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a

中文:
定义 truncOfMultisetExistsMem
  签名: {α} (s : Multiset α)
  定义体: Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a

Depends on / 依赖: False.elim, Quotient, Quotient.recOnSubsingleton, Trunc.mk, recOnSubsingleton
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (exists x, x in s) -> Trunc α :=
  Quotient.recOnSubsingleton s fun l h =>
    match l, h with
    | [], _ => False.elim (by tauto)
    | a :: _, _ => Trunc.mk a

/--
Definition of `truncOfNonemptyFintype` / `truncOfNonemptyFintype` 的定义

English:
definition truncOfNonemptyFintype
  signature: (α) [Nonempty α] [Fintype α]
  body: truncOfMultisetExistsMem Finset.univ.val (by simp)

中文:
定义 truncOfNonemptyFintype
  签名: (α) [非空 α] [有限类型 α]
  定义体: truncOfMultisetExistsMem Finset.univ.val (by simp)

Depends on / 依赖: Finset, Finset.univ.val, truncOfMultisetExistsMem
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val (by simp)

/--
Definition of `truncSigmaOfExists` / `truncSigmaOfExists` 的定义

English:
definition truncSigmaOfExists
  signature: {α} [Fintype α] {P : α -> Prop} [DecidablePred P] (h : exists a, P a)
  body: @truncOfNonemptyFintype (Σ' a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

中文:
定义 truncSigmaOfExists
  签名: {α} [有限类型 α] {P : α -> 命题} [DecidablePred P] (h : 存在 a, P a)
  定义体: @truncOfNonemptyFintype (Σ' a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

Depends on / 依赖: Exists, Exists.elim, truncOfNonemptyFintype
-/
def truncSigmaOfExists {α} [Fintype α] {P : α -> Prop} [DecidablePred P] (h : exists a, P a) :
    Trunc (Σ' a, P a) :=
  @truncOfNonemptyFintype (Σ' a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [Fintype β]

@[simp]
/--
theorem `count_univ` / 定理 `count_univ`

English:
theorem count_univ
  given: [DecidableEq α] (a : α)
  statement: count a Finset.univ.val = 1
  proof: count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]

中文:
定理 count_univ
  条件: [DecidableEq α] (a : α)
  结论: count a 有限集.univ.val = 1
  证明: count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.nodup, count_eq_one_of_mem, mem_univ
-/
theorem count_univ [DecidableEq α] (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _)

@[simp]
/--
theorem `map_univ_val_equiv` / 定理 `map_univ_val_equiv`

English:
theorem map_univ_val_equiv
  given: (e : α ≃ β)
  proof: by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e)]; rw [Finset.map_val]; rw [Equiv.coe_toEmbedding]

中文:
定理 map_univ_val_equiv
  条件: (e : α ≃ β)
  证明: by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e)]; rw [Finset.map_val]; rw [Equiv.coe_toEmbedding]

Depends on / 依赖: Equiv.coe_toEmbedding, Finset, Finset.map_univ_equiv, Finset.map_val, Finset.val, coe_toEmbedding, congr_arg, map_univ_equiv, map_val
-/
theorem map_univ_val_equiv (e : α ≃ β) :
    map e univ.val = univ.val := by
  rw [← congr_arg Finset.val (Finset.map_univ_equiv e)]; rw [Finset.map_val]; rw [Equiv.coe_toEmbedding]

/-- For functions on finite sets, they are bijections iff they map universes into universes. -/
@[simp]
/--
theorem `bijective_iff_map_univ_eq_univ` / 定理 `bijective_iff_map_univ_eq_univ`

English:
theorem bijective_iff_map_univ_eq_univ
  given: (f : α -> β)
  proof: ⟨fun bij => congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq => ⟨
      fun a₁ a₂ => inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b => have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

中文:
定理 bijective_iff_map_univ_eq_univ
  条件: (f : α -> β)
  证明: ⟨fun bij => congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq => ⟨
      fun a₁ a₂ => inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b => have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

Depends on / 依赖: Equiv.ofBijective, congr_arg, eq.symm, inj_on_of_nodup_map, map_univ_equiv, mem_map, mem_map.mp, mem_univ, mem_univ_val, ofBijective, univ.nodup
-/
theorem bijective_iff_map_univ_eq_univ (f : α -> β) :
    f.Bijective ↔ map f (Finset.univ : Finset α).val = univ.val :=
  ⟨fun bij => congr_arg (·.val) (map_univ_equiv <| Equiv.ofBijective f bij),
    fun eq => ⟨
      fun a₁ a₂ => inj_on_of_nodup_map (eq.symm ▸ univ.nodup) _ (mem_univ a₁) _ (mem_univ a₂),
      fun b => have ⟨a, _, h⟩ := mem_map.mp (eq.symm ▸ mem_univ_val b); ⟨a, h⟩⟩⟩

end Multiset

/--
Definition of `seqOfForallFinsetExistsAux` / `seqOfForallFinsetExistsAux` 的定义

English:
definition seqOfForallFinsetExistsAux
  signature: {α : Type*} [DecidableEq α] (P : α -> Prop)

中文:
定义 seqOfForallFinsetExistsAux
  签名: {α : 类型} [DecidableEq α] (P : α -> 命题)
-/
noncomputable def seqOfForallFinsetExistsAux {α : Type*} [DecidableEq α] (P : α -> Prop)
    (r : α -> α -> Prop) (h : forall s : Finset α, exists y, (forall x in s, P x) -> P y ∧ forall x in s, r x y) : Nat -> α
  | n =>
    Classical.choose
      (h
        (Finset.image (fun i : Fin n => seqOfForallFinsetExistsAux P r h i)
          (Finset.univ : Finset (Fin n))))

/--
theorem `exists_seq_of_forall_finset_exists` / 定理 `exists_seq_of_forall_finset_exists`

English:
theorem exists_seq_of_forall_finset_exists
  statement: {α : Type*} (P : α -> Prop) (r : α -> α -> Prop)
  proof: by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : forall s : Finset α, exists y, (forall x in s, P x) -> P y ∧ forall x in s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : forall n : Nat, P (f n) := by
      intro n
      induction n using Nat.strong_induction_on with | _ n IH
      have IH' : forall x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf]; rw [seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

中文:
定理 存在_seq_of_对任意_finset_存在
  结论: {α : 类型} (P : α -> 命题) (r : α -> α -> 命题)
  证明: by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : forall s : Finset α, exists y, (forall x in s, P x) -> P y ∧ forall x in s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : forall n : Nat, P (f n) := by
      intro n
      induction n using Nat.strong_induction_on with | _ n IH
      have IH' : forall x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf]; rw [seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

Depends on / 依赖: Classical, Classical.choose_spec, Finset, Nat.strong_induction_on, Nonempty, choose_spec, classical, seqOfForallFinsetExistsAux, strong_induction_on
-/
theorem exists_seq_of_forall_finset_exists {α : Type*} (P : α -> Prop) (r : α -> α -> Prop)
    (h : forall s : Finset α, (forall x in s, P x) -> exists y, P y ∧ forall x in s, r x y) :
    exists f : Nat -> α, (forall n, P (f n)) ∧ forall m n, m < n -> r (f m) (f n) := by
  classical
    have : Nonempty α := by
      rcases h ∅ (by simp) with ⟨y, _⟩
      exact ⟨y⟩
    choose! F hF using h
    have h' : forall s : Finset α, exists y, (forall x in s, P x) -> P y ∧ forall x in s, r x y := fun s => ⟨F s, hF s⟩
    set f := seqOfForallFinsetExistsAux P r h' with hf
    have A : forall n : Nat, P (f n) := by
      intro n
      induction n using Nat.strong_induction_on with | _ n IH
      have IH' : forall x : Fin n, P (f x) := fun n => IH n.1 n.2
      rw [hf]; rw [seqOfForallFinsetExistsAux]
      exact
        (Classical.choose_spec
            (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n))))
            (by simp [IH'])).1
    refine ⟨f, A, fun m n hmn => ?_⟩
    conv_rhs => rw [hf]
    rw [seqOfForallFinsetExistsAux]
    apply
      (Classical.choose_spec
          (h' (Finset.image (fun i : Fin n => f i) (Finset.univ : Finset (Fin n)))) (by simp [A])).2
    exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

/--
theorem `exists_seq_of_forall_finset_exists'` / 定理 `exists_seq_of_forall_finset_exists'`

English:
theorem exists_seq_of_forall_finset_exists'
  statement: {α : Type*} (P : α -> Prop) (r : α -> α -> Prop)
  proof: by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  grind +splitIndPred

中文:
定理 存在_seq_of_对任意_finset_存在'
  结论: {α : 类型} (P : α -> 命题) (r : α -> α -> 命题)
  证明: by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  grind +splitIndPred

Depends on / 依赖: exists_seq_of_forall_finset_exists, splitIndPred
-/
theorem exists_seq_of_forall_finset_exists' {α : Type*} (P : α -> Prop) (r : α -> α -> Prop)
    [Std.Symm r] (h : forall s : Finset α, (forall x in s, P x) -> exists y, P y ∧ forall x in s, r x y) :
    exists f : Nat -> α, (forall n, P (f n)) ∧ Pairwise (r on f) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine ⟨f, hf, fun m n hmn => ?_⟩
  grind +splitIndPred
