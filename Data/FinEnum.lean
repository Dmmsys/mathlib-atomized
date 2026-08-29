/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Pi

/-!
Type class for finitely enumerable types. The property is stronger
than `Fintype` in that it assigns each element a rank in a finite
enumeration.
-/

@[expose] public section


universe u v

open Finset

/--
Definition of `FinEnum` / `FinEnum` 的定义

English:
class FinEnum
  parameters: (α : Sort*)
  axioms and operations (3):
    - card : Nat
    - equiv : α ≃ Fin card
    - [decEq : DecidableEq α]

中文:
类 FinEnum
  参数: (α : 类型层*)
  公理与运算 (3 个):
    - card : 自然数
    - equiv : α ≃ 有限集 card
    - [decEq : DecidableEq α]
-/
class FinEnum (α : Sort*) where
  /-- `FinEnum.card` is the cardinality of the `FinEnum` -/
  card : Nat
  /-- `FinEnum.Equiv` states that type `α` is in bijection with `Fin card`,
  the size of the `FinEnum` -/
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]

attribute [instance_reducible, instance 100] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α -> Type v}

/-- transport a `FinEnum` instance across an equivalence -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (α) {β} [FinEnum α] (h : β ≃ α)
  body: card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq

中文:
定义 ofEquiv
  签名: (α) {β} [FinEnum α] (h : β ≃ α)
  定义体: card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq
-/
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β where
  card := card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq

/-- create a `FinEnum` instance from an exhaustive list without duplicates -/
@[instance_reducible]
/--
Definition of `ofNodupList` / `ofNodupList` 的定义

English:
definition ofNodupList
  signature: [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) (h' : List.Nodup xs)
  body: xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [h'.idxOf_getElem]⟩

中文:
定义 ofNodupList
  签名: [DecidableEq α] (xs : 列表 α) (h : 对任意 x : α, x in xs) (h' : 列表.Nodup xs)
  定义体: xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [h'.idxOf_getElem]⟩

Depends on / 依赖: length, xs.length
-/
def ofNodupList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) (h' : List.Nodup xs) :
    FinEnum α where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [h'.idxOf_getElem]⟩

/-- create a `FinEnum` instance from an exhaustive list; duplicates are removed -/
@[instance_reducible]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: [DecidableEq α] (xs : List α) (h : forall x : α, x in xs)
  body: ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)

中文:
定义 ofList
  签名: [DecidableEq α] (xs : 列表 α) (h : 对任意 x : α, x in xs)
  定义体: ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)

Depends on / 依赖: List.nodup_dedup, nodup_dedup, ofNodupList, xs.dedup
-/
def ofList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)

/--
lemma `card_ofList` / 引理 `card_ofList`

English:
lemma card_ofList
  given: [DecidableEq α] (xs : List α) (h : forall x : α, x in xs)
  proof: rfl

中文:
引理 card_ofList
  条件: [DecidableEq α] (xs : 列表 α) (h : 对任意 x : α, x in xs)
  证明: rfl
-/
lemma card_ofList [DecidableEq α] (xs : List α) (h : forall x : α, x in xs) :
    (FinEnum.ofList xs h).card = xs.dedup.length := rfl

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (α) [FinEnum α]
  body: (List.finRange (card α)).map equiv.symm

中文:
定义 toList
  签名: (α) [FinEnum α]
  定义体: (List.finRange (card α)).map equiv.symm

Depends on / 依赖: List.finRange, equiv.symm, finRange
-/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map equiv.symm

open Function

@[simp]
/--
theorem `mem_toList` / 定理 `mem_toList`

English:
theorem mem_toList
  given: [FinEnum α] (x : α)
  statement: x in toList α
  proof: by
  simp only [toList, List.mem_map, List.mem_finRange, true_and]; exists equiv x; simp

@[simp]

中文:
定理 mem_toList
  条件: [FinEnum α] (x : α)
  结论: x in toList α
  证明: by
  simp only [toList, List.mem_map, List.mem_finRange, true_and]; exists equiv x; simp

@[simp]

Depends on / 依赖: List.mem_finRange, List.mem_map, mem_finRange, mem_map, toList, true_and
-/
theorem mem_toList [FinEnum α] (x : α) : x in toList α := by
  simp only [toList, List.mem_map, List.mem_finRange, true_and]; exists equiv x; simp

@[simp]
/--
theorem `nodup_toList` / 定理 `nodup_toList`

English:
theorem nodup_toList
  given: [FinEnum α]
  statement: List.Nodup (toList α)
  proof: by
  simp only [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]

中文:
定理 nodup_toList
  条件: [FinEnum α]
  结论: 列表.Nodup (toList α)
  证明: by
  simp only [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]

Depends on / 依赖: Equiv.injective, List.Nodup.map, List.nodup_finRange, injective, nodup_finRange, toList
-/
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp only [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]

/-- create a `FinEnum` instance using a surjection -/
@[instance_reducible]
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: {β} (f : β -> α) [DecidableEq α] [FinEnum β] (h : Surjective f)
  body: ofList ((toList β).map f) (by intro; simpa using h _)

中文:
定义 ofSurjective
  签名: {β} (f : β -> α) [DecidableEq α] [FinEnum β] (h : 满射 f)
  定义体: ofList ((toList β).map f) (by intro; simpa using h _)

Depends on / 依赖: ofList, toList
-/
def ofSurjective {β} (f : β -> α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simpa using h _)

/-- create a `FinEnum` instance using an injection -/
@[instance_reducible]
/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: {α β} (f : α -> β) [DecidableEq α] [FinEnum β] (h : Injective f)
  body: ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])

中文:
定义 ofInjective
  签名: {α β} (f : α -> β) [DecidableEq α] [FinEnum β] (h : 单射 f)
  定义体: ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])

Depends on / 依赖: Function, Function.partialInv_left, List.mem_filterMap, filterMap, mem_filterMap, mem_toList, ofList, partialInv, partialInv_left, toList, true_and
-/
noncomputable def ofInjective {α β} (f : α -> β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])

/--
Instance `_root_.ULift.instFinEnum` / 实例 `_root_.ULift.instFinEnum`

English:
instance _root_.ULift.instFinEnum
  signature: [FinEnum α]
  body: ⟨card α, Equiv.ulift.trans equiv⟩

@[simp]

中文:
实例 _root_.类型层提升.instFinEnum
  签名: [FinEnum α]
  定义体: ⟨card α, Equiv.ulift.trans equiv⟩

@[simp]

Depends on / 依赖: Equiv.ulift.trans
-/
instance _root_.ULift.instFinEnum [FinEnum α] : FinEnum (ULift α) :=
  ⟨card α, Equiv.ulift.trans equiv⟩

@[simp]
/--
theorem `card_ulift` / 定理 `card_ulift`

English:
theorem card_ulift
  given: [FinEnum (ULift α)] [FinEnum α]
  statement: card (ULift α) = card α
  proof: .trans equiv⟩ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift

中文:
定理 card_ulift
  条件: [FinEnum (类型层提升 α)] [FinEnum α]
  结论: card (类型层提升 α) = card α
  证明: .trans equiv⟩ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift

Depends on / 依赖: Equiv.ulift, Fin.equiv_iff_eq.mp, equiv.symm.trans, equiv_iff_eq
-/
theorem card_ulift [FinEnum (ULift α)] [FinEnum α] : card (ULift α) = card α :=
.trans equiv⟩ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift

section ULift
variable [FinEnum α] (a : α) (a' : ULift α) (i : Fin (card α))

/--
lemma `equiv_up` / 引理 `equiv_up`

English:
lemma equiv_up
  statement: equiv (ULift.up a) = equiv a
  proof: rfl

中文:
引理 equiv_up
  结论: equiv (类型层提升.up a) = equiv a
  证明: rfl
-/
@[simp] lemma equiv_up : equiv (ULift.up a) = equiv a := rfl
/--
lemma `equiv_down` / 引理 `equiv_down`

English:
lemma equiv_down
  statement: equiv a'.down = equiv a'
  proof: rfl

中文:
引理 equiv_down
  结论: equiv a'.down = equiv a'
  证明: rfl
-/
@[simp] lemma equiv_down : equiv a'.down = equiv a' := rfl
/--
lemma `up_equiv_symm` / 引理 `up_equiv_symm`

English:
lemma up_equiv_symm
  statement: ULift.up (equiv.symm i) = (equiv (α := ULift α)).symm i
  proof: rfl

中文:
引理 up_equiv_symm
  结论: 类型层提升.up (equiv.symm i) = (equiv (α := 类型层提升 α)).symm i
  证明: rfl
-/
@[simp] lemma up_equiv_symm : ULift.up (equiv.symm i) = (equiv (α := ULift α)).symm i := rfl
/--
lemma `down_equiv_symm` / 引理 `down_equiv_symm`

English:
lemma down_equiv_symm
  statement: ((equiv (α := ULift α)).symm i).down = equiv.symm i
  proof: rfl

中文:
引理 down_equiv_symm
  结论: ((equiv (α := 类型层提升 α)).symm i).down = equiv.symm i
  证明: rfl
-/
@[simp] lemma down_equiv_symm : ((equiv (α := ULift α)).symm i).down = equiv.symm i := rfl

end ULift

/--
Instance `pempty` / 实例 `pempty`

English:
instance pempty
  signature: : FinEnum PEmpty
  body: ofList [] fun x => PEmpty.elim x

中文:
实例 pempty
  签名: : FinEnum 命题空
  定义体: ofList [] fun x => PEmpty.elim x

Depends on / 依赖: PEmpty, PEmpty.elim, ofList
-/
instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x

/--
lemma `card_pempty` / 引理 `card_pempty`

English:
lemma card_pempty
  statement: FinEnum.card PEmpty = 0
  proof: rfl

中文:
引理 card_pempty
  结论: FinEnum.card 命题空 = 0
  证明: rfl

Depends on / 依赖: binaryRec, binaryRec_eq, dif_pos
-/
@[simp] lemma card_pempty : FinEnum.card PEmpty = 0 := rfl

/--
Instance `empty` / 实例 `empty`

English:
instance empty
  signature: : FinEnum Empty
  body: ofList [] fun x => Empty.elim x

中文:
实例 empty
  签名: : FinEnum 空
  定义体: ofList [] fun x => Empty.elim x

Depends on / 依赖: Empty.elim, ofList
-/
instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x

/--
lemma `card_empty` / 引理 `card_empty`

English:
lemma card_empty
  statement: FinEnum.card Empty = 0
  proof: rfl

中文:
引理 card_empty
  结论: FinEnum.card 空 = 0
  证明: rfl
-/
@[simp] lemma card_empty : FinEnum.card Empty = 0 := rfl

/--
Instance `punit` / 实例 `punit`

English:
instance punit
  signature: : FinEnum PUnit
  body: ofList [PUnit.unit] fun x => by simp

中文:
实例 punit
  签名: : FinEnum 命题单元
  定义体: ofList [PUnit.unit] fun x => by simp

Depends on / 依赖: PUnit.unit, ofList
-/
instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by simp

/--
lemma `card_punit` / 引理 `card_punit`

English:
lemma card_punit
  statement: FinEnum.card PUnit = 1
  proof: rfl

中文:
引理 card_punit
  结论: FinEnum.card 命题单元 = 1
  证明: rfl
-/
@[simp] lemma card_punit : FinEnum.card PUnit = 1 := rfl

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: {β} [FinEnum α] [FinEnum β]
  body: ofList (toList α ×ˢ toList β) fun x => by cases x; simp

中文:
实例 乘积
  签名: {β} [FinEnum α] [FinEnum β]
  定义体: ofList (toList α ×ˢ toList β) fun x => by cases x; simp

Depends on / 依赖: ofList, toList
-/
instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: {β} [FinEnum α] [FinEnum β]
  body: ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp

中文:
实例 求和
  签名: {β} [FinEnum α] [FinEnum β]
  定义体: ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp

Depends on / 依赖: Sum.inl, Sum.inr, ofList, toList
-/
instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (α oplus β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp

/--
Instance `fin` / 实例 `fin`

English:
instance fin
  signature: {n}
  body: ofList (List.finRange _) (by simp)

@[simp]

中文:
实例 fin
  签名: {n}
  定义体: ofList (List.finRange _) (by simp)

@[simp]

Depends on / 依赖: List.finRange, finRange, ofList
-/
instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)

@[simp]
/--
theorem `card_fin` / 定理 `card_fin`

English:
theorem card_fin
  given: {n} [FinEnum (Fin n)]
  statement: card (Fin n) = n
  proof: Fin.equiv_iff_eq.mp ⟨equiv.symm⟩

中文:
定理 card_fin
  条件: {n} [FinEnum (有限集 n)]
  结论: card (有限集 n) = n
  证明: Fin.equiv_iff_eq.mp ⟨equiv.symm⟩

Depends on / 依赖: Fin.equiv_iff_eq.mp, equiv.symm, equiv_iff_eq
-/
theorem card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n := Fin.equiv_iff_eq.mp ⟨equiv.symm⟩

/--
Instance `Quotient.enum` / 实例 `Quotient.enum`

English:
instance Quotient.enum
  signature: [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α -> α -> Prop)]
  body: FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

中文:
实例 商.enum
  签名: [FinEnum α] (s : 集合等价关系 α) [DecidableRel ((· ≈ ·) : α -> α -> 命题)]
  定义体: FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

Depends on / 依赖: FinEnum, FinEnum.ofSurjective, Quotient, Quotient.inductionOn, Quotient.mk, inductionOn, ofSurjective
-/
instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α -> α -> Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

/--
Definition of `Finset.enum` / `Finset.enum` 的定义

English:
definition Finset.enum
  signature: [DecidableEq α]

中文:
定义 有限集.enum
  签名: [DecidableEq α]
-/
def Finset.enum [DecidableEq α] : List α -> List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← Finset.enum xs
    [r, insert x r]

@[simp, grind =]
/--
theorem `Finset.mem_enum` / 定理 `Finset.mem_enum`

English:
theorem Finset.mem_enum
  given: [DecidableEq α] (s : Finset α) (xs : List α)
  proof: by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_notMem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_if

中文:
定理 有限集.mem_enum
  条件: [DecidableEq α] (s : 有限集 α) (xs : 列表 α)
  证明: by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_notMem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_if

Depends on / 依赖: List.bind_eq_flatMap, List.mem_cons, List.mem_flatMap, List.not_mem_nil, bind_eq_flatMap, contextual, eq_comm, eq_empty_iff_forall_notMem, generalizing, mem_cons, mem_flatMap, not_mem_nil, or_false, or_iff_not_imp_left, s.erase
-/
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s in Finset.enum xs ↔ forall x in s, x in xs := by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_notMem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_iff_not_imp_left] at hs
      simp +contextual [eq_comm (a := s), or_iff_not_imp_left, hs]

/--
Instance `Finset.finEnum` / 实例 `Finset.finEnum`

English:
instance Finset.finEnum
  signature: [FinEnum α]
  body: ofList (Finset.enum (toList α)) (by simp)

中文:
实例 有限集.finEnum
  签名: [FinEnum α]
  定义体: ofList (Finset.enum (toList α)) (by simp)

Depends on / 依赖: Finset, Finset.enum, ofList, toList
-/
instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by simp)

/--
Instance `Subtype.finEnum` / 实例 `Subtype.finEnum`

English:
instance Subtype.finEnum
  signature: [FinEnum α] (p : α -> Prop) [DecidablePred p]
  body: ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)

中文:
实例 子类型.finEnum
  签名: [FinEnum α] (p : α -> 命题) [DecidablePred p]
  定义体: ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)

Depends on / 依赖: filterMap, ofList, toList
-/
instance Subtype.finEnum [FinEnum α] (p : α -> Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)

instance (β : α -> Type v) [FinEnum α] [forall a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).flatMap fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)

/--
Instance `PSigma.finEnum` / 实例 `PSigma.finEnum`

English:
instance PSigma.finEnum
  signature: [FinEnum α] [forall a, FinEnum (β a)]
  body: FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)

中文:
实例 命题和类型.finEnum
  签名: [FinEnum α] [对任意 a, FinEnum (β a)]
  定义体: FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)

Depends on / 依赖: Equiv.psigmaEquivSigma, FinEnum, FinEnum.ofEquiv, ofEquiv, psigmaEquivSigma
-/
instance PSigma.finEnum [FinEnum α] [forall a, FinEnum (β a)] : FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)

/--
Instance `PSigma.finEnumPropLeft` / 实例 `PSigma.finEnumPropLeft`

English:
instance PSigma.finEnumPropLeft
  signature: {α : Prop} {β : α -> Type v} [forall a, FinEnum (β a)] [Decidable α]
  body: if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim

中文:
实例 命题和类型.finEnumPropLeft
  签名: {α : 命题} {β : α -> 类型v} [对任意 a, FinEnum (β a)] [可判定 α]
  定义体: if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim

Depends on / 依赖: PSigma, PSigma.mk, ofList, toList
-/
instance PSigma.finEnumPropLeft {α : Prop} {β : α -> Type v} [forall a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ' a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim

/--
Instance `PSigma.finEnumPropRight` / 实例 `PSigma.finEnumPropRight`

English:
instance PSigma.finEnumPropRight
  signature: {β : α -> Prop} [FinEnum α] [forall a, Decidable (β a)]
  body: FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

中文:
实例 命题和类型.finEnumPropRight
  签名: {β : α -> 命题} [FinEnum α] [对任意 a, 可判定 (β a)]
  定义体: FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

Depends on / 依赖: FinEnum, FinEnum.ofEquiv, ofEquiv
-/
instance PSigma.finEnumPropRight {β : α -> Prop} [FinEnum α] [forall a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

/--
Instance `PSigma.finEnumPropProp` / 实例 `PSigma.finEnumPropProp`

English:
instance PSigma.finEnumPropProp
  signature: {α : Prop} {β : α -> Prop} [Decidable α] [forall a, Decidable (β a)]
  body: if h : exists a, β a then ofList [⟨h.fst, h.snd⟩] (by simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim

中文:
实例 命题和类型.finEnumPropProp
  签名: {α : 命题} {β : α -> 命题} [可判定 α] [对任意 a, 可判定 (β a)]
  定义体: if h : exists a, β a then ofList [⟨h.fst, h.snd⟩] (by simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim

Depends on / 依赖: a.fst, a.snd, h.fst, h.snd, ofList
-/
instance PSigma.finEnumPropProp {α : Prop} {β : α -> Prop} [Decidable α] [forall a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  if h : exists a, β a then ofList [⟨h.fst, h.snd⟩] (by simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] (xs
  body: ofList xs.attach (by simp)

中文:
实例 [DecidableEq
  签名: α] (xs
  定义体: ofList xs.attach (by simp)

Depends on / 依赖: attach, ofList, xs.attach
-/
instance [DecidableEq α] (xs : List α) : FinEnum { x : α // x in xs } := ofList xs.attach (by simp)

instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map equiv.symm.toEmbedding
  complete := by intros; simp

/--
theorem `card_eq_fintypeCard` / 定理 `card_eq_fintypeCard`

English:
theorem card_eq_fintypeCard
  given: {α : Type u} [FinEnum α] [Fintype α]
  statement: card α = Fintype.card α
  proof: .inductionOn (fun h => Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩) Fintype.truncEquivFin α

中文:
定理 card_eq_fintypeCard
  条件: {α : 类型u} [FinEnum α] [有限类型 α]
  结论: card α = 有限类型.card α
  证明: .inductionOn (fun h => Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩) Fintype.truncEquivFin α

Depends on / 依赖: Fin.equiv_iff_eq.mp, Fintype, Fintype.truncEquivFin, equiv.symm.trans, equiv_iff_eq, inductionOn, truncEquivFin
-/
theorem card_eq_fintypeCard {α : Type u} [FinEnum α] [Fintype α] : card α = Fintype.card α :=
.inductionOn (fun h => Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩) Fintype.truncEquivFin α

/--
theorem `card_unique` / 定理 `card_unique`

English:
theorem card_unique
  given: {α : Type u} (e₁ e₂ : FinEnum α)
  statement: e₁.card = e₂.card
  proof: calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
.symm _ = _ := @card_eq_fintypeCard _ e₂ inferInstance

中文:
定理 card_unique
  条件: {α : 类型u} (e₁ e₂ : FinEnum α)
  结论: e₁.card = e₂.card
  证明: calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
.symm _ = _ := @card_eq_fintypeCard _ e₂ inferInstance

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, card_eq_fintypeCard
-/
theorem card_unique {α : Type u} (e₁ e₂ : FinEnum α) : e₁.card = e₂.card :=
  calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
.symm _ = _ := @card_eq_fintypeCard _ e₂ inferInstance

/--
theorem `card_eq_zero_iff` / 定理 `card_eq_zero_iff`

English:
theorem card_eq_zero_iff
  given: {α : Type u} [FinEnum α]
  statement: card α = 0 ↔ IsEmpty α
  proof: .trans Fintype.card_eq_zero_iff Eq.congr_left card_eq_fintypeCard

中文:
定理 card_eq_zero_iff
  条件: {α : 类型u} [FinEnum α]
  结论: card α = 0 ↔ 是空 α
  证明: .trans Fintype.card_eq_zero_iff Eq.congr_left card_eq_fintypeCard

Depends on / 依赖: Eq.congr_left, Fintype, Fintype.card_eq_zero_iff, card_eq_fintypeCard, card_eq_zero_iff, congr_left
-/
theorem card_eq_zero_iff {α : Type u} [FinEnum α] : card α = 0 ↔ IsEmpty α :=
.trans Fintype.card_eq_zero_iff Eq.congr_left card_eq_fintypeCard

/--
theorem `card_eq_zero` / 定理 `card_eq_zero`

English:
theorem card_eq_zero
  given: {α : Type u} [FinEnum α] [IsEmpty α]
  statement: card α = 0
  proof: card_eq_zero_iff.mpr ‹_›

中文:
定理 card_eq_zero
  条件: {α : 类型u} [FinEnum α] [是空 α]
  结论: card α = 0
  证明: card_eq_zero_iff.mpr ‹_›

Depends on / 依赖: card_eq_zero_iff, card_eq_zero_iff.mpr
-/
theorem card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.mpr ‹_›

/--
theorem `card_pos_iff` / 定理 `card_pos_iff`

English:
theorem card_pos_iff
  given: {α : Type u} [FinEnum α]
  statement: 0 < card α ↔ Nonempty α
  proof: card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff

中文:
定理 card_pos_iff
  条件: {α : 类型u} [FinEnum α]
  结论: 0 < card α ↔ 非空 α
  证明: card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff

Depends on / 依赖: Fintype, Fintype.card_pos_iff, card_eq_fintypeCard, card_pos_iff
-/
theorem card_pos_iff {α : Type u} [FinEnum α] : 0 < card α ↔ Nonempty α :=
  card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff

/--
lemma `card_pos` / 引理 `card_pos`

English:
lemma card_pos
  given: {α : Type*} [FinEnum α] [Nonempty α]
  statement: 0 < card α
  proof: card_pos_iff.mpr ‹_›

中文:
引理 card_pos
  条件: {α : 类型} [FinEnum α] [非空 α]
  结论: 0 < card α
  证明: card_pos_iff.mpr ‹_›

Depends on / 依赖: card_pos_iff, card_pos_iff.mpr
-/
lemma card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < card α :=
  card_pos_iff.mpr ‹_›

/--
lemma `card_ne_zero` / 引理 `card_ne_zero`

English:
lemma card_ne_zero
  given: {α : Type*} [FinEnum α] [Nonempty α]
  statement: card α != 0
  proof: card_pos.ne'

中文:
引理 card_ne_zero
  条件: {α : 类型} [FinEnum α] [非空 α]
  结论: card α != 0
  证明: card_pos.ne'

Depends on / 依赖: card_pos, card_pos.ne
-/
lemma card_ne_zero {α : Type*} [FinEnum α] [Nonempty α] : card α != 0 := card_pos.ne'

/--
theorem `card_eq_one` / 定理 `card_eq_one`

English:
theorem card_eq_one
  given: (α : Type u) [FinEnum α] [Unique α]
  statement: card α = 1
  proof: card_eq_fintypeCard.trans Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩

中文:
定理 card_eq_one
  条件: (α : 类型u) [FinEnum α] [唯一 α]
  结论: card α = 1
  证明: card_eq_fintypeCard.trans Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩

Depends on / 依赖: Fintype, Fintype.card_eq_one_iff_nonempty_unique.mpr, card_eq_fintypeCard, card_eq_fintypeCard.trans, card_eq_one_iff_nonempty_unique
-/
theorem card_eq_one (α : Type u) [FinEnum α] [Unique α] : card α = 1 :=
card_eq_fintypeCard.trans Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (FinEnum α) where
  body: ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x

中文:
实例 [是空
  签名: α] : 唯一 (FinEnum α) where
  定义体: ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x

Depends on / 依赖: Equiv.equivOfIsEmpty, equivOfIsEmpty
-/
instance [IsEmpty α] : Unique (FinEnum α) where
  default := ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x

/-- An empty type has a trivial enumeration. Not registered as an instance, to make sure that there
aren't two definitionally differing instances around. -/
@[instance_reducible]
/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: [IsEmpty α]
  body: default

中文:
定义 ofIsEmpty
  签名: [是空 α]
  定义体: default
-/
def ofIsEmpty [IsEmpty α] : FinEnum α := default

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (FinEnum α) where
  body: ⟨1, Equiv.ofUnique α (Fin 1)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_one α
    · subsingleton

中文:
实例 [唯一
  签名: α] : 唯一 (FinEnum α) where
  定义体: ⟨1, Equiv.ofUnique α (Fin 1)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_one α
    · subsingleton

Depends on / 依赖: Equiv.ofUnique, ofUnique
-/
instance [Unique α] : Unique (FinEnum α) where
  default := ⟨1, Equiv.ofUnique α (Fin 1)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
exact congrArg (α ≃ Fin ·) card_eq_one α
    · subsingleton

/-- A type with unique inhabitant has a trivial enumeration. Not registered as an instance, to make
sure that there aren't two definitionally differing instances around. -/
@[instance_reducible]
/--
Definition of `ofUnique` / `ofUnique` 的定义

English:
definition ofUnique
  signature: [Unique α]
  body: default

中文:
定义 ofUnique
  签名: [唯一 α]
  定义体: default
-/
def ofUnique [Unique α] : FinEnum α := default

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum UInt8
  body: 2 ^ 8
  equiv := ⟨UInt8.toFin, UInt8.ofFin, by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum U整数8
  定义体: 2 ^ 8
  equiv := ⟨UInt8.toFin, UInt8.ofFin, by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum UInt8 where
  card := 2 ^ 8
  equiv := ⟨UInt8.toFin, UInt8.ofFin, by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum UInt16
  body: 2 ^ 16
  equiv := ⟨UInt16.toFin, UInt16.ofFin, by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum U整数16
  定义体: 2 ^ 16
  equiv := ⟨UInt16.toFin, UInt16.ofFin, by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum UInt16 where
  card := 2 ^ 16
  equiv := ⟨UInt16.toFin, UInt16.ofFin, by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum UInt32
  body: 2 ^ 32
  equiv := ⟨UInt32.toFin, UInt32.ofFin, by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum U整数32
  定义体: 2 ^ 32
  equiv := ⟨UInt32.toFin, UInt32.ofFin, by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum UInt32 where
  card := 2 ^ 32
  equiv := ⟨UInt32.toFin, UInt32.ofFin, by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum UInt64
  body: 2 ^ 64
  equiv := ⟨UInt64.toFin, UInt64.ofFin, by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum U整数64
  定义体: 2 ^ 64
  equiv := ⟨UInt64.toFin, UInt64.ofFin, by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum UInt64 where
  card := 2 ^ 64
  equiv := ⟨UInt64.toFin, UInt64.ofFin, by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum Int8
  body: 2 ^ 8
  equiv := ⟨BitVec.toFin ∘ Int8.toBitVec, Int8.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum 整数8
  定义体: 2 ^ 8
  equiv := ⟨BitVec.toFin ∘ Int8.toBitVec, Int8.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum Int8 where
  card := 2 ^ 8
  equiv := ⟨BitVec.toFin ∘ Int8.toBitVec, Int8.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum Int16
  body: 2 ^ 16
  equiv := ⟨BitVec.toFin ∘ Int16.toBitVec, Int16.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum 整数16
  定义体: 2 ^ 16
  equiv := ⟨BitVec.toFin ∘ Int16.toBitVec, Int16.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum Int16 where
  card := 2 ^ 16
  equiv := ⟨BitVec.toFin ∘ Int16.toBitVec, Int16.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum Int32
  body: 2 ^ 32
  equiv := ⟨BitVec.toFin ∘ Int32.toBitVec, Int32.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum 整数32
  定义体: 2 ^ 32
  equiv := ⟨BitVec.toFin ∘ Int32.toBitVec, Int32.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum Int32 where
  card := 2 ^ 32
  equiv := ⟨BitVec.toFin ∘ Int32.toBitVec, Int32.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FinEnum Int64
  body: 2 ^ 64
  equiv := ⟨BitVec.toFin ∘ Int64.toBitVec, Int64.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

中文:
实例 :
  签名: FinEnum 整数64
  定义体: 2 ^ 64
  equiv := ⟨BitVec.toFin ∘ Int64.toBitVec, Int64.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩
-/
instance : FinEnum Int64 where
  card := 2 ^ 64
  equiv := ⟨BitVec.toFin ∘ Int64.toBitVec, Int64.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

instance (n : Nat) : FinEnum (BitVec n) where
  card := 2 ^ n
  equiv := ⟨BitVec.toFin, BitVec.ofFin, by intro x; simp, by intro x; simp⟩

/--
lemma `card_UInt8` / 引理 `card_UInt8`

English:
lemma card_UInt8
  statement: card UInt8 = 2 ^ 8
  proof: rfl

中文:
引理 card_U整数8
  结论: card U整数8 = 2 ^ 8
  证明: rfl
-/
@[simp, grind =] lemma card_UInt8 : card UInt8 = 2 ^ 8 := rfl
/--
lemma `card_UInt16` / 引理 `card_UInt16`

English:
lemma card_UInt16
  statement: card UInt16 = 2 ^ 16
  proof: rfl

中文:
引理 card_U整数16
  结论: card U整数16 = 2 ^ 16
  证明: rfl
-/
@[simp, grind =] lemma card_UInt16 : card UInt16 = 2 ^ 16 := rfl
/--
lemma `card_UInt32` / 引理 `card_UInt32`

English:
lemma card_UInt32
  statement: card UInt32 = 2 ^ 32
  proof: rfl

中文:
引理 card_U整数32
  结论: card U整数32 = 2 ^ 32
  证明: rfl
-/
@[simp, grind =] lemma card_UInt32 : card UInt32 = 2 ^ 32 := rfl
/--
lemma `card_UInt64` / 引理 `card_UInt64`

English:
lemma card_UInt64
  statement: card UInt64 = 2 ^ 64
  proof: rfl

中文:
引理 card_U整数64
  结论: card U整数64 = 2 ^ 64
  证明: rfl
-/
@[simp, grind =] lemma card_UInt64 : card UInt64 = 2 ^ 64 := rfl
/--
lemma `card_Int8` / 引理 `card_Int8`

English:
lemma card_Int8
  statement: card Int8 = 2 ^ 8
  proof: rfl

中文:
引理 card_整数8
  结论: card 整数8 = 2 ^ 8
  证明: rfl
-/
@[simp, grind =] lemma card_Int8 : card Int8 = 2 ^ 8 := rfl
/--
lemma `card_Int16` / 引理 `card_Int16`

English:
lemma card_Int16
  statement: card Int16 = 2 ^ 16
  proof: rfl

中文:
引理 card_整数16
  结论: card 整数16 = 2 ^ 16
  证明: rfl
-/
@[simp, grind =] lemma card_Int16 : card Int16 = 2 ^ 16 := rfl
/--
lemma `card_Int32` / 引理 `card_Int32`

English:
lemma card_Int32
  statement: card Int32 = 2 ^ 32
  proof: rfl

中文:
引理 card_整数32
  结论: card 整数32 = 2 ^ 32
  证明: rfl
-/
@[simp, grind =] lemma card_Int32 : card Int32 = 2 ^ 32 := rfl
/--
lemma `card_Int64` / 引理 `card_Int64`

English:
lemma card_Int64
  statement: card Int64 = 2 ^ 64
  proof: rfl

中文:
引理 card_整数64
  结论: card 整数64 = 2 ^ 64
  证明: rfl
-/
@[simp, grind =] lemma card_Int64 : card Int64 = 2 ^ 64 := rfl
/--
lemma `card_bitVec` / 引理 `card_bitVec`

English:
lemma card_bitVec
  given: (n : Nat)
  statement: card (BitVec n) = 2 ^ n
  proof: rfl

中文:
引理 card_bitVec
  条件: (n : 自然数)
  结论: card (BitVec n) = 2 ^ n
  证明: rfl
-/
@[simp, grind =] lemma card_bitVec (n : Nat) : card (BitVec n) = 2 ^ n := rfl

end FinEnum

namespace List
variable {α : Type*} [FinEnum α] {β : α -> Type*} [forall a, FinEnum (β a)]
open FinEnum

/--
theorem `mem_pi_toList` / 定理 `mem_pi_toList`

English:
theorem mem_pi_toList
  statement: (xs : List α)
  proof: (mem_pi _ _).mpr fun _ _ => mem_toList _

中文:
定理 mem_pi_toList
  结论: (xs : 列表 α)
  证明: (mem_pi _ _).mpr fun _ _ => mem_toList _

Depends on / 依赖: mem_pi, mem_toList
-/
theorem mem_pi_toList (xs : List α)
    (f : forall a, a in xs -> β a) : f in pi xs fun x => toList (β x) :=
  (mem_pi _ _).mpr fun _ _ => mem_toList _

/--
Definition of `Pi.enum` / `Pi.enum` 的定义

English:
definition Pi.enum
  signature: (β : α -> Type*) [forall a, FinEnum (β a)]
  body: (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))

中文:
定义 依赖函数类型.enum
  签名: (β : α -> 类型) [对任意 a, FinEnum (β a)]
  定义体: (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))

Depends on / 依赖: mem_toList, toList
-/
def Pi.enum (β : α -> Type*) [forall a, FinEnum (β a)] : List (forall a, β a) :=
  (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))

/--
theorem `Pi.mem_enum` / 定理 `Pi.mem_enum`

English:
theorem Pi.mem_enum
  given: (f : forall a, β a)
  proof: by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩

中文:
定理 依赖函数类型.mem_enum
  条件: (f : 对任意 a, β a)
  证明: by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩

Depends on / 依赖: Pi.enum, mem_pi_toList
-/
theorem Pi.mem_enum (f : forall a, β a) :
    f in Pi.enum β := by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩

/--
Instance `Pi.finEnum` / 实例 `Pi.finEnum`

English:
instance Pi.finEnum
  signature: : FinEnum (forall a, β a)
  body: ofList (Pi.enum _) fun _ => Pi.mem_enum _

中文:
实例 依赖函数类型.finEnum
  签名: : FinEnum (对任意 a, β a)
  定义体: ofList (Pi.enum _) fun _ => Pi.mem_enum _

Depends on / 依赖: Pi.enum, Pi.mem_enum, mem_enum, ofList
-/
instance Pi.finEnum : FinEnum (forall a, β a) :=
  ofList (Pi.enum _) fun _ => Pi.mem_enum _

/--
Instance `pfunFinEnum` / 实例 `pfunFinEnum`

English:
instance pfunFinEnum
  signature: (p : Prop) [Decidable p] (α : p -> Type) [forall hp, FinEnum (α hp)]
  body: if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by simp [funext_iff, hp])

中文:
实例 pfunFinEnum
  签名: (p : 命题) [可判定 p] (α : p -> 类型) [对任意 hp, FinEnum (α hp)]
  定义体: if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by simp [funext_iff, hp])

Depends on / 依赖: funext_iff, ofList, toList
-/
instance pfunFinEnum (p : Prop) [Decidable p] (α : p -> Type) [forall hp, FinEnum (α hp)] :
    FinEnum (forall hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by simp [funext_iff, hp])

end List
