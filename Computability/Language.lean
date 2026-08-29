/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Martin Dvorak, Rudy Peterson
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Set.Lattice
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Lattice.Image

/-!
# Languages

This file contains the definition and operations on formal languages over an alphabet.
Note that "strings" are implemented as lists over the alphabet.

Union and concatenation define a [Kleene algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
over the languages.

In addition to that, we define a reversal of a language and prove that it behaves well
with respect to other language operations.

## Notation

* `l + m`: union of languages `l` and `m`
* `l - m`: difference of languages `l` and `m`
* `l * m`: language of strings `x ++ y` such that `x ∈ l` and `y ∈ m`
* `l ^ n`: language of strings consisting of `n` members of `l` concatenated together
* `1`: language consisting of only the empty string. This is because it is the unit of the `*`
  operator.
* `l∗`: Kleene star – language of strings consisting of arbitrarily many members of `l`
  concatenated together. Note that this notation uses the Unicode asterisk operator `∗`, as opposed
  to the more common ASCII asterisk `*`.
* `lᶜ`: complement, language of strings `x` such that `x ∉ l`
* `l ⊓ m`: intersection of languages `l` and `m`

## Main definitions

* `Language α`: a set of strings over the alphabet `α`
* `l.map f`: transform a language `l` over `α` into a language over `β`
  by translating through `f : α → β`

## Main theorems

* `Language.self_eq_mul_add_iff`: Arden's lemma – if a language `l` satisfies the equation
  `l = m * l + n`, and `m` doesn't contain the empty string,
  then `l` is the language `m∗ * n`

-/

@[expose] public section


open List Set Computability

universe v

variable {α β γ : Type*}

/--
Definition of `Language` / `Language` 的定义

English:
definition Language
  signature: (α)
  body: Set (List α)
deriving CompleteAtomicBooleanAlgebra

中文:
定义 Language
  签名: (α)
  定义体: Set (List α)
deriving CompleteAtomicBooleanAlgebra
-/
def Language (α) :=
  Set (List α)
deriving CompleteAtomicBooleanAlgebra

namespace Language

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (List α) (Language α)
  body: ⟨Set.Mem⟩

中文:
实例 :
  签名: Membership (列表 α) (Language α)
  定义体: ⟨Set.Mem⟩

Depends on / 依赖: Set.Mem
-/
instance : Membership (List α) (Language α) := ⟨Set.Mem⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton (List α) (Language α)
  body: ⟨Set.singleton⟩

中文:
实例 :
  签名: 单例 (列表 α) (Language α)
  定义体: ⟨Set.singleton⟩

Depends on / 依赖: Set.singleton, singleton
-/
instance : Singleton (List α) (Language α) := ⟨Set.singleton⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert (List α) (Language α)
  body: ⟨Set.insert⟩

中文:
实例 :
  签名: Insert (列表 α) (Language α)
  定义体: ⟨Set.insert⟩

Depends on / 依赖: Set.insert, insert
-/
instance : Insert (List α) (Language α) := ⟨Set.insert⟩

variable {l m : Language α} {a b x : List α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Language α)
  body: ⟨(∅ : Set _)⟩

中文:
实例 :
  签名: 零 (Language α)
  定义体: ⟨(∅ : Set _)⟩
-/
instance : Zero (Language α) :=
  ⟨(∅ : Set _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Language α)
  body: ⟨{[]}⟩

中文:
实例 :
  签名: 幺 (Language α)
  定义体: ⟨{[]}⟩
-/
instance : One (Language α) :=
  ⟨{[]}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Language α)
  body: ⟨(∅ : Set _)⟩

中文:
实例 :
  签名: 可居 (Language α)
  定义体: ⟨(∅ : Set _)⟩
-/
instance : Inhabited (Language α) := ⟨(∅ : Set _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Language α)
  body: ⟨((· union ·) : Set (List α) -> Set (List α) -> Set (List α))⟩

中文:
实例 :
  签名: 加法 (Language α)
  定义体: ⟨((· union ·) : Set (List α) -> Set (List α) -> Set (List α))⟩
-/
instance : Add (Language α) :=
  ⟨((· union ·) : Set (List α) -> Set (List α) -> Set (List α))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Language α)
  body: SDiff.sdiff

中文:
实例 :
  签名: 减法 (Language α)
  定义体: SDiff.sdiff

Depends on / 依赖: SDiff.sdiff
-/
instance : Sub (Language α) where
  sub := SDiff.sdiff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Language α)
  body: ⟨image2 (· ++ ·)⟩

中文:
实例 :
  签名: 乘法 (Language α)
  定义体: ⟨image2 (· ++ ·)⟩

Depends on / 依赖: image2
-/
instance : Mul (Language α) :=
  ⟨image2 (· ++ ·)⟩

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (0 : Language α) = (∅ : Set _)
  proof: rfl

中文:
定理 zero_def
  结论: (0 : Language α) = (∅ : 集合 _)
  证明: rfl
-/
theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : Language α) = ({[]} : Set (List α))
  proof: rfl

中文:
定理 one_def
  结论: (1 : Language α) = ({[]} : 集合 (列表 α))
  证明: rfl
-/
theorem one_def : (1 : Language α) = ({[]} : Set (List α)) :=
  rfl

/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: (l m : Language α)
  statement: l + m = (l union m : Set (List α))
  proof: rfl

中文:
定理 add_def
  条件: (l m : Language α)
  结论: l + m = (l union m : 集合 (列表 α))
  证明: rfl
-/
theorem add_def (l m : Language α) : l + m = (l union m : Set (List α)) :=
  rfl

/--
theorem `sub_def` / 定理 `sub_def`

English:
theorem sub_def
  given: (l m : Language α)
  statement: l - m = (l \ m : Set (List α))
  proof: rfl

中文:
定理 sub_def
  条件: (l m : Language α)
  结论: l - m = (l \ m : 集合 (列表 α))
  证明: rfl
-/
theorem sub_def (l m : Language α) : l - m = (l \ m : Set (List α)) :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (l m : Language α)
  statement: l * m = image2 (· ++ ·) l m
  proof: rfl

中文:
定理 mul_def
  条件: (l m : Language α)
  结论: l * m = image2 (· ++ ·) l m
  证明: rfl
-/
theorem mul_def (l m : Language α) : l * m = image2 (· ++ ·) l m :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: KStar (Language α)
  body: ⟨fun l => {x | exists L : List (List α), x = L.flatten ∧ forall y in L, y in l}⟩

中文:
实例 :
  签名: KStar (Language α)
  定义体: ⟨fun l => {x | exists L : List (List α), x = L.flatten ∧ forall y in L, y in l}⟩

Depends on / 依赖: L.flatten, flatten
-/
instance : KStar (Language α) := ⟨fun l => {x | exists L : List (List α), x = L.flatten ∧ forall y in L, y in l}⟩

/--
lemma `kstar_def` / 引理 `kstar_def`

English:
lemma kstar_def
  given: (l : Language α)
  statement: l∗ = {x | exists L : List (List α), x = L.flatten ∧ forall y in L, y in l}
  proof: rfl

@[ext]

中文:
引理 kstar_def
  条件: (l : Language α)
  结论: l∗ = {x | 存在 L : 列表 (列表 α), x = L.flatten ∧ 对任意 y in L, y in l}
  证明: rfl

@[ext]
-/
lemma kstar_def (l : Language α) : l∗ = {x | exists L : List (List α), x = L.flatten ∧ forall y in L, y in l} :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {l m : Language α} (h : forall (x : List α), x in l ↔ x in m)
  statement: l = m
  proof: Set.ext h

@[simp]

中文:
定理 ext
  条件: {l m : Language α} (h : 对任意 (x : 列表 α), x in l ↔ x in m)
  结论: l = m
  证明: Set.ext h

@[simp]

Depends on / 依赖: Set.ext
-/
theorem ext {l m : Language α} (h : forall (x : List α), x in l ↔ x in m) : l = m :=
  Set.ext h

@[simp]
/--
theorem `notMem_zero` / 定理 `notMem_zero`

English:
theorem notMem_zero
  given: (x : List α)
  statement: x ∉ (0 : Language α)
  proof: id

@[simp]

中文:
定理 notMem_zero
  条件: (x : 列表 α)
  结论: x ∉ (0 : Language α)
  证明: id

@[simp]
-/
theorem notMem_zero (x : List α) : x ∉ (0 : Language α) :=
  id

@[simp]
/--
theorem `mem_one` / 定理 `mem_one`

English:
theorem mem_one
  given: (x : List α)
  statement: x in (1 : Language α) ↔ x = []
  proof: by rfl

中文:
定理 mem_one
  条件: (x : 列表 α)
  结论: x in (1 : Language α) ↔ x = []
  证明: by rfl
-/
theorem mem_one (x : List α) : x in (1 : Language α) ↔ x = [] := by rfl

/--
theorem `nil_mem_one` / 定理 `nil_mem_one`

English:
theorem nil_mem_one
  statement: [] in (1 : Language α)
  proof: Set.mem_singleton _

中文:
定理 nil_mem_one
  结论: [] in (1 : Language α)
  证明: Set.mem_singleton _

Depends on / 依赖: Set.mem_singleton, mem_singleton
-/
theorem nil_mem_one : [] in (1 : Language α) :=
  Set.mem_singleton _

/--
theorem `mem_add` / 定理 `mem_add`

English:
theorem mem_add
  given: (l m : Language α) (x : List α)
  statement: x in l + m ↔ x in l ∨ x in m
  proof: Iff.rfl

中文:
定理 mem_add
  条件: (l m : Language α) (x : 列表 α)
  结论: x in l + m ↔ x in l ∨ x in m
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_add (l m : Language α) (x : List α) : x in l + m ↔ x in l ∨ x in m :=
  Iff.rfl

/--
theorem `mem_sub` / 定理 `mem_sub`

English:
theorem mem_sub
  given: (l m : Language α) (x : List α)
  statement: x in l - m ↔ x in l ∧ x ∉ m
  proof: Iff.rfl

中文:
定理 mem_sub
  条件: (l m : Language α) (x : 列表 α)
  结论: x in l - m ↔ x in l ∧ x ∉ m
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_sub (l m : Language α) (x : List α) : x in l - m ↔ x in l ∧ x ∉ m :=
  Iff.rfl

/--
theorem `mem_mul` / 定理 `mem_mul`

English:
theorem mem_mul
  statement: x in l * m ↔ exists a in l, exists b in m, a ++ b = x
  proof: mem_image2

中文:
定理 mem_mul
  结论: x in l * m ↔ 存在 a in l, 存在 b in m, a ++ b = x
  证明: mem_image2

Depends on / 依赖: mem_image2
-/
theorem mem_mul : x in l * m ↔ exists a in l, exists b in m, a ++ b = x :=
  mem_image2

/--
theorem `append_mem_mul` / 定理 `append_mem_mul`

English:
theorem append_mem_mul
  statement: a in l -> b in m -> a ++ b in l * m
  proof: mem_image2_of_mem

中文:
定理 append_mem_mul
  结论: a in l -> b in m -> a ++ b in l * m
  证明: mem_image2_of_mem

Depends on / 依赖: mem_image2_of_mem
-/
theorem append_mem_mul : a in l -> b in m -> a ++ b in l * m :=
  mem_image2_of_mem

/--
theorem `mem_kstar` / 定理 `mem_kstar`

English:
theorem mem_kstar
  statement: x in l∗ ↔ exists L : List (List α), x = L.flatten ∧ forall y in L, y in l
  proof: Iff.rfl

中文:
定理 mem_kstar
  结论: x in l∗ ↔ 存在 L : 列表 (列表 α), x = L.flatten ∧ 对任意 y in L, y in l
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_kstar : x in l∗ ↔ exists L : List (List α), x = L.flatten ∧ forall y in L, y in l :=
  Iff.rfl

/--
theorem `join_mem_kstar` / 定理 `join_mem_kstar`

English:
theorem join_mem_kstar
  given: {L : List (List α)} (h : forall y in L, y in l)
  statement: L.flatten in l∗
  proof: ⟨L, rfl, h⟩

中文:
定理 join_mem_kstar
  条件: {L : 列表 (列表 α)} (h : 对任意 y in L, y in l)
  结论: L.flatten in l∗
  证明: ⟨L, rfl, h⟩
-/
theorem join_mem_kstar {L : List (List α)} (h : forall y in L, y in l) : L.flatten in l∗ :=
  ⟨L, rfl, h⟩

/--
theorem `nil_mem_kstar` / 定理 `nil_mem_kstar`

English:
theorem nil_mem_kstar
  given: (l : Language α)
  statement: [] in l∗
  proof: ⟨[], rfl, fun _ h => by contradiction⟩

中文:
定理 nil_mem_kstar
  条件: (l : Language α)
  结论: [] in l∗
  证明: ⟨[], rfl, fun _ h => by contradiction⟩
-/
theorem nil_mem_kstar (l : Language α) : [] in l∗ :=
  ⟨[], rfl, fun _ h => by contradiction⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderedSub (Language α)
  body: sdiff_le_iff'

中文:
实例 :
  签名: OrderedSub (Language α)
  定义体: sdiff_le_iff'

Depends on / 依赖: sdiff_le_iff
-/
instance : OrderedSub (Language α) where
  tsub_le_iff_right _ _ _ := sdiff_le_iff'

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring (Language α) where
  body: union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n

中文:
实例 instSemiring
  签名: : 半环 (Language α) where
  定义体: union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n

Depends on / 依赖: union_assoc
-/
instance instSemiring : Semiring (Language α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  mul_assoc _ _ _ := image2_assoc append_assoc
  zero_mul _ := image2_empty_left
  mul_zero _ := image2_empty_right
  one_mul l := by simp [mul_def, one_def]
  mul_one l := by simp [mul_def, one_def]
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp [add_def, zero_def]
  left_distrib _ _ _ := image2_union_right
  right_distrib _ _ _ := image2_union_left
  nsmul := nsmulRec

@[simp]
/--
theorem `add_self` / 定理 `add_self`

English:
theorem add_self
  given: (l : Language α)
  statement: l + l = l
  proof: sup_idem _

中文:
定理 add_self
  条件: (l : Language α)
  结论: l + l = l
  证明: sup_idem _

Depends on / 依赖: sup_idem
-/
theorem add_self (l : Language α) : l + l = l :=
  sup_idem _

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
map_mul' _ _ := image_image2_distrib fun _ _ => map_append

中文:
定义 map
  签名: (f : α -> β)
  定义体: image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
map_mul' _ _ := image_image2_distrib fun _ _ => map_append

Depends on / 依赖: List.map
-/
def map (f : α -> β) : Language α ->+* Language β where
  toFun := image (List.map f)
  map_zero' := image_empty _
  map_one' := image_singleton
  map_add' := image_union _
map_mul' _ _ := image_image2_distrib fun _ _ => map_append

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (l : Language α)
  statement: map id l = l
  proof: by simp [map]

中文:
定理 map_id
  条件: (l : Language α)
  结论: map id l = l
  证明: by simp [map]
-/
theorem map_id (l : Language α) : map id l = l := by simp [map]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> γ) (f : α -> β) (l : Language α)
  statement: map g (map f l) = map (g ∘ f) l
  proof: by
  simp [map, image_image]

中文:
定理 map_map
  条件: (g : β -> γ) (f : α -> β) (l : Language α)
  结论: map g (map f l) = map (g ∘ f) l
  证明: by
  simp [map, image_image]

Depends on / 依赖: image_image
-/
theorem map_map (g : β -> γ) (f : α -> β) (l : Language α) : map g (map f l) = map (g ∘ f) l := by
  simp [map, image_image]

/--
lemma `mem_kstar_iff_exists_nonempty` / 引理 `mem_kstar_iff_exists_nonempty`

English:
lemma mem_kstar_iff_exists_nonempty
  given: {x : List α}
  proof: by
  constructor
  · rintro ⟨S, rfl, h⟩
    refine ⟨S.filter fun l => !List.isEmpty l,
      by simp [List.flatten_filter_not_isEmpty], fun y hy => ?_⟩
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false_iff, ne_eq] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩

中文:
引理 mem_kstar_iff_存在_nonempty
  条件: {x : 列表 α}
  证明: by
  constructor
  · rintro ⟨S, rfl, h⟩
    refine ⟨S.filter fun l => !List.isEmpty l,
      by simp [List.flatten_filter_not_isEmpty], fun y hy => ?_⟩
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false_iff, ne_eq] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩

Depends on / 依赖: Bool.not_eq_eq_eq_not, Bool.not_true, List.flatten_filter_not_isEmpty, List.isEmpty, S.filter, filter, flatten_filter_not_isEmpty, isEmpty, isEmpty_eq_false_iff, mem_filter, ne_eq, not_eq_eq_eq_not, not_true
-/
lemma mem_kstar_iff_exists_nonempty {x : List α} :
    x in l∗ ↔ exists S : List (List α), x = S.flatten ∧ forall y in S, y in l ∧ y != [] := by
  constructor
  · rintro ⟨S, rfl, h⟩
    refine ⟨S.filter fun l => !List.isEmpty l,
      by simp [List.flatten_filter_not_isEmpty], fun y hy => ?_⟩
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, isEmpty_eq_false_iff, ne_eq] at hy
    exact ⟨h y hy.1, hy.2⟩
  · rintro ⟨S, hx, h⟩
    exact ⟨S, hx, fun y hy => (h y hy).1⟩

/--
theorem `kstar_def_nonempty` / 定理 `kstar_def_nonempty`

English:
theorem kstar_def_nonempty
  given: (l : Language α)
  proof: by
  ext x; apply mem_kstar_iff_exists_nonempty

中文:
定理 kstar_def_nonempty
  条件: (l : Language α)
  证明: by
  ext x; apply mem_kstar_iff_exists_nonempty

Depends on / 依赖: mem_kstar_iff_exists_nonempty
-/
theorem kstar_def_nonempty (l : Language α) :
    l∗ = { x | exists S : List (List α), x = S.flatten ∧ forall y in S, y in l ∧ y != [] } := by
  ext x; apply mem_kstar_iff_exists_nonempty

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: (l m : Language α)
  statement: l <= m ↔ l + m = m
  proof: sup_eq_right.symm

中文:
定理 le_iff
  条件: (l m : Language α)
  结论: l <= m ↔ l + m = m
  证明: sup_eq_right.symm

Depends on / 依赖: sup_eq_right, sup_eq_right.symm
-/
theorem le_iff (l m : Language α) : l <= m ↔ l + m = m :=
  sup_eq_right.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono (Language α)
  body: image2_subset_left

中文:
实例 :
  签名: MulLeftMono (Language α)
  定义体: image2_subset_left

Depends on / 依赖: image2_subset_left
-/
instance : MulLeftMono (Language α) where
  elim _ _ _ := image2_subset_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono (Language α)
  body: image2_subset_right

中文:
实例 :
  签名: MulRightMono (Language α)
  定义体: image2_subset_right

Depends on / 依赖: image2_subset_right
-/
instance : MulRightMono (Language α) where
  elim _ _ _ := image2_subset_right

/--
theorem `mem_iSup` / 定理 `mem_iSup`

English:
theorem mem_iSup
  given: {ι : Sort v} {l : ι -> Language α} {x : List α}
  statement: (x in ⨆ i, l i) ↔ exists i, x in l i
  proof: mem_iUnion

中文:
定理 mem_iSup
  条件: {ι : 类型层 v} {l : ι -> Language α} {x : 列表 α}
  结论: (x in ⨆ i, l i) ↔ 存在 i, x in l i
  证明: mem_iUnion

Depends on / 依赖: mem_iUnion
-/
theorem mem_iSup {ι : Sort v} {l : ι -> Language α} {x : List α} : (x in ⨆ i, l i) ↔ exists i, x in l i :=
  mem_iUnion

/--
theorem `iSup_mul` / 定理 `iSup_mul`

English:
theorem iSup_mul
  given: {ι : Sort v} (l : ι -> Language α) (m : Language α)
  proof: image2_iUnion_left _ _ _

中文:
定理 iSup_mul
  条件: {ι : 类型层 v} (l : ι -> Language α) (m : Language α)
  证明: image2_iUnion_left _ _ _

Depends on / 依赖: image2_iUnion_left
-/
theorem iSup_mul {ι : Sort v} (l : ι -> Language α) (m : Language α) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  image2_iUnion_left _ _ _

/--
theorem `mul_iSup` / 定理 `mul_iSup`

English:
theorem mul_iSup
  given: {ι : Sort v} (l : ι -> Language α) (m : Language α)
  proof: image2_iUnion_right _ _ _

中文:
定理 mul_iSup
  条件: {ι : 类型层 v} (l : ι -> Language α) (m : Language α)
  证明: image2_iUnion_right _ _ _

Depends on / 依赖: image2_iUnion_right
-/
theorem mul_iSup {ι : Sort v} (l : ι -> Language α) (m : Language α) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  image2_iUnion_right _ _ _

/--
theorem `iSup_add` / 定理 `iSup_add`

English:
theorem iSup_add
  given: {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α)
  proof: iSup_sup

中文:
定理 iSup_add
  条件: {ι : 类型层 v} [非空 ι] (l : ι -> Language α) (m : Language α)
  证明: iSup_sup

Depends on / 依赖: iSup_sup
-/
theorem iSup_add {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) :
    (⨆ i, l i) + m = ⨆ i, l i + m :=
  iSup_sup

/--
theorem `add_iSup` / 定理 `add_iSup`

English:
theorem add_iSup
  given: {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α)
  proof: sup_iSup

中文:
定理 add_iSup
  条件: {ι : 类型层 v} [非空 ι] (l : ι -> Language α) (m : Language α)
  证明: sup_iSup

Depends on / 依赖: sup_iSup
-/
theorem add_iSup {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) :
    (m + ⨆ i, l i) = ⨆ i, m + l i :=
  sup_iSup

/--
theorem `iSup_sub` / 定理 `iSup_sub`

English:
theorem iSup_sub
  given: {ι : Sort v} (l : ι -> Language α) (m : Language α)
  proof: iUnion_sdiff _ _

中文:
定理 iSup_sub
  条件: {ι : 类型层 v} (l : ι -> Language α) (m : Language α)
  证明: iUnion_sdiff _ _

Depends on / 依赖: iUnion_sdiff
-/
theorem iSup_sub {ι : Sort v} (l : ι -> Language α) (m : Language α) :
    (⨆ i, l i) - m = ⨆ i, l i - m :=
  iUnion_sdiff _ _

/--
theorem `sub_iSup` / 定理 `sub_iSup`

English:
theorem sub_iSup
  given: {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α)
  proof: sdiff_iUnion _ _

中文:
定理 sub_iSup
  条件: {ι : 类型层 v} [非空 ι] (l : ι -> Language α) (m : Language α)
  证明: sdiff_iUnion _ _

Depends on / 依赖: sdiff_iUnion
-/
theorem sub_iSup {ι : Sort v} [Nonempty ι] (l : ι -> Language α) (m : Language α) :
    (m - ⨆ i, l i) = ⨅ i, m - l i :=
  sdiff_iUnion _ _

/--
theorem `mem_pow` / 定理 `mem_pow`

English:
theorem mem_pow
  given: {l : Language α} {x : List α} {n : Nat}
  proof: by
  induction n generalizing x with
  | zero => simp
  | succ n ihn =>
    simp only [pow_succ', mem_mul, ihn]
    constructor
    · rintro ⟨a, ha, b, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [for

中文:
定理 mem_pow
  条件: {l : Language α} {x : 列表 α} {n : 自然数}
  证明: by
  induction n generalizing x with
  | zero => simp
  | succ n ihn =>
    simp only [pow_succ', mem_mul, ihn]
    constructor
    · rintro ⟨a, ha, b, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [for

Depends on / 依赖: forall_mem_cons, generalizing, mem_mul, pow_succ
-/
theorem mem_pow {l : Language α} {x : List α} {n : Nat} :
    x in l ^ n ↔ exists S : List (List α), x = S.flatten ∧ S.length = n ∧ forall y in S, y in l := by
  induction n generalizing x with
  | zero => simp
  | succ n ihn =>
    simp only [pow_succ', mem_mul, ihn]
    constructor
    · rintro ⟨a, ha, b, ⟨S, rfl, rfl, hS⟩, rfl⟩
      exact ⟨a :: S, rfl, rfl, forall_mem_cons.2 ⟨ha, hS⟩⟩
    · rintro ⟨_ | ⟨a, S⟩, rfl, hn, hS⟩ <;> cases hn
      rw [forall_mem_cons] at hS
      exact ⟨a, hS.1, _, ⟨S, rfl, rfl, hS.2⟩, rfl⟩

/--
theorem `kstar_eq_iSup_pow` / 定理 `kstar_eq_iSup_pow`

English:
theorem kstar_eq_iSup_pow
  given: (l : Language α)
  statement: l∗ = ⨆ i : Nat, l ^ i
  proof: by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  grind

@[simp]

中文:
定理 kstar_eq_iSup_pow
  条件: (l : Language α)
  结论: l∗ = ⨆ i : 自然数, l ^ i
  证明: by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  grind

@[simp]

Depends on / 依赖: mem_iSup, mem_kstar, mem_pow
-/
theorem kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : Nat, l ^ i := by
  ext x
  simp only [mem_kstar, mem_iSup, mem_pow]
  grind

@[simp]
/--
theorem `map_kstar` / 定理 `map_kstar`

English:
theorem map_kstar
  given: (f : α -> β) (l : Language α)
  statement: map f l∗ = (map f l)∗
  proof: by
  rw [kstar_eq_iSup_pow]; rw [kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion

中文:
定理 map_kstar
  条件: (f : α -> β) (l : Language α)
  结论: map f l∗ = (map f l)∗
  证明: by
  rw [kstar_eq_iSup_pow]; rw [kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion

Depends on / 依赖: image_iUnion, kstar_eq_iSup_pow, map_pow, simp_rw
-/
theorem map_kstar (f : α -> β) (l : Language α) : map f l∗ = (map f l)∗ := by
  rw [kstar_eq_iSup_pow]; rw [kstar_eq_iSup_pow]
  simp_rw [← map_pow]
  exact image_iUnion

/--
theorem `mul_self_kstar_comm` / 定理 `mul_self_kstar_comm`

English:
theorem mul_self_kstar_comm
  given: (l : Language α)
  statement: l∗ * l = l * l∗
  proof: by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]

中文:
定理 mul_self_kstar_comm
  条件: (l : Language α)
  结论: l∗ * l = l * l∗
  证明: by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]

Depends on / 依赖: iSup_mul, kstar_eq_iSup_pow, mul_iSup, pow_succ
-/
theorem mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]
/--
theorem `one_add_self_mul_kstar_eq_kstar` / 定理 `one_add_self_mul_kstar_eq_kstar`

English:
theorem one_add_self_mul_kstar_eq_kstar
  given: (l : Language α)
  statement: 1 + l * l∗ = l∗
  proof: by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ _

@[simp]

中文:
定理 one_add_self_mul_kstar_eq_kstar
  条件: (l : Language α)
  结论: 1 + l * l∗ = l∗
  证明: by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ _

@[simp]

Depends on / 依赖: kstar_eq_iSup_pow, mul_iSup, pow_succ, pow_zero, sup_iSup_nat_succ
-/
theorem one_add_self_mul_kstar_eq_kstar (l : Language α) : 1 + l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ', ← pow_zero l]
  exact sup_iSup_nat_succ _

@[simp]
/--
theorem `one_add_kstar_mul_self_eq_kstar` / 定理 `one_add_kstar_mul_self_eq_kstar`

English:
theorem one_add_kstar_mul_self_eq_kstar
  given: (l : Language α)
  statement: 1 + l∗ * l = l∗
  proof: by
  rw [mul_self_kstar_comm]; rw [one_add_self_mul_kstar_eq_kstar]

中文:
定理 one_add_kstar_mul_self_eq_kstar
  条件: (l : Language α)
  结论: 1 + l∗ * l = l∗
  证明: by
  rw [mul_self_kstar_comm]; rw [one_add_self_mul_kstar_eq_kstar]

Depends on / 依赖: mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar
-/
theorem one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ := by
  rw [mul_self_kstar_comm]; rw [one_add_self_mul_kstar_eq_kstar]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: KleeneAlgebra (Language α)
  body: inferInstance
  one_le_kstar a _ hl := ⟨[], hl, by simp⟩
  mul_kstar_le_kstar a := (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_kstar a := (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_self l m h := by
    rw [kstar_eq_iSup_pow]; rw [iSup_mul]

中文:
实例 :
  签名: Kleene代数 (Language α)
  定义体: inferInstance
  one_le_kstar a _ hl := ⟨[], hl, by simp⟩
  mul_kstar_le_kstar a := (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_kstar a := (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_self l m h := by
    rw [kstar_eq_iSup_pow]; rw [iSup_mul]
-/
instance : KleeneAlgebra (Language α) where
  __ : OrderBot (Language α) := inferInstance
  one_le_kstar a _ hl := ⟨[], hl, by simp⟩
  mul_kstar_le_kstar a := (one_add_self_mul_kstar_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_kstar a := (one_add_kstar_mul_self_eq_kstar a).le.trans' le_sup_right
  kstar_mul_le_self l m h := by
    rw [kstar_eq_iSup_pow]; rw [iSup_mul]
    refine iSup_le fun n => ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, mul_assoc, h, ih]
  mul_kstar_le_self l m h := by
    rw [kstar_eq_iSup_pow]; rw [mul_iSup]
    refine iSup_le fun n => ?_
    induction n with
    | zero => simp
    | succ n ih => grw [pow_succ, ← mul_assoc m (l ^ n) l, ih, h]

/--
theorem `self_eq_mul_add_iff` / 定理 `self_eq_mul_add_iff`

English:
theorem self_eq_mul_add_iff
  given: {l m n : Language α} (hm : [] ∉ m)
  statement: l = m * l + n ↔ l = m∗ * n where
  proof: by
    apply le_antisymm
    · intro x hx
      induction hlen : x.length using Nat.strong_induction_on generalizing x with | _ _ ih
      subst hlen
      rw [h] at hx
      obtain hx | hx := hx
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hx
        rw [length_append] at ih
have hal : 0 < a.le

中文:
定理 self_eq_mul_add_iff
  条件: {l m n : Language α} (hm : [] ∉ m)
  结论: l = m * l + n ↔ l = m∗ * n where
  证明: by
    apply le_antisymm
    · intro x hx
      induction hlen : x.length using Nat.strong_induction_on generalizing x with | _ _ ih
      subst hlen
      rw [h] at hx
      obtain hx | hx := hx
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hx
        rw [length_append] at ih
have hal : 0 < a.le

Depends on / 依赖: Nat.lt_add_left_iff_pos.mpr, Nat.strong_induction_on, a.length, b.length, generalizing, le_antisymm, length, length_append, length_pos_iff, length_pos_iff.mpr, lt_add_left_iff_pos, mem_mul, mem_mul.mp, mul_assoc, ne_of_mem_of_not_mem, nil_mem_ks, one_add_mul, one_add_self_mul_kstar_eq_kstar, specialize, strong_induction_on
-/
theorem self_eq_mul_add_iff {l m n : Language α} (hm : [] ∉ m) : l = m * l + n ↔ l = m∗ * n where
  mp h := by
    apply le_antisymm
    · intro x hx
      induction hlen : x.length using Nat.strong_induction_on generalizing x with | _ _ ih
      subst hlen
      rw [h] at hx
      obtain hx | hx := hx
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hx
        rw [length_append] at ih
have hal : 0 < a.length := length_pos_iff.mpr ne_of_mem_of_not_mem ha hm
        specialize ih b.length (Nat.lt_add_left_iff_pos.mpr hal) hb rfl
        rw [← one_add_self_mul_kstar_eq_kstar]; rw [one_add_mul]; rw [mul_assoc]
        right
        exact ⟨_, ha, _, ih, rfl⟩
      · exact ⟨[], nil_mem_kstar _, _, ⟨hx, nil_append _⟩⟩
    · rw [kstar_eq_iSup_pow, iSup_mul, iSup_le_iff]
      intro i
      induction i with rw [h]
      | zero =>
        rw [pow_zero]; rw [one_mul]; rw [add_comm]
        exact le_self_add
      | succ _ ih =>
        grw [add_comm, pow_add, pow_one, mul_assoc, ih]
        exact le_self_add
  mpr h := by rw [h, add_comm, ← mul_assoc, ← one_add_mul, one_add_self_mul_kstar_eq_kstar]

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (l : Language α)
  body: { w : List α | w.reverse in l }

@[simp]

中文:
定义 reverse
  签名: (l : Language α)
  定义体: { w : List α | w.reverse in l }

@[simp]

Depends on / 依赖: reverse, w.reverse
-/
def reverse (l : Language α) : Language α := { w : List α | w.reverse in l }

@[simp]
/--
lemma `mem_reverse` / 引理 `mem_reverse`

English:
lemma mem_reverse
  statement: a in l.reverse ↔ a.reverse in l
  proof: Iff.rfl

中文:
引理 mem_reverse
  结论: a in l.reverse ↔ a.reverse in l
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_reverse : a in l.reverse ↔ a.reverse in l := Iff.rfl

/--
lemma `reverse_mem_reverse` / 引理 `reverse_mem_reverse`

English:
lemma reverse_mem_reverse
  statement: a.reverse in l.reverse ↔ a in l
  proof: by
  rw [mem_reverse]; rw [List.reverse_reverse]

中文:
引理 reverse_mem_reverse
  结论: a.reverse in l.reverse ↔ a in l
  证明: by
  rw [mem_reverse]; rw [List.reverse_reverse]

Depends on / 依赖: List.reverse_reverse, mem_reverse, reverse_reverse
-/
lemma reverse_mem_reverse : a.reverse in l.reverse ↔ a in l := by
  rw [mem_reverse]; rw [List.reverse_reverse]

/--
lemma `reverse_eq_image` / 引理 `reverse_eq_image`

English:
lemma reverse_eq_image
  given: (l : Language α)
  statement: l.reverse = List.reverse '' l
  proof: ((List.reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

@[simp]

中文:
引理 reverse_eq_image
  条件: (l : Language α)
  结论: l.reverse = 列表.reverse '' l
  证明: ((List.reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

@[simp]

Depends on / 依赖: List.reverse_involutive.toPerm, image_eq_preimage_symm, reverse_involutive, toPerm
-/
lemma reverse_eq_image (l : Language α) : l.reverse = List.reverse '' l :=
  ((List.reverse_involutive.toPerm _).image_eq_preimage_symm _).symm

@[simp]
/--
lemma `reverse_zero` / 引理 `reverse_zero`

English:
lemma reverse_zero
  statement: (0 : Language α).reverse = 0
  proof: rfl

@[simp]

中文:
引理 reverse_zero
  结论: (0 : Language α).reverse = 0
  证明: rfl

@[simp]
-/
lemma reverse_zero : (0 : Language α).reverse = 0 := rfl

@[simp]
/--
lemma `reverse_one` / 引理 `reverse_one`

English:
lemma reverse_one
  statement: (1 : Language α).reverse = 1
  proof: by
  simp [reverse, ← one_def]

中文:
引理 reverse_one
  结论: (1 : Language α).reverse = 1
  证明: by
  simp [reverse, ← one_def]

Depends on / 依赖: one_def, reverse
-/
lemma reverse_one : (1 : Language α).reverse = 1 := by
  simp [reverse, ← one_def]

/--
lemma `reverse_involutive` / 引理 `reverse_involutive`

English:
lemma reverse_involutive
  statement: Function.Involutive (reverse : Language α -> _)
  proof: List.reverse_involutive.preimage

中文:
引理 reverse_involutive
  结论: 函数.对合 (reverse : Language α -> _)
  证明: List.reverse_involutive.preimage

Depends on / 依赖: List.reverse_involutive.preimage, preimage, reverse_involutive
-/
lemma reverse_involutive : Function.Involutive (reverse : Language α -> _) :=
  List.reverse_involutive.preimage

/--
lemma `reverse_bijective` / 引理 `reverse_bijective`

English:
lemma reverse_bijective
  statement: Function.Bijective (reverse : Language α -> _)
  proof: reverse_involutive.bijective

中文:
引理 reverse_bijective
  结论: 函数.双射 (reverse : Language α -> _)
  证明: reverse_involutive.bijective

Depends on / 依赖: bijective, reverse_involutive, reverse_involutive.bijective
-/
lemma reverse_bijective : Function.Bijective (reverse : Language α -> _) :=
  reverse_involutive.bijective

/--
lemma `reverse_injective` / 引理 `reverse_injective`

English:
lemma reverse_injective
  statement: Function.Injective (reverse : Language α -> _)
  proof: reverse_involutive.injective

中文:
引理 reverse_injective
  结论: 函数.单射 (reverse : Language α -> _)
  证明: reverse_involutive.injective

Depends on / 依赖: injective, reverse_involutive, reverse_involutive.injective
-/
lemma reverse_injective : Function.Injective (reverse : Language α -> _) :=
  reverse_involutive.injective

/--
lemma `reverse_surjective` / 引理 `reverse_surjective`

English:
lemma reverse_surjective
  statement: Function.Surjective (reverse : Language α -> _)
  proof: reverse_involutive.surjective

@[simp]

中文:
引理 reverse_surjective
  结论: 函数.满射 (reverse : Language α -> _)
  证明: reverse_involutive.surjective

@[simp]

Depends on / 依赖: reverse_involutive, reverse_involutive.surjective, surjective
-/
lemma reverse_surjective : Function.Surjective (reverse : Language α -> _) :=
  reverse_involutive.surjective

@[simp]
/--
lemma `reverse_reverse` / 引理 `reverse_reverse`

English:
lemma reverse_reverse
  given: (l : Language α)
  statement: l.reverse.reverse = l
  proof: reverse_involutive l

@[simp]

中文:
引理 reverse_reverse
  条件: (l : Language α)
  结论: l.reverse.reverse = l
  证明: reverse_involutive l

@[simp]

Depends on / 依赖: reverse_involutive
-/
lemma reverse_reverse (l : Language α) : l.reverse.reverse = l := reverse_involutive l

@[simp]
/--
lemma `reverse_add` / 引理 `reverse_add`

English:
lemma reverse_add
  given: (l m : Language α)
  statement: (l + m).reverse = l.reverse + m.reverse
  proof: rfl

中文:
引理 reverse_add
  条件: (l m : Language α)
  结论: (l + m).reverse = l.reverse + m.reverse
  证明: rfl
-/
lemma reverse_add (l m : Language α) : (l + m).reverse = l.reverse + m.reverse := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `reverse_mul` / 引理 `reverse_mul`

English:
lemma reverse_mul
  given: (l m : Language α)
  statement: (l * m).reverse = m.reverse * l.reverse
  proof: by
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]

中文:
引理 reverse_mul
  条件: (l m : Language α)
  结论: (l * m).reverse = m.reverse * l.reverse
  证明: by
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]

Depends on / 依赖: List.reverse_append, image2_image_left, image2_image_right, image2_swap, image_image2, mul_def, reverse_append, reverse_eq_image
-/
lemma reverse_mul (l m : Language α) : (l * m).reverse = m.reverse * l.reverse := by
  simp only [mul_def, reverse_eq_image, image2_image_left, image2_image_right, image_image2,
    List.reverse_append]
  apply image2_swap

@[simp]
/--
lemma `reverse_iSup` / 引理 `reverse_iSup`

English:
lemma reverse_iSup
  given: {ι : Sort*} (l : ι -> Language α)
  statement: (⨆ i, l i).reverse = ⨆ i, (l i).reverse
  proof: preimage_iUnion

@[simp]

中文:
引理 reverse_iSup
  条件: {ι : 类型层*} (l : ι -> Language α)
  结论: (⨆ i, l i).reverse = ⨆ i, (l i).reverse
  证明: preimage_iUnion

@[simp]

Depends on / 依赖: preimage_iUnion
-/
lemma reverse_iSup {ι : Sort*} (l : ι -> Language α) : (⨆ i, l i).reverse = ⨆ i, (l i).reverse :=
  preimage_iUnion

@[simp]
/--
lemma `reverse_iInf` / 引理 `reverse_iInf`

English:
lemma reverse_iInf
  given: {ι : Sort*} (l : ι -> Language α)
  statement: (⨅ i, l i).reverse = ⨅ i, (l i).reverse
  proof: preimage_iInter

中文:
引理 reverse_iInf
  条件: {ι : 类型层*} (l : ι -> Language α)
  结论: (⨅ i, l i).reverse = ⨅ i, (l i).reverse
  证明: preimage_iInter

Depends on / 依赖: preimage_iInter
-/
lemma reverse_iInf {ι : Sort*} (l : ι -> Language α) : (⨅ i, l i).reverse = ⨅ i, (l i).reverse :=
  preimage_iInter

variable (α) in
/-- `Language.reverse` as a ring isomorphism to the opposite ring. -/
@[simps]
/--
Definition of `reverseIso` / `reverseIso` 的定义

English:
definition reverseIso
  signature: : Language α ≃+* (Language α)ᵐᵒᵖ where
  body: .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
right_inv l' := MulOpposite.unop_injective reverse_reverse l'.unop
map_mul' l₁ l₂ := MulOpposite.unop_injective reverse_mul l₁ l₂
map_add' l₁ l₂ := MulOpposite.unop_injective reverse_add l₁ l₂

@[simp]

中文:
定义 reverseIso
  签名: : Language α ≃+* (Language α)ᵐᵒᵖ where
  定义体: .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
right_inv l' := MulOpposite.unop_injective reverse_reverse l'.unop
map_mul' l₁ l₂ := MulOpposite.unop_injective reverse_mul l₁ l₂
map_add' l₁ l₂ := MulOpposite.unop_injective reverse_add l₁ l₂

@[simp]

Depends on / 依赖: l.reverse, reverse
-/
def reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ where
  toFun l := .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
right_inv l' := MulOpposite.unop_injective reverse_reverse l'.unop
map_mul' l₁ l₂ := MulOpposite.unop_injective reverse_mul l₁ l₂
map_add' l₁ l₂ := MulOpposite.unop_injective reverse_add l₁ l₂

@[simp]
/--
lemma `reverse_pow` / 引理 `reverse_pow`

English:
lemma reverse_pow
  given: (l : Language α) (n : Nat)
  statement: (l ^ n).reverse = l.reverse ^ n
  proof: MulOpposite.op_injective (map_pow (reverseIso α) l n)

@[simp]

中文:
引理 reverse_pow
  条件: (l : Language α) (n : 自然数)
  结论: (l ^ n).reverse = l.reverse ^ n
  证明: MulOpposite.op_injective (map_pow (reverseIso α) l n)

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_injective, map_pow, op_injective, reverseIso
-/
lemma reverse_pow (l : Language α) (n : Nat) : (l ^ n).reverse = l.reverse ^ n :=
  MulOpposite.op_injective (map_pow (reverseIso α) l n)

@[simp]
/--
lemma `reverse_kstar` / 引理 `reverse_kstar`

English:
lemma reverse_kstar
  given: (l : Language α)
  statement: l∗.reverse = l.reverse∗
  proof: by
  simp only [kstar_eq_iSup_pow, reverse_iSup, reverse_pow]

@[simp]

中文:
引理 reverse_kstar
  条件: (l : Language α)
  结论: l∗.reverse = l.reverse∗
  证明: by
  simp only [kstar_eq_iSup_pow, reverse_iSup, reverse_pow]

@[simp]

Depends on / 依赖: kstar_eq_iSup_pow, reverse_iSup, reverse_pow
-/
lemma reverse_kstar (l : Language α) : l∗.reverse = l.reverse∗ := by
  simp only [kstar_eq_iSup_pow, reverse_iSup, reverse_pow]

@[simp]
/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  given: {x : List α} {l m : Language α}
  statement: x in l ⊓ m ↔ x in l ∧ x in m
  proof: by
  apply Set.mem_inter_iff

中文:
引理 mem_inf
  条件: {x : 列表 α} {l m : Language α}
  结论: x in l ⊓ m ↔ x in l ∧ x in m
  证明: by
  apply Set.mem_inter_iff

Depends on / 依赖: Set.mem_inter_iff, mem_inter_iff
-/
lemma mem_inf {x : List α} {l m : Language α} : x in l ⊓ m ↔ x in l ∧ x in m := by
  apply Set.mem_inter_iff

/--
lemma `compl_compl` / 引理 `compl_compl`

English:
lemma compl_compl
  given: (l : Language α)
  statement: lᶜᶜ = l
  proof: _root_.compl_compl l

中文:
引理 compl_compl
  条件: (l : Language α)
  结论: lᶜᶜ = l
  证明: _root_.compl_compl l

Depends on / 依赖: _root_, _root_.compl_compl, compl_compl
-/
lemma compl_compl (l : Language α) : lᶜᶜ = l :=
  _root_.compl_compl l

end Language

/--
Inductive type `Symbol` / 归纳类型 `Symbol`

English:
inductive Symbol
  parameters: (T N : Type*)
  constructors (2):
    - terminal: (t : T) : Symbol T N
    - nonterminal: (n : N) : Symbol T N

中文:
归纳类型 Symbol
  参数: (T N : 类型)
  构造子 (2 个):
    - terminal: (t : T) : Symbol T N
    - nonterminal: (n : N) : Symbol T N
-/
inductive Symbol (T N : Type*)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr, Fintype

attribute [nolint docBlame] Symbol.proxyType Symbol.proxyTypeEquiv
