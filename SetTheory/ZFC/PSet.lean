/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Set.Lattice

/-!
# Pre-sets

A pre-set is inductively defined by its indexing type and its members, which are themselves
pre-sets.

After defining pre-sets we define extensional equality over them, also inductively. We construct a
`Setoid` instance from it, and in `Mathlib/SetTheory/ZFC/Basic.lean` we define ZFC sets as the
quotient of pre-sets by extensional equality.

## Main definitions

* `PSet`: Pre-set.
* `PSet.Type`: Underlying type of a pre-set.
* `PSet.Func`: Underlying family of pre-sets of a pre-set.
* `PSet.Equiv`: Extensional equivalence of pre-sets. Defined inductively.
* `PSet.omega`: The von Neumann ordinal `ω` as a `PSet`.
-/

@[expose] public section


universe u v

/-- The type of pre-sets in universe `u`. A pre-set
  is a family of pre-sets indexed by a type in `Type u`.
  The ZFC universe is defined as a quotient of this
  to ensure extensionality. -/
@[pp_with_univ, use_set_notation_for_order]
/--
Inductive type `PSet` / 归纳类型 `PSet`

English:
inductive PSet
  parameters: : Type (u + 1)
  constructors (1):
    - mk: (α : Type u) (A : α -> PSet) : PSet

中文:
归纳类型 命题集合
  参数: : 类型 (u + 1)
  构造子 (1 个):
    - mk: (α : 类型u) (A : α -> 命题集合) : 命题集合
-/
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α -> PSet) : PSet

namespace PSet

/--
Definition of `«Type»` / `«Type»` 的定义

English:
definition «Type»
  signature: : PSet -> Type u

中文:
定义 «类型»
  签名: : 命题集合 -> 类型u
-/
def «Type» : PSet -> Type u
  | ⟨α, _⟩ => α

/--
Definition of `Func` / `Func` 的定义

English:
definition Func
  signature: : forall x : PSet, x.Type -> PSet

中文:
定义 Func
  签名: : 对任意 x : 命题集合, x.类型 -> 命题集合
-/
def Func : forall x : PSet, x.Type -> PSet
  | ⟨_, A⟩ => A

@[simp]
/--
theorem `mk_type` / 定理 `mk_type`

English:
theorem mk_type
  given: (α A)
  statement: «Type» ⟨α, A⟩ = α
  proof: rfl

@[simp]

中文:
定理 mk_type
  条件: (α A)
  结论: «类型» ⟨α, A⟩ = α
  证明: rfl

@[simp]
-/
theorem mk_type (α A) : «Type» ⟨α, A⟩ = α :=
  rfl

@[simp]
/--
theorem `mk_func` / 定理 `mk_func`

English:
theorem mk_func
  given: (α A)
  statement: Func ⟨α, A⟩ = A
  proof: rfl

@[simp]

中文:
定理 mk_func
  条件: (α A)
  结论: Func ⟨α, A⟩ = A
  证明: rfl

@[simp]
-/
theorem mk_func (α A) : Func ⟨α, A⟩ = A :=
  rfl

@[simp]
/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  statement: forall x : PSet, mk x.Type x.Func = x

中文:
定理 eta
  结论: 对任意 x : 命题集合, mk x.类型 x.Func = x
-/
theorem eta : forall x : PSet, mk x.Type x.Func = x
  | ⟨_, _⟩ => rfl

/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: : PSet -> PSet -> Prop

中文:
定义 等价
  签名: : 命题集合 -> 命题集合 -> 命题
-/
def Equiv : PSet -> PSet -> Prop
  | ⟨_, A⟩, ⟨_, B⟩ => (forall a, exists b, Equiv (A a) (B b)) ∧ (forall b, exists a, Equiv (A a) (B b))

/--
theorem `equiv_iff` / 定理 `equiv_iff`

English:
theorem equiv_iff

中文:
定理 equiv_iff
-/
theorem equiv_iff :
    forall {x y : PSet},
      Equiv x y ↔ (forall i, exists j, Equiv (x.Func i) (y.Func j)) ∧ forall j, exists i, Equiv (x.Func i) (y.Func j)
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl

/--
theorem `Equiv.exists_left` / 定理 `Equiv.exists_left`

English:
theorem Equiv.exists_left
  given: {x y : PSet} (h : Equiv x y)
  statement: forall i, exists j, Equiv (x.Func i) (y.Func j)
  proof: (equiv_iff.1 h).1

中文:
定理 等价.存在_left
  条件: {x y : 命题集合} (h : 等价 x y)
  结论: 对任意 i, 存在 j, 等价 (x.Func i) (y.Func j)
  证明: (equiv_iff.1 h).1

Depends on / 依赖: equiv_iff
-/
theorem Equiv.exists_left {x y : PSet} (h : Equiv x y) : forall i, exists j, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).1

/--
theorem `Equiv.exists_right` / 定理 `Equiv.exists_right`

English:
theorem Equiv.exists_right
  given: {x y : PSet} (h : Equiv x y)
  statement: forall j, exists i, Equiv (x.Func i) (y.Func j)
  proof: (equiv_iff.1 h).2

@[refl]

中文:
定理 等价.存在_right
  条件: {x y : 命题集合} (h : 等价 x y)
  结论: 对任意 j, 存在 i, 等价 (x.Func i) (y.Func j)
  证明: (equiv_iff.1 h).2

@[refl]

Depends on / 依赖: equiv_iff
-/
theorem Equiv.exists_right {x y : PSet} (h : Equiv x y) : forall j, exists i, Equiv (x.Func i) (y.Func j) :=
  (equiv_iff.1 h).2

@[refl]
/--
theorem `Equiv.refl` / 定理 `Equiv.refl`

English:
theorem Equiv.refl
  statement: forall x, Equiv x x

中文:
定理 等价.refl
  结论: 对任意 x, 等价 x x
-/
protected theorem Equiv.refl : forall x, Equiv x x
  | ⟨_, _⟩ => ⟨fun a => ⟨a, Equiv.refl _⟩, fun a => ⟨a, Equiv.refl _⟩⟩

/--
theorem `Equiv.rfl` / 定理 `Equiv.rfl`

English:
theorem Equiv.rfl
  given: {x}
  statement: Equiv x x
  proof: Equiv.refl x

中文:
定理 等价.rfl
  条件: {x}
  结论: 等价 x x
  证明: Equiv.refl x
-/
protected theorem Equiv.rfl {x} : Equiv x x :=
  Equiv.refl x

/--
theorem `Equiv.euc` / 定理 `Equiv.euc`

English:
theorem Equiv.euc
  statement: forall {x y z}, Equiv x y -> Equiv z y -> Equiv x z
  proof: αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩

@[symm]

中文:
定理 等价.euc
  结论: 对任意 {x y z}, 等价 x y -> 等价 z y -> 等价 x z
  证明: αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩

@[symm]
-/
protected theorem Equiv.euc : forall {x y z}, Equiv x y -> Equiv z y -> Equiv x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, ⟨γβ, βγ⟩ =>
    ⟨ fun a =>
        let ⟨b, ab⟩ := αβ a
        let ⟨c, bc⟩ := βγ b
        ⟨c, Equiv.euc ab bc⟩,
      fun c =>
        let ⟨b, cb⟩ := γβ c
        let ⟨a, ba⟩ := βα b
        ⟨a, Equiv.euc ba cb⟩ ⟩

@[symm]
/--
theorem `Equiv.symm` / 定理 `Equiv.symm`

English:
theorem Equiv.symm
  given: {x y}
  statement: Equiv x y -> Equiv y x
  proof: (Equiv.refl y).euc

中文:
定理 等价.symm
  条件: {x y}
  结论: 等价 x y -> 等价 y x
  证明: (Equiv.refl y).euc
-/
protected theorem Equiv.symm {x y} : Equiv x y -> Equiv y x :=
  (Equiv.refl y).euc

/--
theorem `Equiv.comm` / 定理 `Equiv.comm`

English:
theorem Equiv.comm
  given: {x y}
  statement: Equiv x y ↔ Equiv y x
  proof: ⟨Equiv.symm, Equiv.symm⟩

@[trans]

中文:
定理 等价.comm
  条件: {x y}
  结论: 等价 x y ↔ 等价 y x
  证明: ⟨Equiv.symm, Equiv.symm⟩

@[trans]
-/
protected theorem Equiv.comm {x y} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
/--
theorem `Equiv.trans` / 定理 `Equiv.trans`

English:
theorem Equiv.trans
  given: {x y z} (h1 : Equiv x y) (h2 : Equiv y z)
  statement: Equiv x z
  proof: h1.euc h2.symm

中文:
定理 等价.trans
  条件: {x y z} (h1 : 等价 x y) (h2 : 等价 y z)
  结论: 等价 x z
  证明: h1.euc h2.symm
-/
protected theorem Equiv.trans {x y z} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  h1.euc h2.symm

/--
theorem `equiv_of_isEmpty` / 定理 `equiv_of_isEmpty`

English:
theorem equiv_of_isEmpty
  given: (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type]
  statement: Equiv x y
  proof: equiv_iff.2 by simp

中文:
定理 equiv_of_isEmpty
  条件: (x y : 命题集合) [是空 x.类型] [是空 y.类型]
  结论: 等价 x y
  证明: equiv_iff.2 by simp
-/
protected theorem equiv_of_isEmpty (x y : PSet) [IsEmpty x.Type] [IsEmpty y.Type] : Equiv x y :=
equiv_iff.2 by simp

/--
Instance `setoid` / 实例 `setoid`

English:
instance setoid
  signature: : Setoid PSet
  body: ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

中文:
实例 setoid
  签名: : 集合等价关系 命题集合
  定义体: ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

Depends on / 依赖: Equiv.refl, Equiv.symm, Equiv.trans, PSet.Equiv
-/
instance setoid : Setoid PSet :=
  ⟨PSet.Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

/--
Definition of `Subset` / `Subset` 的定义

English:
definition Subset
  signature: (x y : PSet)
  body: forall a, exists b, Equiv (x.Func a) (y.Func b)

中文:
定义 子集
  签名: (x y : 命题集合)
  定义体: forall a, exists b, Equiv (x.Func a) (y.Func b)
-/
protected def Subset (x y : PSet) : Prop :=
  forall a, exists b, Equiv (x.Func a) (y.Func b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE PSet
  body: ⟨PSet.Subset⟩

中文:
实例 :
  签名: LE 命题集合
  定义体: ⟨PSet.Subset⟩

Depends on / 依赖: PSet.Subset, Subset
-/
instance : LE PSet :=
  ⟨PSet.Subset⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder PSet
  body: ⟨a, Equiv.refl _⟩
  le_trans x y z hxy hyz a := by
    obtain ⟨b, hb⟩ := hxy a
    obtain ⟨c, hc⟩ := hyz b
    exact ⟨c, hb.trans hc⟩

中文:
实例 :
  签名: 预序 命题集合
  定义体: ⟨a, Equiv.refl _⟩
  le_trans x y z hxy hyz a := by
    obtain ⟨b, hb⟩ := hxy a
    obtain ⟨c, hc⟩ := hyz b
    exact ⟨c, hb.trans hc⟩

Depends on / 依赖: Equiv.refl
-/
instance : Preorder PSet where
  le_refl _ a := ⟨a, Equiv.refl _⟩
  le_trans x y z hxy hyz a := by
    obtain ⟨b, hb⟩ := hxy a
    obtain ⟨c, hc⟩ := hyz b
    exact ⟨c, hb.trans hc⟩

/--
theorem `Equiv.ext` / 定理 `Equiv.ext`

English:
theorem Equiv.ext
  statement: forall x y : PSet, Equiv x y ↔ x subseteq y ∧ y subseteq x
  proof: βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩

中文:
定理 等价.ext
  结论: 对任意 x y : 命题集合, 等价 x y ↔ x subseteq y ∧ y subseteq x
  证明: βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩
-/
theorem Equiv.ext : forall x y : PSet, Equiv x y ↔ x subseteq y ∧ y subseteq x
  | ⟨_, _⟩, ⟨_, _⟩ =>
    ⟨fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩,
      fun ⟨αβ, βα⟩ =>
      ⟨αβ, fun b =>
        let ⟨a, h⟩ := βα b
        ⟨a, Equiv.symm h⟩⟩⟩

/--
theorem `Subset.congr_left` / 定理 `Subset.congr_left`

English:
theorem Subset.congr_left
  statement: forall {x y z : PSet}, Equiv x y -> (x subseteq z ↔ y subseteq z)
  proof: βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩

中文:
定理 子集.congr_left
  结论: 对任意 {x y z : 命题集合}, 等价 x y -> (x subseteq z ↔ y subseteq z)
  证明: βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩
-/
theorem Subset.congr_left : forall {x y z : PSet}, Equiv x y -> (x subseteq z ↔ y subseteq z)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun αγ b =>
      let ⟨a, ba⟩ := βα b
      let ⟨c, ac⟩ := αγ a
      ⟨c, (Equiv.symm ba).trans ac⟩,
      fun βγ a =>
      let ⟨b, ab⟩ := αβ a
      let ⟨c, bc⟩ := βγ b
      ⟨c, Equiv.trans ab bc⟩⟩

/--
theorem `Subset.congr_right` / 定理 `Subset.congr_right`

English:
theorem Subset.congr_right
  statement: forall {x y z : PSet}, Equiv x y -> (z subseteq x ↔ z subseteq y)
  proof: γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]

中文:
定理 子集.congr_right
  结论: 对任意 {x y z : 命题集合}, 等价 x y -> (z subseteq x ↔ z subseteq y)
  证明: γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
-/
theorem Subset.congr_right : forall {x y z : PSet}, Equiv x y -> (z subseteq x ↔ z subseteq y)
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩ =>
    ⟨fun γα c =>
      let ⟨a, ca⟩ := γα c
      let ⟨b, ab⟩ := αβ a
      ⟨b, ca.trans ab⟩,
      fun γβ c =>
      let ⟨b, cb⟩ := γβ c
      let ⟨a, ab⟩ := βα b
      ⟨a, cb.trans (Equiv.symm ab)⟩⟩

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: (x y : PSet)
  statement: x <= y ↔ x subseteq y
  proof: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]

中文:
定理 le_def
  条件: (x y : 命题集合)
  结论: x <= y ↔ x subseteq y
  证明: Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]

Depends on / 依赖: Iff.rfl
-/
theorem le_def (x y : PSet) : x <= y ↔ x subseteq y :=
  Iff.rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: (x y : PSet)
  statement: x < y ↔ x ⊂ y
  proof: Iff.rfl

中文:
定理 lt_def
  条件: (x y : 命题集合)
  结论: x < y ↔ x ⊂ y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def (x y : PSet) : x < y ↔ x ⊂ y :=
  Iff.rfl

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (y x : PSet.{u})
  body: exists b, Equiv x (y.Func b)

中文:
定义 Mem
  签名: (y x : 命题集合.{u})
  定义体: exists b, Equiv x (y.Func b)
-/
protected def Mem (y x : PSet.{u}) : Prop :=
  exists b, Equiv x (y.Func b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership PSet PSet
  body: ⟨PSet.Mem⟩

中文:
实例 :
  签名: Membership 命题集合 命题集合
  定义体: ⟨PSet.Mem⟩

Depends on / 依赖: PSet.Mem
-/
instance : Membership PSet PSet :=
  ⟨PSet.Mem⟩

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  given: {x y : PSet}
  statement: x in y ↔ exists b, Equiv x (y.Func b)
  proof: Iff.rfl

中文:
定理 mem_def
  条件: {x y : 命题集合}
  结论: x in y ↔ 存在 b, 等价 x (y.Func b)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_def {x y : PSet} : x in y ↔ exists b, Equiv x (y.Func b) :=
  Iff.rfl

/--
theorem `Mem.mk` / 定理 `Mem.mk`

English:
theorem Mem.mk
  given: {α : Type u} (A : α -> PSet) (a : α)
  statement: A a in mk α A
  proof: ⟨a, Equiv.refl (A a)⟩

中文:
定理 Mem.mk
  条件: {α : 类型u} (A : α -> 命题集合) (a : α)
  结论: A a in mk α A
  证明: ⟨a, Equiv.refl (A a)⟩

Depends on / 依赖: Equiv.refl
-/
theorem Mem.mk {α : Type u} (A : α -> PSet) (a : α) : A a in mk α A :=
  ⟨a, Equiv.refl (A a)⟩

/--
theorem `func_mem` / 定理 `func_mem`

English:
theorem func_mem
  given: (x : PSet) (i : x.Type)
  statement: x.Func i in x
  proof: Mem.mk _ _

中文:
定理 func_mem
  条件: (x : 命题集合) (i : x.类型)
  结论: x.Func i in x
  证明: Mem.mk _ _

Depends on / 依赖: Mem.mk
-/
theorem func_mem (x : PSet) (i : x.Type) : x.Func i in x := Mem.mk _ _

/--
theorem `Mem.ext` / 定理 `Mem.ext`

English:
theorem Mem.ext
  statement: forall {x y : PSet.{u}}, (forall w : PSet.{u}, w in x ↔ w in y) -> Equiv x y
  proof: (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩

中文:
定理 Mem.ext
  结论: 对任意 {x y : 命题集合.{u}}, (对任意 w : 命题集合.{u}, w in x ↔ w in y) -> 等价 x y
  证明: (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩

Depends on / 依赖: Mem.mk
-/
theorem Mem.ext : forall {x y : PSet.{u}}, (forall w : PSet.{u}, w in x ↔ w in y) -> Equiv x y
  | ⟨_, A⟩, ⟨_, B⟩, h =>
    ⟨fun a => (h (A a)).1 (Mem.mk A a), fun b =>
      let ⟨a, ha⟩ := (h (B b)).2 (Mem.mk B b)
      ⟨a, ha.symm⟩⟩

/--
theorem `Mem.congr_right` / 定理 `Mem.congr_right`

English:
theorem Mem.congr_right
  statement: forall {x y : PSet.{u}}, Equiv x y -> forall {w : PSet.{u}}, w in x ↔ w in y
  proof: αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩

中文:
定理 Mem.congr_right
  结论: 对任意 {x y : 命题集合.{u}}, 等价 x y -> 对任意 {w : 命题集合.{u}}, w in x ↔ w in y
  证明: αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩
-/
theorem Mem.congr_right : forall {x y : PSet.{u}}, Equiv x y -> forall {w : PSet.{u}}, w in x ↔ w in y
  | ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, _ =>
    ⟨fun ⟨a, ha⟩ =>
      let ⟨b, hb⟩ := αβ a
      ⟨b, ha.trans hb⟩,
      fun ⟨b, hb⟩ =>
      let ⟨a, ha⟩ := βα b
      ⟨a, hb.euc ha⟩⟩

/--
theorem `equiv_iff_mem` / 定理 `equiv_iff_mem`

English:
theorem equiv_iff_mem
  given: {x y : PSet.{u}}
  statement: Equiv x y ↔ forall {w : PSet.{u}}, w in x ↔ w in y
  proof: ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩

中文:
定理 equiv_iff_mem
  条件: {x y : 命题集合.{u}}
  结论: 等价 x y ↔ 对任意 {w : 命题集合.{u}}, w in x ↔ w in y
  证明: ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩

Depends on / 依赖: Mem.congr_right, Mem.mk, congr_right, h.symm
-/
theorem equiv_iff_mem {x y : PSet.{u}} : Equiv x y ↔ forall {w : PSet.{u}}, w in x ↔ w in y :=
  ⟨Mem.congr_right,
    match x, y with
    | ⟨_, A⟩, ⟨_, B⟩ => fun h =>
      ⟨fun a => h.1 (Mem.mk A a), fun b =>
        let ⟨a, h⟩ := h.2 (Mem.mk B b)
        ⟨a, h.symm⟩⟩⟩

/--
theorem `Mem.congr_left` / 定理 `Mem.congr_left`

English:
theorem Mem.congr_left
  statement: forall {x y : PSet.{u}}, Equiv x y -> forall {w : PSet.{u}}, x in w ↔ y in w

中文:
定理 Mem.congr_left
  结论: 对任意 {x y : 命题集合.{u}}, 等价 x y -> 对任意 {w : 命题集合.{u}}, x in w ↔ y in w
-/
theorem Mem.congr_left : forall {x y : PSet.{u}}, Equiv x y -> forall {w : PSet.{u}}, x in w ↔ y in w
  | _, _, h, ⟨_, _⟩ => ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩

/--
theorem `mem_of_subset` / 定理 `mem_of_subset`

English:
theorem mem_of_subset
  given: {x y z : PSet}
  statement: x subseteq y -> z in x -> z in y

中文:
定理 mem_of_subset
  条件: {x y z : 命题集合}
  结论: x subseteq y -> z in x -> z in y
-/
theorem mem_of_subset {x y z : PSet} : x subseteq y -> z in x -> z in y
  | h₁, ⟨a, h₂⟩ => (h₁ a).elim fun b h₃ => ⟨b, h₂.trans h₃⟩

/--
theorem `subset_iff` / 定理 `subset_iff`

English:
theorem subset_iff
  given: {x y : PSet}
  statement: x subseteq y ↔ forall ⦃z⦄, z in x -> z in y
  proof: ⟨fun h _ => mem_of_subset h, fun h a => h (Mem.mk _ a)⟩

中文:
定理 subset_iff
  条件: {x y : 命题集合}
  结论: x subseteq y ↔ 对任意 ⦃z⦄, z in x -> z in y
  证明: ⟨fun h _ => mem_of_subset h, fun h a => h (Mem.mk _ a)⟩

Depends on / 依赖: Mem.mk, mem_of_subset
-/
theorem subset_iff {x y : PSet} : x subseteq y ↔ forall ⦃z⦄, z in x -> z in y :=
  ⟨fun h _ => mem_of_subset h, fun h a => h (Mem.mk _ a)⟩

/--
theorem `mem_wf_aux` / 定理 `mem_wf_aux`

English:
theorem mem_wf_aux
  statement: forall {x y : PSet.{u}}, Equiv x y -> Acc (· in ·) y
  proof: H.exists_right b
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩

中文:
定理 mem_wf_aux
  结论: 对任意 {x y : 命题集合.{u}}, 等价 x y -> Acc (· in ·) y
  证明: H.exists_right b
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩
-/
private theorem mem_wf_aux : forall {x y : PSet.{u}}, Equiv x y -> Acc (· in ·) y
  | ⟨α, A⟩, ⟨β, B⟩, H =>
    ⟨_, by
      rintro ⟨γ, C⟩ ⟨b, hc⟩
      obtain ⟨a, ha⟩ := H.exists_right b
      have H := ha.trans hc.symm
      rw [mk_func] at H
      exact mem_wf_aux H⟩

/--
theorem `mem_wf` / 定理 `mem_wf`

English:
theorem mem_wf
  statement: @WellFounded PSet (· in ·)
  proof: ⟨fun x => mem_wf_aux Equiv.refl x⟩

中文:
定理 mem_wf
  结论: @良基 命题集合 (· in ·)
  证明: ⟨fun x => mem_wf_aux Equiv.refl x⟩

Depends on / 依赖: Equiv.refl, PseudoEMetricSpace, PseudoMetricSpace, PseudoMetricSpace.toPseudoEMetricSpace, mem_wf_aux, toPseudoEMetricSpace
-/
theorem mem_wf : @WellFounded PSet (· in ·) :=
⟨fun x => mem_wf_aux Equiv.refl x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsWellFounded PSet (· in ·)
  body: ⟨mem_wf⟩

中文:
实例 :
  签名: 是良基 命题集合 (· in ·)
  定义体: ⟨mem_wf⟩

Depends on / 依赖: mem_wf
-/
instance : IsWellFounded PSet (· in ·) :=
  ⟨mem_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation PSet
  body: ⟨_, mem_wf⟩

中文:
实例 :
  签名: 良基关系 命题集合
  定义体: ⟨_, mem_wf⟩

Depends on / 依赖: mem_wf
-/
instance : WellFoundedRelation PSet :=
  ⟨_, mem_wf⟩

/--
theorem `mem_asymm` / 定理 `mem_asymm`

English:
theorem mem_asymm
  given: {x y : PSet}
  statement: x in y -> y ∉ x
  proof: asymm_of (· in ·)

中文:
定理 mem_asymm
  条件: {x y : 命题集合}
  结论: x in y -> y ∉ x
  证明: asymm_of (· in ·)

Depends on / 依赖: asymm_of
-/
theorem mem_asymm {x y : PSet} : x in y -> y ∉ x :=
  asymm_of (· in ·)

/--
theorem `mem_irrefl` / 定理 `mem_irrefl`

English:
theorem mem_irrefl
  given: (x : PSet)
  statement: x ∉ x
  proof: irrefl_of (· in ·) x

中文:
定理 mem_irrefl
  条件: (x : 命题集合)
  结论: x ∉ x
  证明: irrefl_of (· in ·) x

Depends on / 依赖: irrefl_of
-/
theorem mem_irrefl (x : PSet) : x ∉ x :=
  irrefl_of (· in ·) x

/--
theorem `not_subset_of_mem` / 定理 `not_subset_of_mem`

English:
theorem not_subset_of_mem
  given: {x y : PSet} (h : x in y)
  statement: ¬ y subseteq x
  proof: fun h' => mem_irrefl _ mem_of_subset h' h

中文:
定理 not_subset_of_mem
  条件: {x y : 命题集合} (h : x in y)
  结论: ¬ y subseteq x
  证明: fun h' => mem_irrefl _ mem_of_subset h' h

Depends on / 依赖: mem_irrefl, mem_of_subset
-/
theorem not_subset_of_mem {x y : PSet} (h : x in y) : ¬ y subseteq x :=
fun h' => mem_irrefl _ mem_of_subset h' h

/--
theorem `notMem_of_subset` / 定理 `notMem_of_subset`

English:
theorem notMem_of_subset
  given: {x y : PSet} (h : x subseteq y)
  statement: y ∉ x
  proof: imp_not_comm.2 not_subset_of_mem h

中文:
定理 notMem_of_subset
  条件: {x y : 命题集合} (h : x subseteq y)
  结论: y ∉ x
  证明: imp_not_comm.2 not_subset_of_mem h

Depends on / 依赖: imp_not_comm, not_subset_of_mem
-/
theorem notMem_of_subset {x y : PSet} (h : x subseteq y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (u : PSet.{u})
  body: { x | x in u }

@[simp]

中文:
定义 toSet
  签名: (u : 命题集合.{u})
  定义体: { x | x in u }

@[simp]
-/
def toSet (u : PSet.{u}) : Set PSet.{u} :=
  { x | x in u }

@[simp]
/--
theorem `mem_toSet` / 定理 `mem_toSet`

English:
theorem mem_toSet
  given: (a u : PSet.{u})
  statement: a in u.toSet ↔ a in u
  proof: Iff.rfl

中文:
定理 mem_toSet
  条件: (a u : 命题集合.{u})
  结论: a in u.toSet ↔ a in u
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSet (a u : PSet.{u}) : a in u.toSet ↔ a in u :=
  Iff.rfl

/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
definition Nonempty
  signature: (u : PSet)
  body: u.toSet.Nonempty

中文:
定义 非空
  签名: (u : 命题集合)
  定义体: u.toSet.Nonempty
-/
protected def Nonempty (u : PSet) : Prop :=
  u.toSet.Nonempty

/--
theorem `nonempty_def` / 定理 `nonempty_def`

English:
theorem nonempty_def
  given: (u : PSet)
  statement: u.Nonempty ↔ exists x, x in u
  proof: Iff.rfl

中文:
定理 nonempty_def
  条件: (u : 命题集合)
  结论: u.非空 ↔ 存在 x, x in u
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem nonempty_def (u : PSet) : u.Nonempty ↔ exists x, x in u :=
  Iff.rfl

/--
theorem `nonempty_of_mem` / 定理 `nonempty_of_mem`

English:
theorem nonempty_of_mem
  given: {x u : PSet} (h : x in u)
  statement: u.Nonempty
  proof: ⟨x, h⟩

@[simp]

中文:
定理 nonempty_of_mem
  条件: {x u : 命题集合} (h : x in u)
  结论: u.非空
  证明: ⟨x, h⟩

@[simp]
-/
theorem nonempty_of_mem {x u : PSet} (h : x in u) : u.Nonempty :=
  ⟨x, h⟩

@[simp]
/--
theorem `nonempty_toSet_iff` / 定理 `nonempty_toSet_iff`

English:
theorem nonempty_toSet_iff
  given: {u : PSet}
  statement: u.toSet.Nonempty ↔ u.Nonempty
  proof: Iff.rfl

中文:
定理 nonempty_toSet_iff
  条件: {u : 命题集合}
  结论: u.toSet.非空 ↔ u.非空
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem nonempty_toSet_iff {u : PSet} : u.toSet.Nonempty ↔ u.Nonempty :=
  Iff.rfl

/--
theorem `nonempty_type_iff_nonempty` / 定理 `nonempty_type_iff_nonempty`

English:
theorem nonempty_type_iff_nonempty
  given: {x : PSet}
  statement: Nonempty x.Type ↔ PSet.Nonempty x
  proof: ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩

中文:
定理 nonempty_type_iff_nonempty
  条件: {x : 命题集合}
  结论: 非空 x.类型 ↔ 命题集合.非空 x
  证明: ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩

Depends on / 依赖: func_mem
-/
theorem nonempty_type_iff_nonempty {x : PSet} : Nonempty x.Type ↔ PSet.Nonempty x :=
  ⟨fun ⟨i⟩ => ⟨_, func_mem _ i⟩, fun ⟨_, j, _⟩ => ⟨j⟩⟩

/--
theorem `nonempty_of_nonempty_type` / 定理 `nonempty_of_nonempty_type`

English:
theorem nonempty_of_nonempty_type
  given: (x : PSet) [h : Nonempty x.Type]
  statement: PSet.Nonempty x
  proof: nonempty_type_iff_nonempty.1 h

中文:
定理 nonempty_of_nonempty_type
  条件: (x : 命题集合) [h : 非空 x.类型]
  结论: 命题集合.非空 x
  证明: nonempty_type_iff_nonempty.1 h

Depends on / 依赖: nonempty_type_iff_nonempty
-/
theorem nonempty_of_nonempty_type (x : PSet) [h : Nonempty x.Type] : PSet.Nonempty x :=
  nonempty_type_iff_nonempty.1 h

/--
theorem `Equiv.eq` / 定理 `Equiv.eq`

English:
theorem Equiv.eq
  given: {x y : PSet}
  statement: Equiv x y ↔ toSet x = toSet y
  proof: equiv_iff_mem.trans .symm Set.ext_iff

中文:
定理 等价.eq
  条件: {x y : 命题集合}
  结论: 等价 x y ↔ toSet x = toSet y
  证明: equiv_iff_mem.trans .symm Set.ext_iff

Depends on / 依赖: Set.ext_iff, equiv_iff_mem, equiv_iff_mem.trans, ext_iff
-/
theorem Equiv.eq {x y : PSet} : Equiv x y ↔ toSet x = toSet y :=
equiv_iff_mem.trans .symm Set.ext_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe PSet (Set PSet)
  body: ⟨toSet⟩

中文:
实例 :
  签名: Coe 命题集合 (集合 命题集合)
  定义体: ⟨toSet⟩
-/
instance : Coe PSet (Set PSet) :=
  ⟨toSet⟩

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : PSet
  body: ⟨_, PEmpty.elim⟩

中文:
定义 empty
  签名: : 命题集合
  定义体: ⟨_, PEmpty.elim⟩
-/
protected def empty : PSet :=
  ⟨_, PEmpty.elim⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection PSet
  body: ⟨PSet.empty⟩

中文:
实例 :
  签名: EmptyCollection 命题集合
  定义体: ⟨PSet.empty⟩

Depends on / 依赖: PSet.empty
-/
instance : EmptyCollection PSet :=
  ⟨PSet.empty⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited PSet
  body: ⟨∅⟩

中文:
实例 :
  签名: 可居 命题集合
  定义体: ⟨∅⟩
-/
instance : Inhabited PSet :=
  ⟨∅⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty («Type» ∅)
  body: ⟨PEmpty.elim⟩

中文:
实例 :
  签名: 是空 («类型» ∅)
  定义体: ⟨PEmpty.elim⟩

Depends on / 依赖: PEmpty, PEmpty.elim
-/
instance : IsEmpty («Type» ∅) :=
  ⟨PEmpty.elim⟩

/--
theorem `empty_def` / 定理 `empty_def`

English:
theorem empty_def
  statement: (∅ : PSet) = ⟨_, PEmpty.elim⟩
  proof: by
  simp [EmptyCollection.emptyCollection, PSet.empty]

@[simp]

中文:
定理 empty_def
  结论: (∅ : 命题集合) = ⟨_, 命题空.elim⟩
  证明: by
  simp [EmptyCollection.emptyCollection, PSet.empty]

@[simp]

Depends on / 依赖: EmptyCollection, EmptyCollection.emptyCollection, PSet.empty, emptyCollection
-/
theorem empty_def : (∅ : PSet) = ⟨_, PEmpty.elim⟩ := by
  simp [EmptyCollection.emptyCollection, PSet.empty]

@[simp]
/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (x : PSet.{u})
  statement: x ∉ (∅ : PSet.{u})
  proof: IsEmpty.exists_iff.1

@[simp]

中文:
定理 notMem_empty
  条件: (x : 命题集合.{u})
  结论: x ∉ (∅ : 命题集合.{u})
  证明: IsEmpty.exists_iff.1

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.exists_iff, exists_iff
-/
theorem notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u}) :=
  IsEmpty.exists_iff.1

@[simp]
/--
theorem `toSet_empty` / 定理 `toSet_empty`

English:
theorem toSet_empty
  statement: toSet ∅ = ∅
  proof: by simp [toSet]

@[simp]

中文:
定理 toSet_empty
  结论: toSet ∅ = ∅
  证明: by simp [toSet]

@[simp]
-/
theorem toSet_empty : toSet ∅ = ∅ := by simp [toSet]

@[simp]
/--
theorem `empty_subset` / 定理 `empty_subset`

English:
theorem empty_subset
  given: (x : PSet.{u})
  statement: (∅ : PSet) subseteq x
  proof: fun x => x.elim

@[simp]

中文:
定理 empty_subset
  条件: (x : 命题集合.{u})
  结论: (∅ : 命题集合) subseteq x
  证明: fun x => x.elim

@[simp]

Depends on / 依赖: x.elim
-/
theorem empty_subset (x : PSet.{u}) : (∅ : PSet) subseteq x := fun x => x.elim

@[simp]
/--
theorem `not_nonempty_empty` / 定理 `not_nonempty_empty`

English:
theorem not_nonempty_empty
  statement: ¬PSet.Nonempty ∅
  proof: by simp [PSet.Nonempty]

中文:
定理 not_nonempty_empty
  结论: ¬命题集合.非空 ∅
  证明: by simp [PSet.Nonempty]

Depends on / 依赖: Nonempty, PSet.Nonempty
-/
theorem not_nonempty_empty : ¬PSet.Nonempty ∅ := by simp [PSet.Nonempty]

/--
theorem `equiv_empty` / 定理 `equiv_empty`

English:
theorem equiv_empty
  given: (x : PSet) [IsEmpty x.Type]
  statement: Equiv x ∅
  proof: PSet.equiv_of_isEmpty x _

中文:
定理 equiv_empty
  条件: (x : 命题集合) [是空 x.类型]
  结论: 等价 x ∅
  证明: PSet.equiv_of_isEmpty x _
-/
protected theorem equiv_empty (x : PSet) [IsEmpty x.Type] : Equiv x ∅ :=
  PSet.equiv_of_isEmpty x _

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (x y : PSet)
  body: ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩

中文:
定义 insert
  签名: (x y : 命题集合)
  定义体: ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩
-/
protected def insert (x y : PSet) : PSet :=
  ⟨Option y.Type, fun o => Option.casesOn o x y.Func⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert PSet PSet
  body: ⟨PSet.insert⟩

中文:
实例 :
  签名: Insert 命题集合 命题集合
  定义体: ⟨PSet.insert⟩

Depends on / 依赖: PSet.insert, insert
-/
instance : Insert PSet PSet :=
  ⟨PSet.insert⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton PSet PSet
  body: ⟨fun s => insert s ∅⟩

中文:
实例 :
  签名: 单例 命题集合 命题集合
  定义体: ⟨fun s => insert s ∅⟩

Depends on / 依赖: insert
-/
instance : Singleton PSet PSet :=
  ⟨fun s => insert s ∅⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulSingleton PSet PSet
  body: ⟨fun _ => rfl⟩

中文:
实例 :
  签名: LawfulSingleton 命题集合 命题集合
  定义体: ⟨fun _ => rfl⟩
-/
instance : LawfulSingleton PSet PSet :=
  ⟨fun _ => rfl⟩

instance (x y : PSet) : Inhabited (insert x y).Type :=
  inferInstanceAs (Inhabited <| Option y.Type)

@[simp]
/--
theorem `mem_insert_iff` / 定理 `mem_insert_iff`

English:
theorem mem_insert_iff
  statement: forall {x y z : PSet.{u}}, x in insert y z ↔ Equiv x y ∨ x in z

中文:
定理 mem_insert_iff
  结论: 对任意 {x y z : 命题集合.{u}}, x in insert y z ↔ 等价 x y ∨ x in z
-/
theorem mem_insert_iff : forall {x y z : PSet.{u}}, x in insert y z ↔ Equiv x y ∨ x in z
  | x, y, ⟨α, A⟩ =>
    show (x in PSet.mk (Option α) fun o => Option.rec y A o) ↔ Equiv x y ∨ x in PSet.mk α A from
      ⟨fun m =>
        match m with
        | ⟨some a, ha⟩ => Or.inr ⟨a, ha⟩
        | ⟨none, h⟩ => Or.inl h,
        fun m =>
        match m with
        | Or.inr ⟨a, ha⟩ => ⟨some a, ha⟩
        | Or.inl h => ⟨none, h⟩⟩

/--
theorem `mem_insert` / 定理 `mem_insert`

English:
theorem mem_insert
  given: (x y : PSet)
  statement: x in insert x y
  proof: mem_insert_iff.2 Or.inl Equiv.rfl

中文:
定理 mem_insert
  条件: (x y : 命题集合)
  结论: x in insert x y
  证明: mem_insert_iff.2 Or.inl Equiv.rfl

Depends on / 依赖: Equiv.rfl, Or.inl, mem_insert_iff
-/
theorem mem_insert (x y : PSet) : x in insert x y :=
mem_insert_iff.2 Or.inl Equiv.rfl

/--
theorem `mem_insert_of_mem` / 定理 `mem_insert_of_mem`

English:
theorem mem_insert_of_mem
  given: {y z : PSet} (x) (h : z in y)
  statement: z in insert x y
  proof: mem_insert_iff.2 Or.inr h

@[simp]

中文:
定理 mem_insert_of_mem
  条件: {y z : 命题集合} (x) (h : z in y)
  结论: z in insert x y
  证明: mem_insert_iff.2 Or.inr h

@[simp]

Depends on / 依赖: Or.inr, mem_insert_iff
-/
theorem mem_insert_of_mem {y z : PSet} (x) (h : z in y) : z in insert x y :=
mem_insert_iff.2 Or.inr h

@[simp]
/--
theorem `mem_singleton` / 定理 `mem_singleton`

English:
theorem mem_singleton
  given: {x y : PSet}
  statement: x in ({y} : PSet) ↔ Equiv x y
  proof: mem_insert_iff.trans
    ⟨fun o => Or.rec id (fun n => absurd n (notMem_empty _)) o, Or.inl⟩

中文:
定理 mem_singleton
  条件: {x y : 命题集合}
  结论: x in ({y} : 命题集合) ↔ 等价 x y
  证明: mem_insert_iff.trans
    ⟨fun o => Or.rec id (fun n => absurd n (notMem_empty _)) o, Or.inl⟩

Depends on / 依赖: Or.inl, Or.rec, absurd, mem_insert_iff, mem_insert_iff.trans, notMem_empty
-/
theorem mem_singleton {x y : PSet} : x in ({y} : PSet) ↔ Equiv x y :=
  mem_insert_iff.trans
    ⟨fun o => Or.rec id (fun n => absurd n (notMem_empty _)) o, Or.inl⟩

/--
theorem `mem_pair` / 定理 `mem_pair`

English:
theorem mem_pair
  given: {x y z : PSet}
  statement: x in ({y, z} : PSet) ↔ Equiv x y ∨ Equiv x z
  proof: by
  simp

中文:
定理 mem_pair
  条件: {x y z : 命题集合}
  结论: x in ({y, z} : 命题集合) ↔ 等价 x y ∨ 等价 x z
  证明: by
  simp
-/
theorem mem_pair {x y z : PSet} : x in ({y, z} : PSet) ↔ Equiv x y ∨ Equiv x z := by
  simp

/--
Definition of `ofNat` / `ofNat` 的定义

English:
definition ofNat
  signature: : Nat -> PSet

中文:
定义 of自然数
  签名: : 自然数 -> 命题集合
-/
def ofNat : Nat -> PSet
  | 0 => ∅
  | n + 1 => insert (ofNat n) (ofNat n)

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : PSet
  body: ⟨ULift Nat, fun n => ofNat n.down⟩

中文:
定义 omega
  签名: : 命题集合
  定义体: ⟨ULift Nat, fun n => ofNat n.down⟩

Depends on / 依赖: n.down
-/
def omega : PSet :=
  ⟨ULift Nat, fun n => ofNat n.down⟩

/--
Definition of `sep` / `sep` 的定义

English:
definition sep
  signature: (p : PSet -> Prop) (x : PSet)
  body: ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩

中文:
定义 sep
  签名: (p : 命题集合 -> 命题) (x : 命题集合)
  定义体: ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩
-/
protected def sep (p : PSet -> Prop) (x : PSet) : PSet :=
  ⟨{ a // p (x.Func a) }, fun y => x.Func y.1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sep PSet PSet
  body: ⟨PSet.sep⟩

中文:
实例 :
  签名: Sep 命题集合 命题集合
  定义体: ⟨PSet.sep⟩

Depends on / 依赖: PSet.sep
-/
instance : Sep PSet PSet :=
  ⟨PSet.sep⟩

/--
theorem `mem_sep` / 定理 `mem_sep`

English:
theorem mem_sep
  given: {p : PSet -> Prop} (H : forall x y, Equiv x y -> p x -> p y)

中文:
定理 mem_sep
  条件: {p : 命题集合 -> 命题} (H : 对任意 x y, 等价 x y -> p x -> p y)
-/
theorem mem_sep {p : PSet -> Prop} (H : forall x y, Equiv x y -> p x -> p y) :
    forall {x y : PSet}, y in PSet.sep p x ↔ y in x ∧ p y
  | ⟨_, _⟩, _ =>
    ⟨fun ⟨⟨a, pa⟩, h⟩ => ⟨⟨a, h⟩, H _ _ h.symm pa⟩, fun ⟨⟨a, h⟩, pa⟩ =>
      ⟨⟨a, H _ _ h pa⟩, h⟩⟩

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (x : PSet)
  body: ⟨Set x.Type, fun p => ⟨p, fun y => x.Func y.1⟩⟩

@[simp]

中文:
定义 powerset
  签名: (x : 命题集合)
  定义体: ⟨Set x.Type, fun p => ⟨p, fun y => x.Func y.1⟩⟩

@[simp]

Depends on / 依赖: x.Func, x.Type
-/
def powerset (x : PSet) : PSet :=
  ⟨Set x.Type, fun p => ⟨p, fun y => x.Func y.1⟩⟩

@[simp]
/--
theorem `mem_powerset` / 定理 `mem_powerset`

English:
theorem mem_powerset
  statement: forall {x y : PSet}, y in powerset x ↔ y subseteq x
  proof: βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩

中文:
定理 mem_powerset
  结论: 对任意 {x y : 命题集合}, y in powerset x ↔ y subseteq x
  证明: βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩
-/
theorem mem_powerset : forall {x y : PSet}, y in powerset x ↔ y subseteq x
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a, _⟩ => ⟨a, Equiv.refl (A a)⟩, fun βα =>
      ⟨{ a | exists b, Equiv (B b) (A a) }, fun b =>
        let ⟨a, ba⟩ := βα b
        ⟨⟨a, b, ba⟩, ba⟩,
        fun ⟨_, b, ba⟩ => ⟨b, ba⟩⟩⟩

/--
Definition of `sUnion` / `sUnion` 的定义

English:
definition sUnion
  signature: (a : PSet)
  body: ⟨Σ x, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]

中文:
定义 集合并集
  签名: (a : 命题集合)
  定义体: ⟨Σ x, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]

Depends on / 依赖: a.Func
-/
def sUnion (a : PSet) : PSet :=
  ⟨Σ x, (a.Func x).Type, fun ⟨x, y⟩ => (a.Func x).Func y⟩

@[inherit_doc]
prefix:110 "⋃₀ " => sUnion

@[simp]
/--
theorem `mem_sUnion` / 定理 `mem_sUnion`

English:
theorem mem_sUnion
  statement: forall {x y : PSet.{u}}, y in ⋃₀ x ↔ exists z in x, y in z
  proof: Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩

@[simp]

中文:
定理 mem_sUnion
  结论: 对任意 {x y : 命题集合.{u}}, y in ⋃₀ x ↔ 存在 z in x, y in z
  证明: Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩

@[simp]

Depends on / 依赖: Mem.mk
-/
theorem mem_sUnion : forall {x y : PSet.{u}}, y in ⋃₀ x ↔ exists z in x, y in z
  | ⟨α, A⟩, y =>
    ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ =>
      have : Func (A a) c in mk (A a).Type (A a).Func := Mem.mk (A a).Func c
      ⟨_, Mem.mk _ _, (Mem.congr_left e).2 (by rwa [eta] at this)⟩,
      fun ⟨⟨β, B⟩, ⟨a, (e : Equiv (mk β B) (A a))⟩, ⟨b, yb⟩⟩ => by
      rw [← eta (A a)] at e
      exact
        let ⟨βt, _⟩ := e
        let ⟨c, bc⟩ := βt b
        ⟨⟨a, c⟩, yb.trans bc⟩⟩

@[simp]
/--
theorem `toSet_sUnion` / 定理 `toSet_sUnion`

English:
theorem toSet_sUnion
  given: (x : PSet.{u})
  statement: (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet)
  proof: by
  ext
  simp

中文:
定理 toSet_sUnion
  条件: (x : 命题集合.{u})
  结论: (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet)
  证明: by
  ext
  simp
-/
theorem toSet_sUnion (x : PSet.{u}) : (⋃₀ x).toSet = ⋃₀ (toSet '' x.toSet) := by
  ext
  simp

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (f : PSet.{u} -> PSet.{u}) (x : PSet.{u})
  body: ⟨x.Type, f ∘ x.Func⟩

中文:
定义 像
  签名: (f : 命题集合.{u} -> 命题集合.{u}) (x : 命题集合.{u})
  定义体: ⟨x.Type, f ∘ x.Func⟩

Depends on / 依赖: x.Func, x.Type
-/
def image (f : PSet.{u} -> PSet.{u}) (x : PSet.{u}) : PSet :=
  ⟨x.Type, f ∘ x.Func⟩

/--
theorem `mem_image` / 定理 `mem_image`

English:
theorem mem_image
  given: {f : PSet.{u} -> PSet.{u}} (H : forall x y, Equiv x y -> Equiv (f x) (f y))

中文:
定理 mem_image
  条件: {f : 命题集合.{u} -> 命题集合.{u}} (H : 对任意 x y, 等价 x y -> 等价 (f x) (f y))
-/
theorem mem_image {f : PSet.{u} -> PSet.{u}} (H : forall x y, Equiv x y -> Equiv (f x) (f y)) :
    forall {x y : PSet.{u}}, y in image f x ↔ exists z in x, Equiv y (f z)
  | ⟨_, A⟩, _ =>
⟨fun ⟨a, ya⟩ => ⟨A a, Mem.mk A a, ya⟩, fun ⟨_, ⟨a, za⟩, yz⟩ => ⟨a, yz.trans H _ _ za⟩⟩

/--
Definition of `Lift` / `Lift` 的定义

English:
definition Lift
  signature: : PSet.{u} -> PSet.{max u v}

中文:
定义 Lift
  签名: : 命题集合.{u} -> 命题集合.{最大值 u v}
-/
protected def Lift : PSet.{u} -> PSet.{max u v}
  | ⟨α, A⟩ => ⟨ULift.{v, u} α, fun ⟨x⟩ => PSet.Lift (A x)⟩

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: : PSet.{max (u + 1) v}
  body: ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩

中文:
定义 embed
  签名: : 命题集合.{最大值 (u + 1) v}
  定义体: ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩

Depends on / 依赖: PSet.Lift
-/
def embed : PSet.{max (u + 1) v} :=
  ⟨ULift.{v, u + 1} PSet, fun ⟨x⟩ => PSet.Lift.{u, max (u + 1) v} x⟩

/--
theorem `lift_mem_embed` / 定理 `lift_mem_embed`

English:
theorem lift_mem_embed
  statement: forall x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x in embed.{u, v}
  proof: fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩

中文:
定理 lift_mem_embed
  结论: 对任意 x : 命题集合.{u}, 命题集合.Lift.{u, 最大值 (u + 1) v} x in embed.{u, v}
  证明: fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩
-/
theorem lift_mem_embed : forall x : PSet.{u}, PSet.Lift.{u, max (u + 1) v} x in embed.{u, v} := fun x =>
  ⟨⟨x⟩, Equiv.rfl⟩

end PSet
