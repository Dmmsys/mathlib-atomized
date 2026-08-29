/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.SetTheory.ZFC.Ordinal

/-!
# ZFC classes

Classes in set theory are usually defined as collections of elements satisfying some property.
Here, however, we define `Class` as `Set ZFSet` to derive many instances automatically,
most of them being the lifting of set operations to classes. The usual definition is then
definitionally equal to ours.

## Main definitions

* `Class`: Defined as `Set ZFSet`.
* `Class.iota`: Definite description operator.
* `ZFSet.isOrdinal_notMem_univ`: The Burali-Forti paradox. Ordinals form a proper class.
-/

@[expose] public section


universe u

/-- The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automatically. However, in
practice, we treat it as (the definitionally equal) `ZFSet → Prop`. This means, the preferred way to
state that `x : ZFSet` belongs to `A : Class` is to write `A x`. -/
@[pp_with_univ, use_set_notation_for_order]
/--
Definition of `Class` / `Class` 的定义

English:
definition Class
  body: Set ZFSet deriving LE, EmptyCollection, Nonempty, Union, Inter, Compl, SDiff

中文:
定义 类
  定义体: Set ZFSet deriving LE, EmptyCollection, Nonempty, Union, Inter, Compl, SDiff

Depends on / 依赖: EmptyCollection, Nonempty, deriving
-/
def Class :=
  Set ZFSet deriving LE, EmptyCollection, Nonempty, Union, Inter, Compl, SDiff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert ZFSet Class
  body: ⟨Set.insert⟩

中文:
实例 :
  签名: Insert ZFSet 类
  定义体: ⟨Set.insert⟩

Depends on / 依赖: Set.insert, insert
-/
instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

-- Porting note: this used to be a `deriving HasSep Set` instance,
-- it should probably be turned into notation.
/--
Definition of `sep` / `sep` 的定义

English:
definition sep
  signature: (p : ZFSet -> Prop) (A : Class)
  body: {y | A y ∧ p y}

@[ext]

中文:
定义 sep
  签名: (p : ZFSet -> 命题) (A : 类)
  定义体: {y | A y ∧ p y}

@[ext]
-/
protected def sep (p : ZFSet -> Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : Class.{u}}
  statement: (forall z : ZFSet.{u}, x z ↔ y z) -> x = y
  proof: Set.ext

中文:
定理 ext
  条件: {x y : 类.{u}}
  结论: (对任意 z : ZFSet.{u}, x z ↔ y z) -> x = y
  证明: Set.ext

Depends on / 依赖: Set.ext
-/
theorem ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> x = y :=
  Set.ext

/-- Coerce a ZFC set into a class -/
@[coe]
/--
Definition of `ofSet` / `ofSet` 的定义

English:
definition ofSet
  signature: (x : ZFSet.{u})
  body: { y | y in x }

中文:
定义 ofSet
  签名: (x : ZFSet.{u})
  定义体: { y | y in x }
-/
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y in x }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe ZFSet Class
  body: ⟨ofSet⟩

中文:
实例 :
  签名: Coe ZFSet 类
  定义体: ⟨ofSet⟩

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.toEDist, toEDist
-/
instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/--
Definition of `univ` / `univ` 的定义

English:
definition univ
  signature: : Class
  body: Set.univ

中文:
定义 univ
  签名: : 类
  定义体: Set.univ

Depends on / 依赖: Set.univ
-/
def univ : Class :=
  Set.univ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top Class
  body: ⟨univ⟩

deriving instance CompleteLattice for Class

中文:
实例 :
  签名: 顶元素 类
  定义体: ⟨univ⟩

deriving instance CompleteLattice for Class
-/
instance : Top Class := ⟨univ⟩

deriving instance CompleteLattice for Class

/--
Definition of `ToSet` / `ToSet` 的定义

English:
definition ToSet
  signature: (B : Class.{u}) (A : Class.{u})
  body: exists x : ZFSet, ↑x = A ∧ B x

中文:
定义 ToSet
  签名: (B : 类.{u}) (A : 类.{u})
  定义体: exists x : ZFSet, ↑x = A ∧ B x
-/
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  exists x : ZFSet, ↑x = A ∧ B x

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (B A : Class.{u})
  body: ToSet.{u} B A

中文:
定义 Mem
  签名: (B A : 类.{u})
  定义体: ToSet.{u} B A
-/
protected def Mem (B A : Class.{u}) : Prop :=
  ToSet.{u} B A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership Class Class
  body: ⟨Class.Mem⟩

中文:
实例 :
  签名: Membership 类 类
  定义体: ⟨Class.Mem⟩

Depends on / 依赖: Class.Mem
-/
instance : Membership Class Class :=
  ⟨Class.Mem⟩

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  given: (A B : Class.{u})
  statement: A in B ↔ exists x : ZFSet, ↑x = A ∧ B x
  proof: Iff.rfl

@[simp]

中文:
定理 mem_def
  条件: (A B : 类.{u})
  结论: A in B ↔ 存在 x : ZFSet, ↑x = A ∧ B x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_def (A B : Class.{u}) : A in B ↔ exists x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl

@[simp]
/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (x : Class.{u})
  statement: x ∉ (∅ : Class.{u})
  proof: fun ⟨_, _, h⟩ => h

@[simp]

中文:
定理 notMem_empty
  条件: (x : 类.{u})
  结论: x ∉ (∅ : 类.{u})
  证明: fun ⟨_, _, h⟩ => h

@[simp]
-/
theorem notMem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[simp]
/--
theorem `not_empty_hom` / 定理 `not_empty_hom`

English:
theorem not_empty_hom
  given: (x : ZFSet.{u})
  statement: ¬(∅ : Class.{u}) x
  proof: id

@[simp]

中文:
定理 not_empty_hom
  条件: (x : ZFSet.{u})
  结论: ¬(∅ : 类.{u}) x
  证明: id

@[simp]
-/
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id

@[simp]
/--
theorem `mem_univ` / 定理 `mem_univ`

English:
theorem mem_univ
  given: {A : Class.{u}}
  statement: A in univ.{u} ↔ exists x : ZFSet.{u}, ↑x = A
  proof: exists_congr fun _ => iff_of_eq (and_true _)

@[simp]

中文:
定理 mem_univ
  条件: {A : 类.{u}}
  结论: A in univ.{u} ↔ 存在 x : ZFSet.{u}, ↑x = A
  证明: exists_congr fun _ => iff_of_eq (and_true _)

@[simp]

Depends on / 依赖: and_true, exists_congr, iff_of_eq
-/
theorem mem_univ {A : Class.{u}} : A in univ.{u} ↔ exists x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[simp]
/--
theorem `mem_univ_hom` / 定理 `mem_univ_hom`

English:
theorem mem_univ_hom
  given: (x : ZFSet.{u})
  statement: univ.{u} x
  proof: trivial

中文:
定理 mem_univ_hom
  条件: (x : ZFSet.{u})
  结论: univ.{u} x
  证明: trivial
-/
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial

/--
theorem `eq_univ_iff_forall` / 定理 `eq_univ_iff_forall`

English:
theorem eq_univ_iff_forall
  given: {A : Class.{u}}
  statement: A = univ ↔ forall x : ZFSet, A x
  proof: Set.eq_univ_iff_forall

中文:
定理 eq_univ_iff_对任意
  条件: {A : 类.{u}}
  结论: A = univ ↔ 对任意 x : ZFSet, A x
  证明: Set.eq_univ_iff_forall

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall
-/
theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ forall x : ZFSet, A x :=
  Set.eq_univ_iff_forall

/--
theorem `eq_univ_of_forall` / 定理 `eq_univ_of_forall`

English:
theorem eq_univ_of_forall
  given: {A : Class.{u}}
  statement: (forall x : ZFSet, A x) -> A = univ
  proof: Set.eq_univ_of_forall

中文:
定理 eq_univ_of_对任意
  条件: {A : 类.{u}}
  结论: (对任意 x : ZFSet, A x) -> A = univ
  证明: Set.eq_univ_of_forall

Depends on / 依赖: Set.eq_univ_of_forall, eq_univ_of_forall
-/
theorem eq_univ_of_forall {A : Class.{u}} : (forall x : ZFSet, A x) -> A = univ :=
  Set.eq_univ_of_forall

/--
theorem `mem_wf` / 定理 `mem_wf`

English:
theorem mem_wf
  statement: @WellFounded Class.{u} (· in ·)
  proof: ⟨by
    have H : forall x : ZFSet.{u}, @Acc Class.{u} (· in ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

中文:
定理 mem_wf
  结论: @良基 类.{u} (· in ·)
  证明: ⟨by
    have H : forall x : ZFSet.{u}, @Acc Class.{u} (· in ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

Depends on / 依赖: ZFSet.inductionOn, inductionOn
-/
theorem mem_wf : @WellFounded Class.{u} (· in ·) :=
  ⟨by
    have H : forall x : ZFSet.{u}, @Acc Class.{u} (· in ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsWellFounded Class (· in ·)
  body: ⟨mem_wf⟩

中文:
实例 :
  签名: 是良基 类 (· in ·)
  定义体: ⟨mem_wf⟩

Depends on / 依赖: mem_wf
-/
instance : IsWellFounded Class (· in ·) :=
  ⟨mem_wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation Class
  body: ⟨_, mem_wf⟩

中文:
实例 :
  签名: 良基关系 类
  定义体: ⟨_, mem_wf⟩

Depends on / 依赖: NNDist, PseudoMetricSpace, PseudoMetricSpace.toNNDist, mem_wf, toNNDist
-/
instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩

/--
theorem `mem_asymm` / 定理 `mem_asymm`

English:
theorem mem_asymm
  given: {x y : Class}
  statement: x in y -> y ∉ x
  proof: asymm_of (· in ·)

中文:
定理 mem_asymm
  条件: {x y : 类}
  结论: x in y -> y ∉ x
  证明: asymm_of (· in ·)

Depends on / 依赖: asymm_of
-/
theorem mem_asymm {x y : Class} : x in y -> y ∉ x :=
  asymm_of (· in ·)

/--
theorem `mem_irrefl` / 定理 `mem_irrefl`

English:
theorem mem_irrefl
  given: (x : Class)
  statement: x ∉ x
  proof: irrefl_of (· in ·) x

中文:
定理 mem_irrefl
  条件: (x : 类)
  结论: x ∉ x
  证明: irrefl_of (· in ·) x

Depends on / 依赖: irrefl_of
-/
theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl_of (· in ·) x

/--
theorem `univ_notMem_univ` / 定理 `univ_notMem_univ`

English:
theorem univ_notMem_univ
  statement: univ ∉ univ
  proof: mem_irrefl _

中文:
定理 univ_notMem_univ
  结论: univ ∉ univ
  证明: mem_irrefl _

Depends on / 依赖: mem_irrefl
-/
theorem univ_notMem_univ : univ ∉ univ :=
  mem_irrefl _

/--
Definition of `congToClass` / `congToClass` 的定义

English:
definition congToClass
  signature: (x : Set Class.{u})
  body: { y | ↑y in x }

@[simp]

中文:
定义 congToClass
  签名: (x : 集合 类.{u})
  定义体: { y | ↑y in x }

@[simp]
-/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y in x }

@[simp]
/--
theorem `congToClass_empty` / 定理 `congToClass_empty`

English:
theorem congToClass_empty
  statement: congToClass ∅ = ∅
  proof: by
  rfl

中文:
定理 congToClass_empty
  结论: congToClass ∅ = ∅
  证明: by
  rfl
-/
theorem congToClass_empty : congToClass ∅ = ∅ := by
  rfl

/--
Definition of `classToCong` / `classToCong` 的定义

English:
definition classToCong
  signature: (x : Class.{u})
  body: { y | y in x }

@[simp]

中文:
定义 classToCong
  签名: (x : 类.{u})
  定义体: { y | y in x }

@[simp]
-/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y in x }

@[simp]
/--
theorem `classToCong_empty` / 定理 `classToCong_empty`

English:
theorem classToCong_empty
  statement: classToCong ∅ = ∅
  proof: by
  simp [classToCong]

中文:
定理 classToCong_empty
  结论: classToCong ∅ = ∅
  证明: by
  simp [classToCong]

Depends on / 依赖: classToCong
-/
theorem classToCong_empty : classToCong ∅ = ∅ := by
  simp [classToCong]

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (x : Class)
  body: congToClass (Set.powerset x)

中文:
定义 powerset
  签名: (x : 类)
  定义体: congToClass (Set.powerset x)

Depends on / 依赖: Set.powerset, congToClass, powerset
-/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)

/--
Definition of `sUnion` / `sUnion` 的定义

English:
definition sUnion
  signature: (x : Class)
  body: sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

中文:
定义 集合并集
  签名: (x : 类)
  定义体: sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

Depends on / 依赖: classToCong
-/
def sUnion (x : Class) : Class :=
  sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

/--
Definition of `sInter` / `sInter` 的定义

English:
definition sInter
  signature: (x : Class)
  body: sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter

中文:
定义 集合交集
  签名: (x : 类)
  定义体: sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter

Depends on / 依赖: classToCong
-/
def sInter (x : Class) : Class :=
  sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter

/--
theorem `ofSet.inj` / 定理 `ofSet.inj`

English:
theorem ofSet.inj
  given: {x y : ZFSet.{u}} (h : (x : Class.{u}) = y)
  statement: x = y
  proof: ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]

中文:
定理 ofSet.inj
  条件: {x y : ZFSet.{u}} (h : (x : 类.{u}) = y)
  结论: x = y
  证明: ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]

Depends on / 依赖: ZFSet.ext
-/
theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]
/--
theorem `toSet_of_ZFSet` / 定理 `toSet_of_ZFSet`

English:
theorem toSet_of_ZFSet
  given: (A : Class.{u}) (x : ZFSet.{u})
  statement: ToSet A x ↔ A x
  proof: ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]

中文:
定理 toSet_of_ZFSet
  条件: (A : 类.{u}) (x : ZFSet.{u})
  结论: ToSet A x ↔ A x
  证明: ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]

Depends on / 依赖: ofSet.inj
-/
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]
/--
theorem `coe_mem` / 定理 `coe_mem`

English:
theorem coe_mem
  given: {x : ZFSet.{u}} {A : Class.{u}}
  statement: ↑x in A ↔ A x
  proof: toSet_of_ZFSet _ _

@[simp]

中文:
定理 coe_mem
  条件: {x : ZFSet.{u}} {A : 类.{u}}
  结论: ↑x in A ↔ A x
  证明: toSet_of_ZFSet _ _

@[simp]

Depends on / 依赖: toSet_of_ZFSet
-/
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x :=
  toSet_of_ZFSet _ _

@[simp]
/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: {x y : ZFSet.{u}}
  statement: (y : Class.{u}) x ↔ x in y
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_apply
  条件: {x y : ZFSet.{u}}
  结论: (y : 类.{u}) x ↔ x in y
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in y :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_subset` / 定理 `coe_subset`

English:
theorem coe_subset
  given: (x y : ZFSet.{u})
  statement: (x : Class.{u}) subseteq y ↔ x subseteq y
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_subset
  条件: (x y : ZFSet.{u})
  结论: (x : 类.{u}) subseteq y ↔ x subseteq y
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) subseteq y ↔ x subseteq y :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_sep` / 定理 `coe_sep`

English:
theorem coe_sep
  given: (p : Class.{u}) (x : ZFSet.{u})
  proof: ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]

中文:
定理 coe_sep
  条件: (p : 类.{u}) (x : ZFSet.{u})
  证明: ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]

Depends on / 依赖: ZFSet.mem_sep, mem_sep
-/
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y in x | p y } :=
  ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]
/--
theorem `coe_empty` / 定理 `coe_empty`

English:
theorem coe_empty
  statement: ↑(∅ : ZFSet.{u}) = (∅ : Class.{u})
  proof: ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[simp, norm_cast]

中文:
定理 coe_empty
  结论: ↑(∅ : ZFSet.{u}) = (∅ : 类.{u})
  证明: ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[simp, norm_cast]

Depends on / 依赖: ZFSet.notMem_empty, iff_false, notMem_empty
-/
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[simp, norm_cast]
/--
theorem `coe_insert` / 定理 `coe_insert`

English:
theorem coe_insert
  given: (x y : ZFSet.{u})
  statement: ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y
  proof: ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]

中文:
定理 coe_insert
  条件: (x y : ZFSet.{u})
  结论: ↑(insert x y) = @insert ZFSet.{u} 类.{u} _ x y
  证明: ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]

Depends on / 依赖: ZFSet.mem_insert_iff, mem_insert_iff
-/
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]
/--
theorem `coe_union` / 定理 `coe_union`

English:
theorem coe_union
  given: (x y : ZFSet.{u})
  statement: ↑(x union y) = (x : Class.{u}) union y
  proof: ext fun _ => ZFSet.mem_union

@[simp, norm_cast]

中文:
定理 coe_union
  条件: (x y : ZFSet.{u})
  结论: ↑(x union y) = (x : 类.{u}) union y
  证明: ext fun _ => ZFSet.mem_union

@[simp, norm_cast]

Depends on / 依赖: ZFSet.mem_union, mem_union
-/
theorem coe_union (x y : ZFSet.{u}) : ↑(x union y) = (x : Class.{u}) union y :=
  ext fun _ => ZFSet.mem_union

@[simp, norm_cast]
/--
theorem `coe_inter` / 定理 `coe_inter`

English:
theorem coe_inter
  given: (x y : ZFSet.{u})
  statement: ↑(x inter y) = (x : Class.{u}) inter y
  proof: ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]

中文:
定理 coe_inter
  条件: (x y : ZFSet.{u})
  结论: ↑(x inter y) = (x : 类.{u}) inter y
  证明: ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]

Depends on / 依赖: ZFSet.mem_inter, mem_inter
-/
theorem coe_inter (x y : ZFSet.{u}) : ↑(x inter y) = (x : Class.{u}) inter y :=
  ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: (x y : ZFSet.{u})
  statement: ↑(x \ y) = (x : Class.{u}) \ y
  proof: ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[simp, norm_cast]

中文:
定理 coe_sdiff
  条件: (x y : ZFSet.{u})
  结论: ↑(x \ y) = (x : 类.{u}) \ y
  证明: ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[simp, norm_cast]

Depends on / 依赖: ZFSet.mem_sdiff, mem_sdiff
-/
theorem coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[simp, norm_cast]
/--
theorem `coe_powerset` / 定理 `coe_powerset`

English:
theorem coe_powerset
  given: (x : ZFSet.{u})
  statement: ↑x.powerset = powerset.{u} x
  proof: ext fun _ => ZFSet.mem_powerset

@[simp]

中文:
定理 coe_powerset
  条件: (x : ZFSet.{u})
  结论: ↑x.powerset = powerset.{u} x
  证明: ext fun _ => ZFSet.mem_powerset

@[simp]

Depends on / 依赖: ZFSet.mem_powerset, mem_powerset
-/
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[simp]
/--
theorem `powerset_apply` / 定理 `powerset_apply`

English:
theorem powerset_apply
  given: {A : Class.{u}} {x : ZFSet.{u}}
  statement: powerset A x ↔ ↑x subseteq A
  proof: Iff.rfl

@[simp]

中文:
定理 powerset_apply
  条件: {A : 类.{u}} {x : ZFSet.{u}}
  结论: powerset A x ↔ ↑x subseteq A
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x subseteq A :=
  Iff.rfl

@[simp]
/--
theorem `sUnion_apply` / 定理 `sUnion_apply`

English:
theorem sUnion_apply
  given: {x : Class} {y : ZFSet}
  statement: (⋃₀ x) y ↔ exists z : ZFSet, x z ∧ y in z
  proof: by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

中文:
定理 sUnion_apply
  条件: {x : 类} {y : ZFSet}
  结论: (⋃₀ x) y ↔ 存在 z : ZFSet, x z ∧ y in z
  证明: by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

Depends on / 依赖: coe_mem
-/
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ exists z : ZFSet, x z ∧ y in z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

open scoped ZFSet in
@[simp, norm_cast]
/--
theorem `coe_sUnion` / 定理 `coe_sUnion`

English:
theorem coe_sUnion
  given: (x : ZFSet.{u})
  statement: ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u})
  proof: ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]

中文:
定理 coe_sUnion
  条件: (x : ZFSet.{u})
  结论: ↑(⋃₀ x : ZFSet) = ⋃₀ (x : 类.{u})
  证明: ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]

Depends on / 依赖: ZFSet.mem_sUnion.trans, mem_sUnion, sUnion_apply, sUnion_apply.trans
-/
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]
/--
theorem `mem_sUnion` / 定理 `mem_sUnion`

English:
theorem mem_sUnion
  given: {x y : Class.{u}}
  statement: y in ⋃₀ x ↔ exists z, z in x ∧ y in z
  proof: by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

中文:
定理 mem_sUnion
  条件: {x y : 类.{u}}
  结论: y in ⋃₀ x ↔ 存在 z, z in x ∧ y in z
  证明: by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

Depends on / 依赖: coe_mem
-/
theorem mem_sUnion {x y : Class.{u}} : y in ⋃₀ x ↔ exists z, z in x ∧ y in z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩

/--
theorem `sInter_apply` / 定理 `sInter_apply`

English:
theorem sInter_apply
  given: {x : Class.{u}} {y : ZFSet.{u}}
  statement: (⋂₀ x) y ↔ forall z : ZFSet.{u}, x z -> y in z
  proof: by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

中文:
定理 s整数er_apply
  条件: {x : 类.{u}} {y : ZFSet.{u}}
  结论: (⋂₀ x) y ↔ 对任意 z : ZFSet.{u}, x z -> y in z
  证明: by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz
-/
theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ forall z : ZFSet.{u}, x z -> y in z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

open scoped ZFSet in
@[simp, norm_cast]
/--
theorem `coe_sInter` / 定理 `coe_sInter`

English:
theorem coe_sInter
  given: {x : ZFSet.{u}} (h : x.Nonempty)
  statement: ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u})
  proof: Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

中文:
定理 coe_s整数er
  条件: {x : ZFSet.{u}} (h : x.非空)
  结论: ↑(⋂₀ x : ZFSet) = ⋂₀ (x : 类.{u})
  证明: Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

Depends on / 依赖: Set.ext, ZFSet.mem_sInter, mem_sInter, sInter_apply, sInter_apply.symm
-/
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm

/--
theorem `mem_of_mem_sInter` / 定理 `mem_of_mem_sInter`

English:
theorem mem_of_mem_sInter
  given: {x y z : Class} (hy : y in ⋂₀ x) (hz : z in x)
  statement: y in z
  proof: by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

中文:
定理 mem_of_mem_s整数er
  条件: {x y z : 类} (hy : y in ⋂₀ x) (hz : z in x)
  结论: y in z
  证明: by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

Depends on / 依赖: coe_mem
-/
theorem mem_of_mem_sInter {x y z : Class} (hy : y in ⋂₀ x) (hz : z in x) : y in z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)

/--
theorem `mem_sInter` / 定理 `mem_sInter`

English:
theorem mem_sInter
  given: {x y : Class.{u}} (h : x.Nonempty)
  statement: y in ⋂₀ x ↔ forall z, z in x -> y in z
  proof: by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]

中文:
定理 mem_s整数er
  条件: {x y : 类.{u}} (h : x.非空)
  结论: y in ⋂₀ x ↔ 对任意 z, z in x -> y in z
  证明: by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]

Depends on / 依赖: coe_apply, coe_mem, mem_def, mem_of_mem_sInter, sInter_apply, simp_rw
-/
theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y in ⋂₀ x ↔ forall z, z in x -> y in z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]
/--
theorem `sUnion_empty` / 定理 `sUnion_empty`

English:
theorem sUnion_empty
  statement: ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u})
  proof: by
  ext
  simp

@[simp]

中文:
定理 sUnion_empty
  结论: ⋃₀ (∅ : 类.{u}) = (∅ : 类.{u})
  证明: by
  ext
  simp

@[simp]
-/
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[simp]
/--
theorem `sInter_empty` / 定理 `sInter_empty`

English:
theorem sInter_empty
  statement: ⋂₀ (∅ : Class.{u}) = univ
  proof: by
  simp [sInter, Top.top]

中文:
定理 s整数er_empty
  结论: ⋂₀ (∅ : 类.{u}) = univ
  证明: by
  simp [sInter, Top.top]

Depends on / 依赖: Top.top, sInter
-/
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  simp [sInter, Top.top]

/--
theorem `eq_univ_of_powerset_subset` / 定理 `eq_univ_of_powerset_subset`

English:
theorem eq_univ_of_powerset_subset
  given: {A : Class} (hA : powerset A subseteq A)
  statement: A = univ
  proof: eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
WellFounded.not_lt_min ZFSet.mem_wf _ hB coe_apply.1 hx))

中文:
定理 eq_univ_of_powerset_subset
  条件: {A : 类} (hA : powerset A subseteq A)
  结论: A = univ
  证明: eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
WellFounded.not_lt_min ZFSet.mem_wf _ hB coe_apply.1 hx))

Depends on / 依赖: Classical, Classical.not_not, WellFounded, WellFounded.min_mem, WellFounded.not_lt_min, ZFSet.mem_wf, coe_apply, eq_univ_of_forall, mem_wf, min_mem, not_lt_min, not_not
-/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A subseteq A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
WellFounded.not_lt_min ZFSet.mem_wf _ hB coe_apply.1 hx))

/--
Definition of `iota` / `iota` 的定义

English:
definition iota
  signature: (A : Class)
  body: ⋃₀ ({ x | forall y, A y ↔ y = x } : Class)

中文:
定义 iota
  签名: (A : 类)
  定义体: ⋃₀ ({ x | forall y, A y ↔ y = x } : Class)
-/
def iota (A : Class) : Class :=
  ⋃₀ ({ x | forall y, A y ↔ y = x } : Class)

/--
theorem `iota_val` / 定理 `iota_val`

English:
theorem iota_val
  given: (A : Class) (x : ZFSet) (H : forall y, A y ↔ y = x)
  statement: iota A = ↑x
  proof: ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

中文:
定理 iota_val
  条件: (A : 类) (x : ZFSet) (H : 对任意 y, A y ↔ y = x)
  结论: iota A = ↑x
  证明: ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩
-/
theorem iota_val (A : Class) (x : ZFSet) (H : forall y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/--
theorem `iota_ex` / 定理 `iota_ex`

English:
theorem iota_ex
  given: (A)
  statement: iota.{u} A in univ.{u}
  proof: mem_univ.2
    Or.elim (Classical.em <| exists x, forall y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

中文:
定理 iota_ex
  条件: (A)
  结论: iota.{u} A in univ.{u}
  证明: mem_univ.2
    Or.elim (Classical.em <| exists x, forall y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

Depends on / 依赖: Classical, Classical.em, Eq.symm, False.rec, Or.elim, coe_empty, coe_empty.symm, iota_val, mem_univ
-/
theorem iota_ex (A) : iota.{u} A in univ.{u} :=
mem_univ.2
    Or.elim (Classical.em <| exists x, forall y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/--
Definition of `fval` / `fval` 的定义

English:
definition fval
  signature: (F A : Class.{u})
  body: iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval

中文:
定义 fval
  签名: (F A : 类.{u})
  定义体: iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval

Depends on / 依赖: ZFSet.pair
-/
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval

/--
theorem `fval_ex` / 定理 `fval_ex`

English:
theorem fval_ex
  given: (F A : Class.{u})
  statement: F ′ A in univ.{u}
  proof: iota_ex _

中文:
定理 fval_ex
  条件: (F A : 类.{u})
  结论: F ′ A in univ.{u}
  证明: iota_ex _

Depends on / 依赖: iota_ex
-/
theorem fval_ex (F A : Class.{u}) : F ′ A in univ.{u} :=
  iota_ex _

end Class

namespace ZFSet

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `map_fval` / 定理 `map_fval`

English:
theorem map_fval
  statement: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
  proof: Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet]; rw [Class.coe_apply]; rw [mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw]; rw [wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

中文:
定理 map_fval
  结论: {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
  证明: Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet]; rw [Class.coe_apply]; rw [mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw]; rw [wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

Depends on / 依赖: Class.coe_apply, Class.iota_val, Class.toSet_of_ZFSet, ZFSet.pair_injective, coe_apply, iota_val, mem_map, pair_injective, toSet_of_ZFSet
-/
theorem map_fval {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
    (h : y in x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet]; rw [Class.coe_apply]; rw [mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw]; rw [wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

variable (x : ZFSet.{u})

/--
Definition of `choice` / `choice` 的定义

English:
definition choice
  signature: : ZFSet
  body: @map (fun y => Classical.epsilon fun z => z in y) (Classical.allZFSetDefinable _) x

中文:
定义 choice
  签名: : ZFSet
  定义体: @map (fun y => Classical.epsilon fun z => z in y) (Classical.allZFSetDefinable _) x

Depends on / 依赖: Classical, Classical.allZFSetDefinable, Classical.epsilon, allZFSetDefinable, epsilon
-/
noncomputable def choice : ZFSet :=
  @map (fun y => Classical.epsilon fun z => z in y) (Classical.allZFSetDefinable _) x

/--
theorem `choice_mem_aux` / 定理 `choice_mem_aux`

English:
theorem choice_mem_aux
  given: (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x)
  proof: (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z in y)
by_contradiction fun n => h by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

中文:
定理 choice_mem_aux
  条件: (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x)
  证明: (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z in y)
by_contradiction fun n => h by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

Depends on / 依赖: Classical, Classical.epsilon_spec, by_contradiction, epsilon_spec, eq_empty
-/
theorem choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x) :
    (Classical.epsilon fun z : ZFSet.{u} => z in y) in y :=
(@Classical.epsilon_spec _ fun z : ZFSet.{u} => z in y)
by_contradiction fun n => h by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]

/--
theorem `choice_isFunc` / 定理 `choice_isFunc`

English:
theorem choice_isFunc
  given: (h : ∅ ∉ x)
  statement: IsFunc x (⋃₀ x) (choice x)
  proof: (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

中文:
定理 choice_isFunc
  条件: (h : ∅ ∉ x)
  结论: IsFunc x (⋃₀ x) (choice x)
  证明: (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

Depends on / 依赖: Classical, Classical.allZFSetDefinable, allZFSetDefinable, choice_mem_aux, map_isFunc, mem_sUnion
-/
theorem choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩

/--
theorem `choice_mem` / 定理 `choice_mem`

English:
theorem choice_mem
  given: (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x)
  proof: by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx]; rw [Class.coe_mem]; rw [Class.coe_apply]
  exact choice_mem_aux x h y yx

中文:
定理 choice_mem
  条件: (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x)
  证明: by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx]; rw [Class.coe_mem]; rw [Class.coe_apply]
  exact choice_mem_aux x h y yx

Depends on / 依赖: Class.coe_apply, Class.coe_mem, Classical, Classical.allZFSetDefinable, allZFSetDefinable, choice, choice_mem_aux, coe_apply, coe_mem, map_fval
-/
theorem choice_mem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x) :
    (choice x ′ y : Class.{u}) in (y : Class.{u}) := by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx]; rw [Class.coe_mem]; rw [Class.coe_apply]
  exact choice_mem_aux x h y yx

/--
lemma `coe_equiv_aux` / 引理 `coe_equiv_aux`

English:
lemma coe_equiv_aux
  given: {s : Set ZFSet.{u}} (hs : Small.{u} s)
  proof: by
  ext x
  rw [SetLike.mem_coe]; rw [← mk_out x]; rw [mk_mem_iff]; rw [mk_out]
  refine ⟨?_, fun xs => ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq]; rw [ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]

中文:
引理 coe_equiv_aux
  条件: {s : 集合 ZFSet.{u}} (hs : Small.{u} s)
  证明: by
  ext x
  rw [SetLike.mem_coe]; rw [← mk_out x]; rw [mk_mem_iff]; rw [mk_out]
  refine ⟨?_, fun xs => ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq]; rw [ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]
-/
private lemma coe_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
    (mk <| PSet.mk (Shrink s) fun x => ((equivShrink s).symm x).1.out) = s := by
  ext x
  rw [SetLike.mem_coe]; rw [← mk_out x]; rw [mk_mem_iff]; rw [mk_out]
  refine ⟨?_, fun xs => ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq]; rw [ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]

/-- `SetLike.coe` as an equivalence. -/
@[simps apply_coe]
/--
Definition of `coeEquiv` / `coeEquiv` 的定义

English:
definition coeEquiv
  signature: : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  body: ⟨x, x.small_coe⟩
invFun := fun ⟨s, _⟩ => mk PSet.mk (Shrink s) fun x => ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := private Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
fun s => Subtype.coe_injective coe_equiv_aux s.2
right_inv s := private Subtype.coe_injective coe_equiv_aux s.2

中文:
定义 coeEquiv
  签名: : ZFSet.{u} ≃ {s : 集合 ZFSet.{u} // Small.{u, u+1} s} where
  定义体: ⟨x, x.small_coe⟩
invFun := fun ⟨s, _⟩ => mk PSet.mk (Shrink s) fun x => ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := private Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
fun s => Subtype.coe_injective coe_equiv_aux s.2
right_inv s := private Subtype.coe_injective coe_equiv_aux s.2

Depends on / 依赖: small_coe, x.small_coe
-/
noncomputable def coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x, x.small_coe⟩
invFun := fun ⟨s, _⟩ => mk PSet.mk (Shrink s) fun x => ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := private Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
fun s => Subtype.coe_injective coe_equiv_aux s.2
right_inv s := private Subtype.coe_injective coe_equiv_aux s.2

/--
theorem `isOrdinal_notMem_univ` / 定理 `isOrdinal_notMem_univ`

English:
theorem isOrdinal_notMem_univ
  statement: IsOrdinal ∉ Class.univ.{u}
  proof: by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl x
    rwa [Class.coe_mem, hx]
  refine ⟨fun y hy z hz => ?_, fun hyz hzw hwx => ?_⟩ <;> rw [← Class.coe_apply, hx] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

中文:
定理 isOrdinal_notMem_univ
  结论: 是序数 ∉ 类.univ.{u}
  证明: by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl x
    rwa [Class.coe_mem, hx]
  refine ⟨fun y hy z hz => ?_, fun hyz hzw hwx => ?_⟩ <;> rw [← Class.coe_apply, hx] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

Depends on / 依赖: Class.coe_apply, Class.coe_mem, Class.mem_irrefl, IsOrdinal, coe_apply, coe_mem, exacts, hwx.mem_trans, hy.mem, mem_irrefl, mem_trans
-/
theorem isOrdinal_notMem_univ : IsOrdinal ∉ Class.univ.{u} := by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl x
    rwa [Class.coe_mem, hx]
  refine ⟨fun y hy z hz => ?_, fun hyz hzw hwx => ?_⟩ <;> rw [← Class.coe_apply, hx] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

end ZFSet
