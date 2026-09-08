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
/-
**Class** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Class
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The collection of all classes.
We define `Class` as `Set ZFSet`, as this allows us to get many instances automa
tically. However, in
practice, we treat it as (the definitionally equal) `ZFSet → Prop`. This means, 
the preferred way to
state that `x : ZFSet` belongs to `A : Class` is to write `A x`.
-/
def Class :=
  Set ZFSet deriving LE, EmptyCollection, Nonempty, Union, Inter, Compl, SDiff
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Insert ZFSet Class :=
  ⟨Set.insert⟩

namespace Class

-- Porting note: this used to be a `deriving HasSep Set` instance,
-- it should probably be turned into notation.
/-- `{x ∈ A | p x}` is the class of elements in `A` satisfying `p` -/
/-
**Class.sep** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：(ZFSet.{u_1} → Prop) → Class.{u_1} → Class.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{x ∈ A | p x}` is the class of elements in `A` satisfying `p`
-/
protected def sep (p : ZFSet → Prop) (A : Class) : Class :=
  {y | A y ∧ p y}

@[ext]
/-
**Class.ext** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
  Set.ext

/-- Coerce a ZFC set into a class -/
@[coe]
/-
**Class.ofSet** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：ofSet (x : ZFSet.{u}) : Class.{u}
参数：x : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce a ZFC set into a class
-/
def ofSet (x : ZFSet.{u}) : Class.{u} :=
  { y | y ∈ x }
/-
**Class.** 是 Mathlib 中的一个实例，位于命名空间 `Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ZFSet Class :=
  ⟨ofSet⟩

/-- The universal class -/
/-
**Class.univ** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：univ : Class
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal class
-/
def univ : Class :=
  Set.univ
/-
**Class.** 是 Mathlib 中的一个实例，位于命名空间 `Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top Class := ⟨univ⟩

deriving instance CompleteLattice for Class

/-- Assert that `A` is a ZFC set satisfying `B` -/
/-
**Class.ToSet** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：ToSet (B : Class.{u}) (A : Class.{u}) : Prop
参数：B : Class.{u}；A : Class.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assert that `A` is a ZFC set satisfying `B`
-/
def ToSet (B : Class.{u}) (A : Class.{u}) : Prop :=
  ∃ x : ZFSet, ↑x = A ∧ B x

/-- `A ∈ B` if `A` is a ZFC set which satisfies `B` -/
/-
**Class.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：Class.{u} → Class.{u} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A ∈ B` if `A` is a ZFC set which satisfies `B`
-/
protected def Mem (B A : Class.{u}) : Prop :=
  ToSet.{u} B A
/-
**Class.** 是 Mathlib 中的一个实例，位于命名空间 `Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership Class Class :=
  ⟨Class.Mem⟩
/-
**Class.mem_def** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_def (A B : Class.{u}) : A in B ↔ exists x : ZFSet, ↑x = A ∧ B x
参数：A B : Class.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_def (A B : Class.{u}) : A ∈ B ↔ ∃ x : ZFSet, ↑x = A ∧ B x :=
  Iff.rfl

@[simp]
/-
**Class.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：notMem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u})
参数：x : Class.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_empty (x : Class.{u}) : x ∉ (∅ : Class.{u}) := fun ⟨_, _, h⟩ => h

@[simp]
/-
**Class.not_empty_hom** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x
参数：x : ZFSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_empty_hom (x : ZFSet.{u}) : ¬(∅ : Class.{u}) x :=
  id

@[simp]
/-
**Class.mem_univ** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_univ {A : Class.{u}} : A in univ.{u} ↔ exists x : ZFSet.{u}, ↑x = A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem mem_univ {A : Class.{u}} : A ∈ univ.{u} ↔ ∃ x : ZFSet.{u}, ↑x = A :=
  exists_congr fun _ => iff_of_eq (and_true _)

@[simp]
/-
**Class.mem_univ_hom** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_univ_hom (x : ZFSet.{u}) : univ.{u} x
参数：x : ZFSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_univ_hom (x : ZFSet.{u}) : univ.{u} x :=
  trivial
/-
**Class.eq_univ_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ forall x : ZFSet, A x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem eq_univ_iff_forall {A : Class.{u}} : A = univ ↔ ∀ x : ZFSet, A x :=
  Set.eq_univ_iff_forall
/-
**Class.eq_univ_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：eq_univ_of_forall {A : Class.{u}} : (forall x : ZFSet, A x) -> A = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
-/
theorem eq_univ_of_forall {A : Class.{u}} : (∀ x : ZFSet, A x) → A = univ :=
  Set.eq_univ_of_forall
/-
**Class.mem_wf** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_wf : @WellFounded Class.{u} (· in ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.inductionOn`：inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (f
orall y in x, p y) -> p x) : p x
-/
theorem mem_wf : @WellFounded Class.{u} (· ∈ ·) :=
  ⟨by
    have H : ∀ x : ZFSet.{u}, @Acc Class.{u} (· ∈ ·) ↑x := by
      refine fun a => ZFSet.inductionOn a fun x IH => ⟨_, ?_⟩
      rintro A ⟨z, rfl, hz⟩
      exact IH z hz
    refine fun A => ⟨A, ?_⟩
    rintro B ⟨x, rfl, _⟩
    exact H x⟩
/-
**Class.** 是 Mathlib 中的一个实例，位于命名空间 `Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsWellFounded Class (· ∈ ·) :=
  ⟨mem_wf⟩
/-
**Class.** 是 Mathlib 中的一个实例，位于命名空间 `Class`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation Class :=
  ⟨_, mem_wf⟩
/-
**Class.mem_asymm** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_asymm {x y : Class} : x in y -> y ∉ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `asymm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Asymm r], r
 a b → ¬r b a
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `Class.instIsWellFoundedMem`：IsWellFounded Class.{u_1} fun x1 x2 => x1 ∈ 
x2
-/
theorem mem_asymm {x y : Class} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)
/-
**Class.mem_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_irrefl (x : Class) : x ∉ x
参数：x : Class。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `Function.instIrreflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Ir
refl r], Std.Irrefl (Function.swap r)
· 使用定理 `Std.instIrreflOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r]
, Std.Irrefl r
· 使用定理 `Function.instAsymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asy
mm r], Std.Asymm (Function.swap r)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `Class.instIsWellFoundedMem`：IsWellFounded Class.{u_1} fun x1 x2 => x1 ∈ 
x2
-/
theorem mem_irrefl (x : Class) : x ∉ x :=
  irrefl_of (· ∈ ·) x

/-- **There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is proper (does not
belong to the class of all sets). -/
/-
**Class.univ_notMem_univ** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：univ_notMem_univ : univ ∉ univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.mem_irrefl`：mem_irrefl (x : Class) : x ∉ x

--- 原说明 ---
**There is no universal set.**
This is stated as `univ ∉ univ`, meaning that `univ` (the class of all sets) is 
proper (does not
belong to the class of all sets).
-/
theorem univ_notMem_univ : univ ∉ univ :=
  mem_irrefl _

/-- Convert a conglomerate (a collection of classes) into a class -/
/-
**Class.congToClass** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：congToClass (x : Set Class.{u}) : Class.{u}
参数：x : Set Class.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a conglomerate (a collection of classes) into a class
-/
def congToClass (x : Set Class.{u}) : Class.{u} :=
  { y | ↑y ∈ x }

@[simp]
/-
**Class.congToClass_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：congToClass_empty : congToClass ∅ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congToClass_empty : congToClass ∅ = ∅ := by
  rfl

/-- Convert a class into a conglomerate (a collection of classes) -/
/-
**Class.classToCong** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：classToCong (x : Class.{u}) : Set Class.{u}
参数：x : Class.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a class into a conglomerate (a collection of classes)
-/
def classToCong (x : Class.{u}) : Set Class.{u} :=
  { y | y ∈ x }

@[simp]
/-
**Class.classToCong_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：classToCong_empty : classToCong ∅ = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem classToCong_empty : classToCong ∅ = ∅ := by
  simp [classToCong]

/-- The power class of a class is the class of all subclasses that are ZFC sets -/
/-
**Class.powerset** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：powerset (x : Class) : Class
参数：x : Class。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power class of a class is the class of all subclasses that are ZFC sets
-/
def powerset (x : Class) : Class :=
  congToClass (Set.powerset x)

/-- The union of a class is the class of all members of ZFC sets in the class. Uses `⋃₀` notation,
scoped under the `Class` namespace. -/
/-
**Class.sUnion** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：sUnion (x : Class) : Class
参数：x : Class。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of a class is the class of all members of ZFC sets in the class. Uses 
`⋃₀` notation,
scoped under the `Class` namespace.
-/
def sUnion (x : Class) : Class :=
  sSup (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋃₀ " => Class.sUnion

/-- The intersection of a class is the class of all members of ZFC sets in the class .
Uses `⋂₀` notation, scoped under the `Class` namespace. -/
/-
**Class.sInter** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：sInter (x : Class) : Class
参数：x : Class。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection of a class is the class of all members of ZFC sets in the class
 .
Uses `⋂₀` notation, scoped under the `Class` namespace.
-/
def sInter (x : Class) : Class :=
  sInf (classToCong x)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => Class.sInter
/-
**Class.ofSet.inj** 是 Mathlib 中的一个定理，位于命名空间 `Class.ofSet`。
形式化陈述：∀ {x y : ZFSet.{u}}, ↑x = ↑y → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofSet.inj {x y : ZFSet.{u}} (h : (x : Class.{u}) = y) : x = y :=
  ZFSet.ext fun z => by
    change (x : Class.{u}) z ↔ (y : Class.{u}) z
    rw [h]

@[simp]
/-
**Class.toSet_of_ZFSet** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x
参数：A : Class.{u}；x : ZFSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Class.ofSet.inj`：∀ {x y : ZFSet.{u}}, ↑x = ↑y → x = y
-/
theorem toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : ToSet A x ↔ A x :=
  ⟨fun ⟨y, yx, py⟩ => by rwa [ofSet.inj yx] at py, fun px => ⟨x, rfl, px⟩⟩

@[simp, norm_cast]
/-
**Class.coe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.toSet_of_ZFSet`：toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : T
oSet A x ↔ A x
-/
theorem coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x ∈ A ↔ A x :=
  toSet_of_ZFSet _ _

@[simp]
/-
**Class.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x ∈ y :=
  Iff.rfl

@[simp, norm_cast]
/-
**Class.coe_subset** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) subseteq y ↔ x subseteq y
参数：x y : ZFSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_subset (x y : ZFSet.{u}) : (x : Class.{u}) ⊆ y ↔ x ⊆ y :=
  Iff.rfl

@[simp, norm_cast]
/-
**Class.coe_sep** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_sep (p : Class.{u}) (x : ZFSet.{u}) : (ZFSet.sep p x : Class) = { y in
 x | p y }
参数：p : Class.{u}；x : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_sep`：mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} : y in 
ZFSet.sep p x ↔ y in x ∧ p y
-/
theorem coe_sep (p : Class.{u}) (x : ZFSet.{u}) :
    (ZFSet.sep p x : Class) = { y ∈ x | p y } :=
  ext fun _ => ZFSet.mem_sep

@[simp, norm_cast]
/-
**Class.coe_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
-/
theorem coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u}) :=
  ext fun y => iff_false _ ▸ ZFSet.notMem_empty y

@[simp, norm_cast]
/-
**Class.coe_insert** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u}
 _ x y
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_insert_iff`：mem_insert_iff {x y z : ZFSet.{u}} : x in insert y
 z ↔ x = y ∨ x in z
-/
theorem coe_insert (x y : ZFSet.{u}) : ↑(insert x y) = @insert ZFSet.{u} Class.{u} _ x y :=
  ext fun _ => ZFSet.mem_insert_iff

@[simp, norm_cast]
/-
**Class.coe_union** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_union (x y : ZFSet.{u}) : ↑(x union y) = (x : Class.{u}) union y
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_union`：∀ {x y z : ZFSet.{u}}, z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y
-/
theorem coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (x : Class.{u}) ∪ y :=
  ext fun _ => ZFSet.mem_union

@[simp, norm_cast]
/-
**Class.coe_inter** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_inter (x y : ZFSet.{u}) : ↑(x inter y) = (x : Class.{u}) inter y
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_inter`：∀ {x y z : ZFSet.{u}}, z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y
-/
theorem coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (x : Class.{u}) ∩ y :=
  ext fun _ => ZFSet.mem_inter

@[simp, norm_cast]
/-
**Class.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_sdiff`：∀ {x y z : ZFSet.{u}}, z ∈ x \ y ↔ z ∈ x ∧ z ∉ y
-/
theorem coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (x : Class.{u}) \ y :=
  ext fun _ => ZFSet.mem_sdiff

@[deprecated (since := "2026-06-03")] alias coe_diff := coe_sdiff

@[simp, norm_cast]
/-
**Class.coe_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x
参数：x : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `ZFSet.mem_powerset`：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y
 subseteq x
-/
theorem coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x :=
  ext fun _ => ZFSet.mem_powerset

@[simp]
/-
**Class.powerset_apply** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x subsete
q A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem powerset_apply {A : Class.{u}} {x : ZFSet.{u}} : powerset A x ↔ ↑x ⊆ A :=
  Iff.rfl

@[simp]
/-
**Class.sUnion_apply** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ exists z : ZFSet, x z ∧ 
y in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
-/
theorem sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ∃ z : ZFSet, x z ∧ y ∈ z := by
  constructor
  · rintro ⟨-, ⟨z, rfl, hxz⟩, hyz⟩
    exact ⟨z, hxz, hyz⟩
  · exact fun ⟨z, hxz, hyz⟩ => ⟨_, coe_mem.2 hxz, hyz⟩

open scoped ZFSet in
@[simp, norm_cast]
/-
**Class.coe_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u})
参数：x : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Class.sUnion_apply`：sUnion_apply {x : Class} {y : ZFSet} : (⋃₀ x) y ↔ ex
ists z : ZFSet, x z ∧ y in z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_sUnion (x : ZFSet.{u}) : ↑(⋃₀ x : ZFSet) = ⋃₀ (x : Class.{u}) :=
  ext fun y =>
    ZFSet.mem_sUnion.trans (sUnion_apply.trans <| by rfl).symm

@[simp]
/-
**Class.mem_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_sUnion {x y : Class.{u}} : y in ⋃₀ x ↔ exists z, z in x ∧ y in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
-/
theorem mem_sUnion {x y : Class.{u}} : y ∈ ⋃₀ x ↔ ∃ z, z ∈ x ∧ y ∈ z := by
  constructor
  · rintro ⟨w, rfl, z, hzx, hwz⟩
    exact ⟨z, hzx, coe_mem.2 hwz⟩
  · rintro ⟨w, hwx, z, rfl, hwz⟩
    exact ⟨z, rfl, w, hwx, hwz⟩
/-
**Class.sInter_apply** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ forall z : ZFSet
.{u}, x z -> y in z
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x) y ↔ ∀ z : ZFSet.{u}, x z → y ∈ z := by
  refine ⟨fun hxy z hxz => hxy _ ⟨z, rfl, hxz⟩, ?_⟩
  rintro H - ⟨z, rfl, hxz⟩
  exact H _ hxz

open scoped ZFSet in
@[simp, norm_cast]
/-
**Class.coe_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Cl
ass.{u})
参数：h : x.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ZFSet.mem_sInter`：mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x 
↔ forall z in x, y in z
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Class.sInter_apply`：sInter_apply {x : Class.{u}} {y : ZFSet.{u}} : (⋂₀ x
) y ↔ forall z : ZFSet.{u}, x z -> y in z
-/
theorem coe_sInter {x : ZFSet.{u}} (h : x.Nonempty) : ↑(⋂₀ x : ZFSet) = ⋂₀ (x : Class.{u}) :=
  Set.ext fun _ => (ZFSet.mem_sInter h).trans sInter_apply.symm
/-
**Class.mem_of_mem_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_of_mem_sInter {x y z : Class} (hy : y in ⋂₀ x) (hz : z in x) : y in z
参数：hy : y in ⋂₀ x；hz : z in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
-/
theorem mem_of_mem_sInter {x y z : Class} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  obtain ⟨w, rfl, hw⟩ := hy
  exact coe_mem.2 (hw z hz)
/-
**Class.mem_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y in ⋂₀ x ↔ forall z, z in
 x -> y in z
参数：h : x.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.mem_of_mem_sInter`：mem_of_mem_sInter {x y z : Class} (hy : y in ⋂₀
 x) (hz : z in x) : y in z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mem_sInter {x y : Class.{u}} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z, z ∈ x → y ∈ z := by
  refine ⟨fun hy z => mem_of_mem_sInter hy, fun H => ?_⟩
  simp_rw [mem_def, sInter_apply]
  obtain ⟨z, hz⟩ := h
  obtain ⟨y, rfl, _⟩ := H z (coe_mem.2 hz)
  refine ⟨y, rfl, fun w hxw => ?_⟩
  simpa only [coe_mem, coe_apply] using H w (coe_mem.2 hxw)

@[simp]
/-
**Class.sUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sUnion_empty : ⋃₀ (∅ : Class.{u}) = (∅ : Class.{u}) := by
  ext
  simp

@[simp]
/-
**Class.sInter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：sInter_empty : ⋂₀ (∅ : Class.{u}) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Class.classToCong_empty`：classToCong_empty : classToCong ∅ = ∅
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_empty : ⋂₀ (∅ : Class.{u}) = univ := by
  simp [sInter, Top.top]

/-- An induction principle for sets. If every subset of a class is a member, then the class is
  universal. -/
/-
**Class.eq_univ_of_powerset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：eq_univ_of_powerset_subset {A : Class} (hA : powerset A subseteq A) : A = 
univ
参数：hA : powerset A subseteq A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.eq_univ_of_forall`：eq_univ_of_forall {A : Class.{u}} : (forall x :
 ZFSet, A x) -> A = univ
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `ZFSet.mem_wf`：mem_wf : @WellFounded ZFSet (· in ·)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `Class.coe_apply`：coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in 
y

--- 原说明 ---
An induction principle for sets. If every subset of a class is a member, then th
e class is
  universal.
-/
theorem eq_univ_of_powerset_subset {A : Class} (hA : powerset A ⊆ A) : A = univ :=
  eq_univ_of_forall
    (by
      by_contra! hnA
      exact
        WellFounded.min_mem ZFSet.mem_wf _ hnA
          (hA fun x hx =>
            Classical.not_not.1 fun hB =>
              WellFounded.not_lt_min ZFSet.mem_wf _ hB <| coe_apply.1 hx))

/-- The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` otherwise. -/
/-
**Class.iota** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：iota (A : Class) : Class
参数：A : Class。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definite description operator, which is `{x}` if `{y | A y} = {x}` and `∅` o
therwise.
-/
def iota (A : Class) : Class :=
  ⋃₀ ({ x | ∀ y, A y ↔ y = x } : Class)
/-
**Class.iota_val** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：iota_val (A : Class) (x : ZFSet) (H : forall y, A y ↔ y = x) : iota A = ↑x
参数：A : Class；x : ZFSet；H : forall y, A y ↔ y = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem iota_val (A : Class) (x : ZFSet) (H : ∀ y, A y ↔ y = x) : iota A = ↑x :=
  ext fun y =>
    ⟨fun ⟨_, ⟨x', rfl, h⟩, yx'⟩ => by rwa [← (H x').1 <| (h x').2 rfl], fun yx =>
      ⟨_, ⟨x, rfl, H⟩, yx⟩⟩

/-- Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function. -/
/-
**Class.iota_ex** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：iota_ex (A) : iota.{u} A in univ.{u}
参数：A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Class.mem_univ`：mem_univ {A : Class.{u}} : A in univ.{u} ↔ exists x : ZF
Set.{u}, ↑x = A
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Class.iota_val`：iota_val (A : Class) (x : ZFSet) (H : forall y, A y ↔ y 
= x) : iota A = ↑x
· 使用定理 `Class.ext`：ext {x y : Class.{u}} : (forall z : ZFSet.{u}, x z ↔ y z) -> 
x = y
· 使用定理 `Class.coe_empty`：coe_empty : ↑(∅ : ZFSet.{u}) = (∅ : Class.{u})

--- 原说明 ---
Unlike the other set constructors, the `iota` definite descriptor
  is a set for any set input, but not constructively so, so there is no
  associated `Class → Set` function.
-/
theorem iota_ex (A) : iota.{u} A ∈ univ.{u} :=
  mem_univ.2 <|
    Or.elim (Classical.em <| ∃ x, ∀ y, A y ↔ y = x) (fun ⟨x, h⟩ => ⟨x, Eq.symm <| iota_val A x h⟩)
      fun hn =>
      ⟨∅, ext fun _ => coe_empty.symm ▸ ⟨False.rec, fun ⟨_, ⟨x, rfl, H⟩, _⟩ => hn ⟨x, H⟩⟩⟩

/-- Function value -/
/-
**Class.fval** 是 Mathlib 中的一个定义，位于命名空间 `Class`。
形式化陈述：fval (F A : Class.{u}) : Class.{u}
参数：F A : Class.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function value
-/
def fval (F A : Class.{u}) : Class.{u} :=
  iota fun y => ToSet (fun x => F (ZFSet.pair x y)) A

@[inherit_doc]
infixl:100 " ′ " => fval
/-
**Class.fval_ex** 是 Mathlib 中的一个定理，位于命名空间 `Class`。
形式化陈述：fval_ex (F A : Class.{u}) : F ′ A in univ.{u}
参数：F A : Class.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.iota_ex`：iota_ex (A) : iota.{u} A in univ.{u}
-/
theorem fval_ex (F A : Class.{u}) : F ′ A ∈ univ.{u} :=
  iota_ex _

end Class

namespace ZFSet

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ZFSet.map_fval** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：map_fval {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}} (h 
: y in x) : (ZFSet.map f x ′ y : Class.{u}) = f y
参数：h : y in x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Class.iota_val`：iota_val (A : Class) (x : ZFSet) (H : forall y, A y ↔ y 
= x) : iota A = ↑x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Class.toSet_of_ZFSet`：toSet_of_ZFSet (A : Class.{u}) (x : ZFSet.{u}) : T
oSet A x ↔ A x
· 使用定理 `Class.coe_apply`：coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in 
y
· 使用定理 `ZFSet.mem_map`：mem_map {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet}
 : y in map f x ↔ exists z in x, pair z (f z) = y
· 使用定理 `ZFSet.pair_injective`：pair_injective : Function.Injective2 pair
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_fval {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}}
    (h : y ∈ x) : (ZFSet.map f x ′ y : Class.{u}) = f y :=
  Class.iota_val _ _ fun z => by
    rw [Class.toSet_of_ZFSet, Class.coe_apply, mem_map]
    exact
      ⟨fun ⟨w, _, pr⟩ => by
        let ⟨wy, fw⟩ := ZFSet.pair_injective pr
        rw [← fw, wy], fun e => by
        subst e
        exact ⟨_, h, rfl⟩⟩

variable (x : ZFSet.{u})

/-- A choice function on the class of nonempty ZFC sets. -/
/-
**ZFSet.choice** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：choice : ZFSet
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A choice function on the class of nonempty ZFC sets.
-/
noncomputable def choice : ZFSet :=
  @map (fun y => Classical.epsilon fun z => z ∈ y) (Classical.allZFSetDefinable _) x
/-
**ZFSet.choice_mem_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x) : (Classical.epsi
lon fun z : ZFSet.{u} => z in y) in y
参数：h : ∅ ∉ x；y : ZFSet.{u}；yx : y in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.epsilon_spec`：∀ {α : Sort u} {p : α → Prop} (hex : ∃ y, p y), 
p (Classical.epsilon p)
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.eq_empty`：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u},
 y ∉ x
-/
theorem choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (Classical.epsilon fun z : ZFSet.{u} => z ∈ y) ∈ y :=
  (@Classical.epsilon_spec _ fun z : ZFSet.{u} => z ∈ y) <|
    by_contradiction fun n => h <| by rwa [← (eq_empty y).2 fun z zx => n ⟨z, zx⟩]
/-
**ZFSet.choice_isFunc** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x)
参数：h : ∅ ∉ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ZFSet.map_isFunc`：map_isFunc {f : ZFSet -> ZFSet} [Definable₁ f] {x y : 
ZFSet} : IsFunc x y (map f x) ↔ forall z in x, f z in y
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
· 使用定理 `ZFSet.choice_mem_aux`：choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y
 in x) : (Classical.epsilon fun z : ZFSet.{u} => z in y) in y
-/
theorem choice_isFunc (h : ∅ ∉ x) : IsFunc x (⋃₀ x) (choice x) :=
  (@map_isFunc _ (Classical.allZFSetDefinable _) _ _).2 fun y yx =>
    mem_sUnion.2 ⟨y, yx, choice_mem_aux x h y yx⟩
/-
**ZFSet.choice_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：choice_mem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y in x) : (choice x ′ y : Cla
ss.{u}) in (y : Class.{u})
参数：h : ∅ ∉ x；y : ZFSet.{u}；yx : y in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.map_fval`：map_fval {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x 
y : ZFSet.{u}} (h : y in x) : (ZFSet.map f x ′ y : Class.{u}) = f y
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x
· 使用定理 `Class.coe_apply`：coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in 
y
· 使用定理 `ZFSet.choice_mem_aux`：choice_mem_aux (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y
 in x) : (Classical.epsilon fun z : ZFSet.{u} => z in y) in y
-/
theorem choice_mem (h : ∅ ∉ x) (y : ZFSet.{u}) (yx : y ∈ x) :
    (choice x ′ y : Class.{u}) ∈ (y : Class.{u}) := by
  delta choice
  rw [@map_fval _ (Classical.allZFSetDefinable _) x y yx, Class.coe_mem, Class.coe_apply]
  exact choice_mem_aux x h y yx
/-
**ZFSet.coe_equiv_aux** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coe_equiv_aux {s : Set ZFSet.{u}} (hs : Small.{u} s) :
    (mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink s).symm x).1.out) = s := by
  ext x
  rw [SetLike.mem_coe, ← mk_out x, mk_mem_iff, mk_out]
  refine ⟨?_, fun xs ↦ ⟨equivShrink s (Subtype.mk x xs), ?_⟩⟩
  · rintro ⟨b, h2⟩
    rw [← ZFSet.eq, ZFSet.mk_out] at h2
    simp [h2]
  · simp [PSet.Equiv.refl]

/-- `SetLike.coe` as an equivalence. -/
@[simps apply_coe]
/-
**ZFSet.coeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where toFun
 x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`SetLike.coe` as an equivalence.
-/
noncomputable def coeEquiv : ZFSet.{u} ≃ {s : Set ZFSet.{u} // Small.{u, u+1} s} where
  toFun x := ⟨x, x.small_coe⟩
  invFun := fun ⟨s, _⟩ ↦ mk <| PSet.mk (Shrink s) fun x ↦ ((equivShrink.{u, u + 1} s).symm x).1.out
  left_inv := private Function.rightInverse_of_injective_of_leftInverse (by intro _ _; simp)
    fun s ↦ Subtype.coe_injective <| coe_equiv_aux s.2
  right_inv s := private Subtype.coe_injective <| coe_equiv_aux s.2

/-- The **Burali-Forti paradox**: ordinals form a proper class. -/
/-
**ZFSet.isOrdinal_notMem_univ** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isOrdinal_notMem_univ : IsOrdinal ∉ Class.univ.{u}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Class.coe_apply`：coe_apply {x y : ZFSet.{u}} : (y : Class.{u}) x ↔ x in 
y
· 使用定理 `ZFSet.IsOrdinal.mem`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdi
nal
· 使用定理 `ZFSet.IsOrdinal.mem_trans`：mem_trans (h : z.IsOrdinal) : x in y -> y in 
z -> x in z
· 使用定理 `Class.mem_irrefl`：mem_irrefl (x : Class) : x ∉ x
· 使用定理 `Class.coe_mem`：coe_mem {x : ZFSet.{u}} {A : Class.{u}} : ↑x in A ↔ A x

--- 原说明 ---
The **Burali-Forti paradox**: ordinals form a proper class.
-/
theorem isOrdinal_notMem_univ : IsOrdinal ∉ Class.univ.{u} := by
  rintro ⟨x, hx, -⟩
  suffices IsOrdinal x by
    apply Class.mem_irrefl x
    rwa [Class.coe_mem, hx]
  refine ⟨fun y hy z hz ↦ ?_, fun hyz hzw hwx ↦ ?_⟩ <;> rw [← Class.coe_apply, hx] at *
  exacts [hy.mem hz, hwx.mem_trans hyz hzw]

end ZFSet

