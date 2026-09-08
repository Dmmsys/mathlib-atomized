/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot, Wen Yang, Johan Commelin
-/
module

public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Partition.Finpartition

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : Set (Set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `IsPartition c`
* An indexed partition is a map `s : ι → Set α` whose image is a partition. This is
  expressed as `IndexedPartition s`.

Of course both implementations are related to `Quotient` and `Setoid`.

`Setoid.isPartition.partition` and `Finpartition.isPartition_parts` furnish
a link between `Setoid.IsPartition` and `Finpartition`.

## TODO

Could the design of `Finpartition` inform the one of `Setoid.IsPartition`? Maybe bundling it and
changing it from `Set (Set α)` to `Set α` where `[Lattice α] [OrderBot α]` would make it more
usable.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

@[expose] public section


namespace Setoid

variable {α : Type*}

/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
/-
**Setoid.eq_of_mem_eqv_class** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_of_mem_eqv_class {c : Set (Set α)} (H : forall a, exists! b in c, a in 
b) {x b b'} (hc : b in c) (hb : x in b) (hc' : b' in c) (hb' : x in b') : b = b'
参数：Set α；H : forall a, exists! b in c, a in b；hc : b in c；hb : x in b；hc' : b' i
n c；hb' : x in b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂

--- 原说明 ---
If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equa
l.
-/
theorem eq_of_mem_eqv_class {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x b b'}
    (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') : b = b' :=
  (H x).unique ⟨hc, hb⟩ ⟨hc', hb'⟩

/-- Makes an equivalence relation from a set of sets partitioning α. -/
@[instance_reducible]
/-
**Setoid.mkClasses** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：mkClasses (c : Set (Set α)) (H : forall a, exists! b in c, a in b) : Setoi
d α where r x y
参数：c : Set (Set α)；H : forall a, exists! b in c, a in b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes an equivalence relation from a set of sets partitioning α.
-/
def mkClasses (c : Set (Set α)) (H : ∀ a, ∃! b ∈ c, a ∈ b) : Setoid α where
  r x y := ∀ s ∈ c, x ∈ s → y ∈ s
  iseqv.refl := fun _ _ _ hx => hx
  iseqv.symm := fun {x _y} h s hs hy => by
    obtain ⟨t, ⟨ht, hx⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy ht (h t ht hx)]
  iseqv.trans := fun {_x _ _} h1 h2 s hs hx => h2 s hs (h1 s hs hx)

/-- Makes the equivalence classes of an equivalence relation. -/
/-
**Setoid.classes** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：classes (r : Setoid α) : Set (Set α)
参数：r : Setoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes the equivalence classes of an equivalence relation.
-/
def classes (r : Setoid α) : Set (Set α) :=
  { s | ∃ y, s = { x | r x y } }
/-
**Setoid.mem_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：mem_classes (r : Setoid α) (y) : { x | r x y } in r.classes
参数：r : Setoid α；y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_classes (r : Setoid α) (y) : { x | r x y } ∈ r.classes :=
  ⟨y, rfl⟩
/-
**Setoid.classes_ker_subset_fiber_set** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：classes_ker_subset_fiber_set {β : Type*} (f : α -> β) : (Setoid.ker f).cla
sses subseteq Set.range fun y => { x | f x = y }
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem classes_ker_subset_fiber_set {β : Type*} (f : α → β) :
    (Setoid.ker f).classes ⊆ Set.range fun y => { x | f x = y } := by
  rintro s ⟨x, rfl⟩
  rw [Set.mem_range]
  exact ⟨f x, rfl⟩
/-
**Setoid.finite_classes_ker** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：finite_classes_ker {α β : Type*} [Finite β] (f : α -> β) : (Setoid.ker f).
classes.Finite
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Setoid.classes_ker_subset_fiber_set`：classes_ker_subset_fiber_set {β : T
ype*} (f : α -> β) : (Setoid.ker f).classes subseteq Set.range fun y => { x | f 
x = y }
-/
theorem finite_classes_ker {α β : Type*} [Finite β] (f : α → β) : (Setoid.ker f).classes.Finite :=
  (Set.finite_range _).subset <| classes_ker_subset_fiber_set f
/-
**Setoid.card_classes_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：card_classes_ker_le {α β : Type*} [Fintype β] (f : α -> β) [Fintype (Setoi
d.ker f).classes] : Fintype.card (Setoid.ker f).classes <= Fintype.card β
参数：f : α -> β；Setoid.ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.card_le_card`：card_le_card {s t : Set α} [Fintype s] [Fintype t] (hs
ub : s subseteq t) : Fintype.card s <= Fintype.card t
· 使用定理 `Setoid.classes_ker_subset_fiber_set`：classes_ker_subset_fiber_set {β : T
ype*} (f : α -> β) : (Setoid.ker f).classes subseteq Set.range fun y => { x | f 
x = y }
· 使用定理 `Fintype.card_range_le`：card_range_le {α β : Type*} (f : α -> β) [Fintype
 α] [Fintype (Set.range f)] : Fintype.card (Set.range f) <= Fintype.card α
-/
theorem card_classes_ker_le {α β : Type*} [Fintype β] (f : α → β)
    [Fintype (Setoid.ker f).classes] : Fintype.card (Setoid.ker f).classes ≤ Fintype.card β := by
  exact
      le_trans (Set.card_le_card (classes_ker_subset_fiber_set f)) (Fintype.card_range_le _)

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
/-
**Setoid.eq_iff_classes_eq** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_iff_classes_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ forall x, { y | r₁ x y } 
= { y | r₂ x y }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b

--- 原说明 ---
Two equivalence relations are equal iff all their equivalence classes are equal.
-/
theorem eq_iff_classes_eq {r₁ r₂ : Setoid α} :
    r₁ = r₂ ↔ ∀ x, { y | r₁ x y } = { y | r₂ x y } :=
  ⟨fun h _x => h ▸ rfl, fun h => ext fun x => Set.ext_iff.1 <| h x⟩
/-
**Setoid.rel_iff_exists_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：rel_iff_exists_classes (r : Setoid α) {x y} : r x y ↔ exists c in r.classe
s, x in c ∧ y in c
参数：r : Setoid α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.mem_classes`：mem_classes (r : Setoid α) (y) : { x | r x y } in r.
classes
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem rel_iff_exists_classes (r : Setoid α) {x y} : r x y ↔ ∃ c ∈ r.classes, x ∈ c ∧ y ∈ c :=
  ⟨fun h => ⟨_, r.mem_classes y, h, r.refl' y⟩, fun ⟨c, ⟨z, hz⟩, hx, hy⟩ => by
    subst c
    exact r.trans' hx (r.symm' hy)⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
/-
**Setoid.classes_inj** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classes = r₂.classes
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two equivalence relations are equal iff their equivalence classes are equal.
-/
theorem classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classes = r₂.classes :=
  ⟨fun h => h ▸ rfl, fun h => ext fun a b => by simp only [rel_iff_exists_classes, h]⟩

/-- The empty set is not an equivalence class. -/
/-
**Setoid.empty_notMem_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：empty_notMem_classes {r : Setoid α} : ∅ ∉ r.classes
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The empty set is not an equivalence class.
-/
theorem empty_notMem_classes {r : Setoid α} : ∅ ∉ r.classes := fun ⟨y, hy⟩ =>
  Set.notMem_empty y <| hy.symm ▸ r.refl' y

/-- Equivalence classes partition the type. -/
/-
**Setoid.classes_eqv_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：classes_eqv_classes {r : Setoid α} (a) : exists! b in r.classes, a in b
参数：a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.intro`：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w
) (h₂ : forall y, p y -> y = w) : exists! x, p x
· 使用定理 `Setoid.mem_classes`：mem_classes (r : Setoid α) (y) : { x | r x y } in r.
classes
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Equivalence classes partition the type.
-/
theorem classes_eqv_classes {r : Setoid α} (a) : ∃! b ∈ r.classes, a ∈ b :=
  ExistsUnique.intro { x | r x a } ⟨r.mem_classes a, r.refl' _⟩ <| by
    rintro y ⟨⟨_, rfl⟩, ha⟩
    ext x
    exact ⟨fun hx => r.trans' hx (r.symm' ha), fun hx => r.trans' hx ha⟩

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
/-
**Setoid.eq_of_mem_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_of_mem_classes {r : Setoid α} {x b} (hc : b in r.classes) (hb : x in b)
 {b'} (hc' : b' in r.classes) (hb' : x in b') : b = b'
参数：hc : b in r.classes；hb : x in b；hc' : b' in r.classes；hb' : x in b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.eq_of_mem_eqv_class`：eq_of_mem_eqv_class {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {x b b'} (hc : b in c) (hb : x in b) (hc' : b' 
in c) (hb' : x i…
· 使用定理 `Setoid.classes_eqv_classes`：classes_eqv_classes {r : Setoid α} (a) : exi
sts! b in r.classes, a in b

--- 原说明 ---
If x ∈ α is in 2 equivalence classes, the equivalence classes are equal.
-/
theorem eq_of_mem_classes {r : Setoid α} {x b} (hc : b ∈ r.classes) (hb : x ∈ b) {b'}
    (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
  eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
equivalence relation defined by the set of sets. -/
/-
**Setoid.eq_eqv_class_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eq_eqv_class_of_mem {c : Set (Set α)} (H : forall a, exists! b in c, a in 
b) {s y} (hs : s in c) (hy : y in s) : s = { x | mkClasses c H x y }
参数：Set α；H : forall a, exists! b in c, a in b；hs : s in c；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.eq_of_mem_eqv_class`：eq_of_mem_eqv_class {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {x b b'} (hc : b in c) (hb : x in b) (hc' : b' 
in c) (hb' : x i…

--- 原说明 ---
The elements of a set of sets partitioning α are the equivalence classes of the
equivalence relation defined by the set of sets.
-/
theorem eq_eqv_class_of_mem {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {s y}
    (hs : s ∈ c) (hy : y ∈ s) : s = { x | mkClasses c H x y } := by
  ext x
  constructor
  · intro hx _s' hs' hx'
    rwa [eq_of_mem_eqv_class H hs' hx' hs hx]
  · intro hx
    obtain ⟨b', ⟨hc, hb'⟩, _⟩ := H x
    rwa [eq_of_mem_eqv_class H hs hy hc (hx b' hc hb')]

/-- The equivalence classes of the equivalence relation defined by a set of sets
partitioning α are elements of the set of sets. -/
/-
**Setoid.eqv_class_mem** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqv_class_mem {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {y}
 : { x | mkClasses c H x y } in c
参数：Set α；H : forall a, exists! b in c, a in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.elim`：ExistsUnique.elim {p : α -> Prop} {b : Prop} (h₂ : ex
ists! x, p x) (h₁ : forall x, p x -> (forall y, p y -> y = x) -> b) : b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Setoid.eq_eqv_class_of_mem`：eq_eqv_class_of_mem {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {s y} (hs : s in c) (hy : y in s) : s = { x | m
kClasses c H x y…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The equivalence classes of the equivalence relation defined by a set of sets
partitioning α are elements of the set of sets.
-/
theorem eqv_class_mem {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {y} :
    { x | mkClasses c H x y } ∈ c :=
  (H y).elim fun _ hc _ => eq_eqv_class_of_mem H hc.1 hc.2 ▸ hc.1
/-
**Setoid.eqv_class_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqv_class_mem' {c : Set (Set α)} (H : forall a, exists! b in c, a in b) {x
} : { y : α | mkClasses c H x y } in c
参数：Set α；H : forall a, exists! b in c, a in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Setoid.eqv_class_mem`：eqv_class_mem {c : Set (Set α)} (H : forall a, exi
sts! b in c, a in b) {y} : { x | mkClasses c H x y } in c
-/
theorem eqv_class_mem' {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x} :
    { y : α | mkClasses c H x y } ∈ c := by
  convert! @Setoid.eqv_class_mem _ _ H x using 3
  rw [Setoid.comm']

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
/-
**Setoid.eqv_classes_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqv_classes_disjoint {c : Set (Set α)} (H : forall a, exists! b in c, a in
 b) : c.PairwiseDisjoint id
参数：Set α；H : forall a, exists! b in c, a in b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `ExistsUnique.elim`：ExistsUnique.elim {p : α -> Prop} {b : Prop} (h₂ : ex
ists! x, p x) (h₁ : forall x, p x -> (forall y, p y -> y = x) -> b) : b
· 使用定理 `Setoid.eq_of_mem_eqv_class`：eq_of_mem_eqv_class {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {x b b'} (hc : b in c) (hb : x in b) (hc' : b' 
in c) (hb' : x i…

--- 原说明 ---
Distinct elements of a set of sets partitioning α are disjoint.
-/
theorem eqv_classes_disjoint {c : Set (Set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) :
    c.PairwiseDisjoint id := fun _b₁ h₁ _b₂ h₂ h =>
  Set.disjoint_left.2 fun x hx1 hx2 =>
    (H x).elim fun _b _hc _hx => h <| eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/-- A set of disjoint sets covering α partition α (classical). -/
/-
**Setoid.eqv_classes_of_disjoint_union** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.sUnion c = @Set.
univ α) (H : c.PairwiseDisjoint id) (a) : exists! b in c, a in b
参数：Set α；hu : Set.sUnion c = @Set.univ α；H : c.PairwiseDisjoint id；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `ExistsUnique.intro`：ExistsUnique.intro {p : α -> Prop} (w : α) (h₁ : p w
) (h₂ : forall y, p y -> y = w) : exists! x, p x
· 使用定理 `Set.PairwiseDisjoint.elim_set`：∀ {α : Type u_1} {ι : Type u_4} {s : Set 
ι} {f : ι → Set α},   s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ 
f i, a ∈ f j → i = …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A set of disjoint sets covering α partition α (classical).
-/
theorem eqv_classes_of_disjoint_union {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) (a) : ∃! b ∈ c, a ∈ b :=
  let ⟨b, hc, ha⟩ := Set.mem_sUnion.1 <| show a ∈ _ by rw [hu]; exact Set.mem_univ a
  ExistsUnique.intro b ⟨hc, ha⟩ fun _ hc' => H.elim_set hc'.1 hc _ hc'.2 ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
@[instance_reducible]
/-
**Setoid.setoidOfDisjointUnion** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：setoidOfDisjointUnion {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α) 
(H : c.PairwiseDisjoint id) : Setoid α
参数：Set α；hu : Set.sUnion c = @Set.univ α；H : c.PairwiseDisjoint id。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.eqv_classes_of_disjoint_union`：eqv_classes_of_disjoint_union {c :
 Set (Set α)} (hu : Set.sUnion c = @Set.univ α) (H : c.PairwiseDisjoint id) (a) 
: exists! b in c, a in b

--- 原说明 ---
Makes an equivalence relation from a set of disjoints sets covering α.
-/
def setoidOfDisjointUnion {c : Set (Set α)} (hu : Set.sUnion c = @Set.univ α)
    (H : c.PairwiseDisjoint id) : Setoid α :=
  Setoid.mkClasses c <| eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence relation `r`
equals `r`. -/
/-
**Setoid.mkClasses_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：mkClasses_classes (r : Setoid α) : mkClasses r.classes classes_eqv_classes
 = r
参数：r : Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Setoid.classes_eqv_classes`：classes_eqv_classes {r : Setoid α} (a) : exi
sts! b in r.classes, a in b
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Setoid.mem_classes`：mem_classes (r : Setoid α) (y) : { x | r x y } in r.
classes
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Setoid.eq_of_mem_classes`：eq_of_mem_classes {r : Setoid α} {x b} (hc : b
 in r.classes) (hb : x in b) {b'} (hc' : b' in r.classes) (hb' : x in b') : b = 
b'

--- 原说明 ---
The equivalence relation made from the equivalence classes of an equivalence rel
ation `r`
equals `r`.
-/
theorem mkClasses_classes (r : Setoid α) : mkClasses r.classes classes_eqv_classes = r :=
  ext fun x _y =>
    ⟨fun h => r.symm' (h { z | r z x } (r.mem_classes x) <| r.refl' x), fun h _b hb hx =>
      eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp]
/-
**Setoid.sUnion_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：sUnion_classes (r : Setoid α) : ⋃₀ r.classes = Set.univ
参数：r : Setoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem sUnion_classes (r : Setoid α) : ⋃₀ r.classes = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_sUnion.2 ⟨{ y | r y x }, ⟨x, rfl⟩, Setoid.refl _⟩

/-- The equivalence between the quotient by an equivalence relation and its
type of equivalence classes. -/
/-
**Setoid.quotientEquivClasses** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：quotientEquivClasses (r : Setoid α) : Quotient r ≃ Setoid.classes r
参数：r : Setoid α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.mem_classes`：mem_classes (r : Setoid α) (y) : { x | r x y } in r.
classes

--- 原说明 ---
The equivalence between the quotient by an equivalence relation and its
type of equivalence classes.
-/
noncomputable def quotientEquivClasses (r : Setoid α) : Quotient r ≃ Setoid.classes r := by
  let f (a : α) : Setoid.classes r := ⟨{ x | r x a }, Setoid.mem_classes r a⟩
  have f_respects_relation (a b : α) (a_rel_b : r a b) : f a = f b := by
    rw [Subtype.mk.injEq]
    exact Setoid.eq_of_mem_classes (Setoid.mem_classes r a) (Setoid.symm a_rel_b)
        (Setoid.mem_classes r b) (Setoid.refl b)
  apply Equiv.ofBijective (Quot.lift f f_respects_relation)
  constructor
  · intro (q_a : Quotient r) (q_b : Quotient r) h_eq
    induction q_a using Quotient.ind with | _ a
    induction q_b using Quotient.ind with | _ b
    simp only [f, Quotient.lift_mk, Subtype.ext_iff] at h_eq
    apply Quotient.sound
    change a ∈ { x | r x b }
    rw [← h_eq]
    exact Setoid.refl a
  · rw [Quot.surjective_lift]
    intro ⟨c, a, hc⟩
    exact ⟨a, Subtype.ext hc.symm⟩

@[simp]
/-
**Setoid.quotientEquivClasses_mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Setoid`。
形式化陈述：quotientEquivClasses_mk_eq (r : Setoid α) (a : α) : (quotientEquivClasses 
r (Quotient.mk r a) : Set α) = { x | r x a }
参数：r : Setoid α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Setoid.mem_classes`：mem_classes (r : Setoid α) (y) : { x | r x y } in r.
classes
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma quotientEquivClasses_mk_eq (r : Setoid α) (a : α) :
    (quotientEquivClasses r (Quotient.mk r a) : Set α) = { x | r x a } :=
  (@Subtype.ext_iff _ _ _ ⟨{ x | r x a }, Setoid.mem_classes r a⟩).mp rfl

section Partition

/-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
/-
**Setoid.IsPartition** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：IsPartition (c : Set (Set α))
参数：c : Set (Set α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c
`.
-/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b

/-- A partition of `α` does not contain the empty set. -/
/-
**Setoid.nonempty_of_mem_partition** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : 
s in c) : s.Nonempty
参数：Set α；hc : IsPartition c；h : s in c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A partition of `α` does not contain the empty set.
-/
theorem nonempty_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (h : s ∈ c) :
    s.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun hs0 => hc.1 <| hs0 ▸ h
/-
**Setoid.isPartition_classes** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：isPartition_classes (r : Setoid α) : IsPartition r.classes
参数：r : Setoid α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.empty_notMem_classes`：empty_notMem_classes {r : Setoid α} : ∅ ∉ r
.classes
· 使用定理 `Setoid.classes_eqv_classes`：classes_eqv_classes {r : Setoid α} (a) : exi
sts! b in r.classes, a in b
-/
theorem isPartition_classes (r : Setoid α) : IsPartition r.classes :=
  ⟨empty_notMem_classes, classes_eqv_classes⟩
/-
**Setoid.IsPartition.pairwiseDisjoint** 是 Mathlib 中的一个定理，位于命名空间 `Setoid.IsPartit
ion`。
形式化陈述：∀ {α : Type u_1} {c : Set (Set α)}, Setoid.IsPartition c → c.PairwiseDisjo
int id
参数：Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.eqv_classes_disjoint`：eqv_classes_disjoint {c : Set (Set α)} (H :
 forall a, exists! b in c, a in b) : c.PairwiseDisjoint id
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPartition.pairwiseDisjoint {c : Set (Set α)} (hc : IsPartition c) :
    c.PairwiseDisjoint id :=
  eqv_classes_disjoint hc.2
/-
**Setoid._root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty** 是 Mathl
ib 中的一个引理，位于命名空间 `Setoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty {α : Type*} {s : Set (Set α)}
    (h₁ : s.PairwiseDisjoint id) (h₂ : ∀ a : α, ∃ x ∈ s, a ∈ x) (h₃ : ∅ ∉ s) :
    Setoid.IsPartition s := by
  refine ⟨h₃, fun a ↦ existsUnique_of_exists_of_unique (h₂ a) ?_⟩
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩
/-
**Setoid.IsPartition.sUnion_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Setoid.IsPartitio
n`。
形式化陈述：∀ {α : Type u_1} {c : Set (Set α)}, Setoid.IsPartition c → ⋃₀ c = Set.univ
参数：Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_sUnion`：mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exist
s t in S, x in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsPartition.sUnion_eq_univ {c : Set (Set α)} (hc : IsPartition c) : ⋃₀ c = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    Set.mem_sUnion.2 <|
      let ⟨t, ht⟩ := hc.2 x
      ⟨t, by
        simp only at ht
        tauto⟩

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
/-
**Setoid.exists_of_mem_partition** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s
 in c) : exists y, s = { x | mkClasses c hc.2 x y }
参数：Set α；hc : IsPartition c；hs : s in c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Setoid.nonempty_of_mem_partition`：nonempty_of_mem_partition {c : Set (Se
t α)} (hc : IsPartition c) {s} (h : s in c) : s.Nonempty
· 使用定理 `Setoid.eq_eqv_class_of_mem`：eq_eqv_class_of_mem {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {s y} (hs : s in c) (hy : y in s) : s = { x | m
kClasses c H x y…

--- 原说明 ---
All elements of a partition of α are the equivalence class of some y ∈ α.
-/
theorem exists_of_mem_partition {c : Set (Set α)} (hc : IsPartition c) {s} (hs : s ∈ c) :
    ∃ y, s = { x | mkClasses c hc.2 x y } :=
  let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
the original partition. -/
/-
**Setoid.classes_mkClasses** 是 Mathlib 中的一个定理，位于命名空间 `Setoid`。
形式化陈述：classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) : (mkClasses c hc
.2).classes = c
参数：c : Set (Set α)；hc : IsPartition c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Setoid.eq_eqv_class_of_mem`：eq_eqv_class_of_mem {c : Set (Set α)} (H : f
orall a, exists! b in c, a in b) {s y} (hs : s in c) (hy : y in s) : s = { x | m
kClasses c H x y…
· 使用定理 `Setoid.exists_of_mem_partition`：exists_of_mem_partition {c : Set (Set α)
} (hc : IsPartition c) {s} (hs : s in c) : exists y, s = { x | mkClasses c hc.2 
x y }

--- 原说明 ---
The equivalence classes of the equivalence relation defined by a partition of α 
equal
the original partition.
-/
theorem classes_mkClasses (c : Set (Set α)) (hc : IsPartition c) :
    (mkClasses c hc.2).classes = c := by
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨b, ⟨hb, hy⟩, _⟩ := hc.2 y
    rwa [← eq_eqv_class_of_mem _ hb hy]
  · exact exists_of_mem_partition hc

/-- The subtype of partitions of a type, endowed with the canonical order on partitions. -/
/-
**Setoid.Partitions** 是 Mathlib 中的一个定义，位于命名空间 `Setoid`。
形式化陈述：Partitions (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of partitions of a type, endowed with the canonical order on partiti
ons.
-/
def Partitions (α : Type*) : Type _ := Subtype (@IsPartition α)

/-- Interpreting an element of `Partitions α` as a set of sets. -/
/-
**Setoid.Partitions.toSet** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.Partitions`。
形式化陈述：{α : Type u_1} → Setoid.Partitions α → Set (Set α)
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpreting an element of `Partitions α` as a set of sets.
-/
def Partitions.toSet (p : Partitions α) : Set (Set α) :=
  Subtype.val p
/-
**Setoid.Partitions.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Setoid.Partitions`。
形式化陈述：∀ {α : Type u_1} (p q : Setoid.Partitions α), p = q ↔ p.toSet = q.toSet
参数：p q : Setoid.Partitions α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma Partitions.ext_iff (p q : Partitions α) : p = q ↔ p.toSet = q.toSet :=
  Subtype.ext_iff
/-
**Setoid.Partitions.isPartition** 是 Mathlib 中的一个定理，位于命名空间 `Setoid.Partitions`。
形式化陈述：∀ {α : Type u_1} (p : Setoid.Partitions α), Setoid.IsPartition p.toSet
参数：p : Setoid.Partitions α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Partitions.isPartition (p : Partitions α) : IsPartition p.toSet := p.2

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
/-
**Setoid.Partition.le** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.Partition`。
形式化陈述：{α : Type u_1} → LE (Setoid.Partitions α)
参数：Setoid.Partitions α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining `≤` on partitions as the `≤` defined on their induced equivalence relat
ions.
-/
instance Partition.le : LE (Partitions α) :=
  ⟨fun x y => mkClasses x.toSet x.isPartition.2 ≤ mkClasses y.toSet y.isPartition.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
equivalence relations. -/
/-
**Setoid.Partition.partialOrder** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.Partition`。
形式化陈述：{α : Type u_1} → PartialOrder (Setoid.Partitions α)
参数：Setoid.Partitions α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining a partial order on partitions as the partial order on their induced
equivalence relations.
-/
instance Partition.partialOrder : PartialOrder (Partitions α) where
  lt x y := x ≤ y ∧ ¬y ≤ x
  le_refl _ := @le_refl (Setoid α) _ _
  le_trans _ _ _ := @le_trans (Setoid α) _ _ _ _
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hx hy := by
    let h := @le_antisymm (Setoid α) _ _ _ hx hy
    rw [Partitions.ext_iff, ← classes_mkClasses x.toSet x.isPartition,
      ← classes_mkClasses y.toSet y.isPartition, h]

set_option backward.isDefEq.respectTransparency.types false in
variable (α) in
/-- The order-preserving bijection between equivalence relations on a type `α`, and
partitions of `α` into subsets. -/
/-
**Setoid.Partition.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.Partition`。
形式化陈述：(α : Type u_1) → Setoid α ≃o Setoid.Partitions α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.mkClasses_classes`：mkClasses_classes (r : Setoid α) : mkClasses r
.classes classes_eqv_classes = r

--- 原说明 ---
The order-preserving bijection between equivalence relations on a type `α`, and
partitions of `α` into subsets.
-/
protected def Partition.orderIso : Setoid α ≃o Partitions α where
  toFun r := ⟨r.classes, empty_notMem_classes, classes_eqv_classes⟩
  invFun C := mkClasses C.1 C.2.2
  left_inv := mkClasses_classes
  right_inv C := by
    rw [Partitions.ext_iff, ← classes_mkClasses C.toSet C.isPartition]
    rfl
  map_rel_iff' {r s} := by
    conv_rhs => rw [← mkClasses_classes r, ← mkClasses_classes s]
    rfl

/-- A complete lattice instance for partitions; there is more infrastructure for the
equivalent complete lattice on equivalence relations. -/
/-
**Setoid.Partition.completeLattice** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.Partition`。
形式化陈述：{α : Type u_1} → CompleteLattice (Setoid.Partitions α)
参数：Setoid.Partitions α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete lattice instance for partitions; there is more infrastructure for the
equivalent complete lattice on equivalence relations.
-/
instance Partition.completeLattice : CompleteLattice (Partitions α) :=
  GaloisInsertion.liftCompleteLattice <|
    @OrderIso.toGaloisInsertion _ (Partitions α) _ (PartialOrder.toPreorder) <|
      Partition.orderIso α

end Partition

/-- A finite setoid partition furnishes a finpartition -/
@[simps]
/-
**Setoid.IsPartition.finpartition** 是 Mathlib 中的一个定义，位于命名空间 `Setoid.IsPartition`
。
形式化陈述：{α : Type u_1} → {c : Finset (Set α)} → Setoid.IsPartition ↑c → Finpartiti
on Set.univ
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite setoid partition furnishes a finpartition
-/
def IsPartition.finpartition {c : Finset (Set α)} (hc : Setoid.IsPartition (c : Set (Set α))) :
    Finpartition (Set.univ : Set α) where
  parts := c
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr <| eqv_classes_disjoint hc.2
  sup_parts := c.sup_id_set_eq_sUnion.trans hc.sUnion_eq_univ
  bot_notMem := hc.left

end Setoid

/-- A finpartition gives rise to a setoid partition -/
/-
**Finpartition.isPartition_parts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
 Setoid.IsPartition (f.parts : Set (Set α))
参数：f : Finpartition (Set.univ : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
· 使用定理 `Setoid.eqv_classes_of_disjoint_union`：eqv_classes_of_disjoint_union {c :
 Set (Set α)} (hu : Set.sUnion c = @Set.univ α) (H : c.PairwiseDisjoint id) (a) 
: exists! b in c, a in b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_id_set_eq_sUnion`：sup_id_set_eq_sUnion (s : Finset (Set α)) :
 s.sup id = ⋃₀ ↑s
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id

--- 原说明 ---
A finpartition gives rise to a setoid partition
-/
theorem Finpartition.isPartition_parts {α} (f : Finpartition (Set.univ : Set α)) :
    Setoid.IsPartition (f.parts : Set (Set α)) :=
  ⟨f.bot_notMem,
    Setoid.eqv_classes_of_disjoint_union (f.parts.sup_id_set_eq_sUnion.symm.trans f.sup_parts)
      f.supIndep.pairwiseDisjoint⟩

/-- Constructive information associated with a partition of a type `α` indexed by another type `ι`,
`s : ι → Set α`.

`IndexedPartition.index` sends an element to its index, while `IndexedPartition.some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not needed, then
`Setoid.ker index` by itself may be sufficient. -/
/-
**IndexedPartition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} → {α : Type u_2} → (ι → Set α) → Type (max u_1 u_2)
参数：ι → Set α；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructive information associated with a partition of a type `α` indexed by an
other type `ι`,
`s : ι → Set α`.

`IndexedPartition.index` sends an element to its index, while `IndexedPartition.
some` sends
an index to an element of the corresponding set.

This type is primarily useful for definitional control of `s` - if this is not n
eeded, then
`Setoid.ker index` by itself may be sufficient.
-/
structure IndexedPartition {ι α : Type*} (s : ι → Set α) where
  /-- two indexes are equal if they are equal in membership -/
  eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j
  /-- sends an index to an element of the corresponding set -/
  some : ι → α
  /-- membership invariance for `some` -/
  some_mem : ∀ i, some i ∈ s i
  /-- index for type `α` -/
  index : α → ι
  /-- membership invariance for `index` -/
  mem_index : ∀ x, x ∈ s (index x)

open scoped Function -- required for scoped `on` notation

/-- The non-constructive constructor for `IndexedPartition`. -/
/-
**IndexedPartition.mk'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IndexedPartition.mk' {ι α : Type*} (s : ι -> Set α) (dis : Pairwise (Disjo
int on s)) (nonempty : forall i, (s i).Nonempty) (ex : forall x, exists i, x in 
s i) : IndexedPartition s where eq_of_mem {_x _i _j} hxi hxj
参数：s : ι -> Set α；dis : Pairwise (Disjoint on s)；nonempty : forall i, (s i).None
mpty；ex : forall x, exists i, x in s i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-constructive constructor for `IndexedPartition`.
-/
noncomputable def IndexedPartition.mk' {ι α : Type*} (s : ι → Set α)
    (dis : Pairwise (Disjoint on s)) (nonempty : ∀ i, (s i).Nonempty)
    (ex : ∀ x, ∃ i, x ∈ s i) : IndexedPartition s where
  eq_of_mem {_x _i _j} hxi hxj := by_contradiction fun h => (dis h).le_bot ⟨hxi, hxj⟩
  some i := (nonempty i).some
  some_mem i := (nonempty i).choose_spec
  index x := (ex x).choose
  mem_index x := (ex x).choose_spec

namespace IndexedPartition

open Set

variable {ι α : Type*} {s : ι → Set α}

/-- On a unique index set there is the obvious trivial partition -/
/-
**IndexedPartition.** 是 Mathlib 中的一个实例，位于命名空间 `IndexedPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a unique index set there is the obvious trivial partition
-/
instance [Unique ι] [Inhabited α] : Inhabited (IndexedPartition fun _i : ι => (Set.univ : Set α)) :=
  ⟨{  eq_of_mem := fun {_x _i _j} _hi _hj => Subsingleton.elim _ _
      some := default
      some_mem := Set.mem_univ
      index := default
      mem_index := Set.mem_univ }⟩

attribute [simp] some_mem

variable (hs : IndexedPartition s)

include hs in
/-
**IndexedPartition.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：exists_mem (x : α) : exists i, x in s i
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndexedPartition.mem_index`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) (x : α), x ∈ s (self.index x)
-/
theorem exists_mem (x : α) : ∃ i, x ∈ s i :=
  ⟨hs.index x, hs.mem_index x⟩

include hs in
/-
**IndexedPartition.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：iUnion : ⋃ i, s i = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IndexedPartition.exists_mem`：exists_mem (x : α) : exists i, x in s i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion : ⋃ i, s i = univ := by
  ext x
  simp [hs.exists_mem x]

include hs in
/-
**IndexedPartition.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：disjoint : Pairwise (Disjoint on s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `IndexedPartition.eq_of_mem`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) {x : α} {i j : ι}, x ∈ s i → x ∈ s j → i = j
-/
theorem disjoint : Pairwise (Disjoint on s) := fun {_i _j} h =>
  disjoint_left.mpr fun {_x} hxi hxj => h (hs.eq_of_mem hxi hxj)
/-
**IndexedPartition.mem_iff_index_eq** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`
。
形式化陈述：mem_iff_index_eq {x i} : x in s i ↔ hs.index x = i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IndexedPartition.eq_of_mem`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) {x : α} {i j : ι}, x ∈ s i → x ∈ s j → i = j
· 使用定理 `IndexedPartition.mem_index`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) (x : α), x ∈ s (self.index x)
-/
theorem mem_iff_index_eq {x i} : x ∈ s i ↔ hs.index x = i :=
  ⟨fun hxi => (hs.eq_of_mem hxi (hs.mem_index x)).symm, fun h => h ▸ hs.mem_index _⟩
/-
**IndexedPartition.eq** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：eq (i) : s i = { x | hs.index x = i }
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
-/
theorem eq (i) : s i = { x | hs.index x = i } :=
  Set.ext fun _ => hs.mem_iff_index_eq

/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
/-
**IndexedPartition.setoid** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：{ι : Type u_1} → {α : Type u_2} → {s : ι → Set α} → IndexedPartition s → S
etoid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition.
-/
protected abbrev setoid (hs : IndexedPartition s) : Setoid α :=
  Setoid.ker hs.index

@[simp]
/-
**IndexedPartition.index_some** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：index_some (i : ι) : hs.index (hs.some i) = i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
· 使用定理 `IndexedPartition.some_mem`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set 
α} (self : IndexedPartition s) (i : ι), self.some i ∈ s i
-/
theorem index_some (i : ι) : hs.index (hs.some i) = i :=
  (mem_iff_index_eq _).1 <| hs.some_mem i
/-
**IndexedPartition.some_index** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：some_index (x : α) : hs.setoid (hs.some (hs.index x)) x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IndexedPartition.index_some`：index_some (i : ι) : hs.index (hs.some i) =
 i
-/
theorem some_index (x : α) : hs.setoid (hs.some (hs.index x)) x :=
  hs.index_some (hs.index x)

/-- The quotient associated to an indexed partition. -/
/-
**IndexedPartition.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：{ι : Type u_1} → {α : Type u_2} → {s : ι → Set α} → IndexedPartition s → T
ype u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient associated to an indexed partition.
-/
protected def Quotient :=
  Quotient hs.setoid

/-- The projection onto the quotient associated to an indexed partition. -/
/-
**IndexedPartition.proj** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：proj : α -> hs.Quotient
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The projection onto the quotient associated to an indexed partition.
-/
def proj : α → hs.Quotient :=
  Quotient.mk''
/-
**IndexedPartition.** 是 Mathlib 中的一个实例，位于命名空间 `IndexedPartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited hs.Quotient :=
  ⟨hs.proj default⟩
/-
**IndexedPartition.proj_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.index x = hs.index y :=
  Quotient.eq''

@[simp]
/-
**IndexedPartition.proj_some_index** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `IndexedPartition.some_index`：some_index (x : α) : hs.setoid (hs.some (hs
.index x)) x
-/
theorem proj_some_index (x : α) : hs.proj (hs.some (hs.index x)) = hs.proj x :=
  Quotient.eq''.2 (hs.some_index x)

/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
/-
**IndexedPartition.equivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：equivQuotient : ι ≃ hs.Quotient
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IndexedPartition.index_some`：index_some (i : ι) : hs.index (hs.some i) =
 i

--- 原说明 ---
The obvious equivalence between the quotient associated to an indexed partition 
and
the indexing type.
-/
def equivQuotient : ι ≃ hs.Quotient :=
  (Setoid.quotientKerEquivOfRightInverse hs.index hs.some <| hs.index_some).symm

@[simp]
/-
**IndexedPartition.equivQuotient_index_apply** 是 Mathlib 中的一个定理，位于命名空间 `IndexedP
artition`。
形式化陈述：equivQuotient_index_apply (x : α) : hs.equivQuotient (hs.index x) = hs.pro
j x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IndexedPartition.proj_eq_iff`：proj_eq_iff {x y : α} : hs.proj x = hs.pro
j y ↔ hs.index x = hs.index y
· 使用定理 `IndexedPartition.some_index`：some_index (x : α) : hs.setoid (hs.some (hs
.index x)) x
-/
theorem equivQuotient_index_apply (x : α) : hs.equivQuotient (hs.index x) = hs.proj x :=
  hs.proj_eq_iff.mpr (some_index hs x)

@[simp]
/-
**IndexedPartition.equivQuotient_symm_proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Inde
xedPartition`。
形式化陈述：equivQuotient_symm_proj_apply (x : α) : hs.equivQuotient.symm (hs.proj x) 
= hs.index x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivQuotient_symm_proj_apply (x : α) : hs.equivQuotient.symm (hs.proj x) = hs.index x :=
  rfl
/-
**IndexedPartition.equivQuotient_index** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartiti
on`。
形式化陈述：equivQuotient_index : hs.equivQuotient ∘ hs.index = hs.proj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IndexedPartition.equivQuotient_index_apply`：equivQuotient_index_apply (x
 : α) : hs.equivQuotient (hs.index x) = hs.proj x
-/
theorem equivQuotient_index : hs.equivQuotient ∘ hs.index = hs.proj :=
  funext hs.equivQuotient_index_apply

/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. This is a computable version of `Quotient.out` using `IndexedPartition.some`. -/
/-
**IndexedPartition.out** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：out : hs.Quotient ↪ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A map choosing a representative for each element of the quotient associated to a
n indexed
partition. This is a computable version of `Quotient.out` using `IndexedPartitio
n.some`.
-/
def out : hs.Quotient ↪ α :=
  hs.equivQuotient.symm.toEmbedding.trans ⟨hs.some, Function.LeftInverse.injective hs.index_some⟩

/-- This lemma is analogous to `Quotient.mk_out'`. -/
@[simp]
/-
**IndexedPartition.out_proj** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is analogous to `Quotient.mk_out'`.
-/
theorem out_proj (x : α) : hs.out (hs.proj x) = hs.some (hs.index x) :=
  rfl

/-- The indices of `Quotient.out` and `IndexedPartition.out` are equal. -/
/-
**IndexedPartition.index_out** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：index_out (x : hs.Quotient) : hs.index x.out = hs.index (hs.out x)
参数：x : hs.Quotient。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Setoid.ker_apply_mk_out`：ker_apply_mk_out {f : α -> β} (a : α) : f (⟦a⟧ 
: Quotient (Setoid.ker f)).out = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IndexedPartition.index_some`：index_some (i : ι) : hs.index (hs.some i) =
 i

--- 原说明 ---
The indices of `Quotient.out` and `IndexedPartition.out` are equal.
-/
theorem index_out (x : hs.Quotient) : hs.index x.out = hs.index (hs.out x) :=
  Quotient.inductionOn' x fun x => (Setoid.ker_apply_mk_out x).trans (hs.index_some _).symm

/-- This lemma is analogous to `Quotient.out_eq'`. -/
@[simp]
/-
**IndexedPartition.proj_out** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：proj_out (x : hs.Quotient) : hs.proj (hs.out x) = x
参数：x : hs.Quotient。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `IndexedPartition.some_index`：some_index (x : α) : hs.setoid (hs.some (hs
.index x)) x

--- 原说明 ---
This lemma is analogous to `Quotient.out_eq'`.
-/
theorem proj_out (x : hs.Quotient) : hs.proj (hs.out x) = x :=
  Quotient.inductionOn' x fun x => Quotient.sound' <| hs.some_index x
/-
**IndexedPartition.class_of** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：class_of {x : α} : Set.ofPred (hs.setoid x) = s (hs.index x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
-/
theorem class_of {x : α} : Set.ofPred (hs.setoid x) = s (hs.index x) :=
  Set.ext fun _y => eq_comm.trans hs.mem_iff_index_eq.symm
/-
**IndexedPartition.proj_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：proj_fiber (x : hs.Quotient) : hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm 
x)
参数：x : hs.Quotient。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem proj_fiber (x : hs.Quotient) : hs.proj ⁻¹' {x} = s (hs.equivQuotient.symm x) :=
  Quotient.inductionOn' x fun x => by
    ext y
    simp only [Set.mem_preimage, hs.mem_iff_index_eq]
    exact Quotient.eq''

/-- Combine functions with disjoint domains into a new function.
You can use the regular expression `def.*piecewise` to search for
other ways to define piecewise functions in mathlib4. -/
/-
**IndexedPartition.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`。
形式化陈述：piecewise {β : Type*} (f : ι -> α -> β) : α -> β
参数：f : ι -> α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine functions with disjoint domains into a new function.
You can use the regular expression `def.*piecewise` to search for
other ways to define piecewise functions in mathlib4.
-/
def piecewise {β : Type*} (f : ι → α → β) : α → β := fun x => f (hs.index x) x
/-
**IndexedPartition.piecewise_apply** 是 Mathlib 中的一个引理，位于命名空间 `IndexedPartition`。
形式化陈述：piecewise_apply {β : Type*} {f : ι -> α -> β} (x : α) : hs.piecewise f x =
 f (hs.index x) x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piecewise_apply {β : Type*} {f : ι → α → β} (x : α) : hs.piecewise f x = f (hs.index x) x :=
  rfl

open Function

variable {β : Type*} {f : ι → α → β}

/-- A family of injective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form an injective function. -/
/-
**IndexedPartition.piecewise_inj** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：piecewise_inj (h_injOn : forall i, InjOn (f i) (s i)) (h_disjoint : Pairwi
seDisjoint (univ : Set ι) fun i => (f i) '' (s i)) : Injective (piecewise hs f)
参数：h_injOn : forall i, InjOn (f i) (s i)；h_disjoint : PairwiseDisjoint (univ : S
et ι) fun i => (f i) '' (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `trivial`：True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IndexedPartition.mem_index`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) (x : α), x ∈ s (self.index x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
A family of injective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form an injective function.
-/
theorem piecewise_inj (h_injOn : ∀ i, InjOn (f i) (s i))
    (h_disjoint : PairwiseDisjoint (univ : Set ι) fun i => (f i) '' (s i)) :
    Injective (piecewise hs f) := by
  intro x y h
  suffices hs.index x = hs.index y by
    apply h_injOn (hs.index x) (hs.mem_index x) (this ▸ hs.mem_index y)
    simpa only [piecewise_apply, this] using h
  apply h_disjoint.elim trivial trivial
  contrapose! h
  exact h.ne_of_mem (mem_image_of_mem _ (hs.mem_index x)) (mem_image_of_mem _ (hs.mem_index y))

/-- A family of bijective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form a bijective function. -/
/-
**IndexedPartition.piecewise_bij** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：piecewise_bij {t : ι -> Set β} (ht : IndexedPartition t) (hf : forall i, B
ijOn (f i) (s i) (t i)) : Bijective (piecewise hs f)
参数：ht : IndexedPartition t；hf : forall i, BijOn (f i) (s i) (t i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.BijOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f₁ f₂ : α → β},   Set.BijOn f₁ s t → Set.EqOn f₁ f₂ s → Set.BijOn f₂ s t
· 使用引理 `IndexedPartition.piecewise_apply`：piecewise_apply {β : Type*} {f : ι -> 
α -> β} (x : α) : hs.piecewise f x = f (hs.index x) x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `IndexedPartition.piecewise_inj`：piecewise_inj (h_injOn : forall i, InjOn
 (f i) (s i)) (h_disjoint : PairwiseDisjoint (univ : Set ι) fun i => (f i) '' (s
 i)) : Injective (pi…
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `IndexedPartition.disjoint`：disjoint : Pairwise (Disjoint on s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.bijOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.BijOn f
 Set.univ Set.univ ↔ Function.Bijective f
· 使用定理 `IndexedPartition.iUnion`：iUnion : ⋃ i, s i = univ
· 使用定理 `Set.bijOn_iUnion`：bijOn_iUnion {s : ι -> Set α} {t : ι -> Set β} {f : α 
-> β} (H : forall i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f 
(⋃ i, …

--- 原说明 ---
A family of bijective functions with pairwise disjoint
domains and pairwise disjoint ranges can be glued together
to form a bijective function.
-/
theorem piecewise_bij {t : ι → Set β} (ht : IndexedPartition t)
    (hf : ∀ i, BijOn (f i) (s i) (t i)) :
    Bijective (piecewise hs f) := by
  set g := piecewise hs f with hg
  have hg_bij (i) : BijOn g (s i) (t i) := by
    refine (hf i).congr fun x hx => ?_
    rw [hg, piecewise_apply, hs.mem_iff_index_eq.mp hx]
  have hg_inj : InjOn g (⋃ i, s i) := by
    refine injOn_of_injective (piecewise_inj hs (fun i ↦ BijOn.injOn (hf i)) ?_)
    simp only [fun i ↦ BijOn.image_eq (hf i)]
    rintro i - j - hij
    exact ht.disjoint hij
  rw [← bijOn_univ, ← hs.iUnion, ← ht.iUnion]
  exact bijOn_iUnion hg_bij hg_inj
/-
**IndexedPartition.piecewise_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartitio
n`。
形式化陈述：piecewise_preimage (f : ι -> α -> β) (t : Set β) : hs.piecewise f ⁻¹' t = 
⋃ i, s i inter (f i ⁻¹' t)
参数：f : ι -> α -> β；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `IndexedPartition.mem_index`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) (x : α), x ∈ s (self.index x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用引理 `IndexedPartition.piecewise_apply`：piecewise_apply {β : Type*} {f : ι -> 
α -> β} (x : α) : hs.piecewise f x = f (hs.index x) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem piecewise_preimage (f : ι → α → β) (t : Set β) :
    hs.piecewise f ⁻¹' t = ⋃ i, s i ∩ (f i ⁻¹' t) := by
  refine ext fun x => ⟨fun hx => ?_, fun ⟨a, ⟨i, hi⟩, ha⟩ => ?_⟩
  · rw [mem_preimage, piecewise_apply, ← mem_preimage] at hx
    exact mem_iUnion_of_mem (hs.index x) (mem_inter (hs.mem_index x) hx)
  · rw [← hi, ← (mem_iff_index_eq hs).mp ha.1] at ha
    simp_all [piecewise_apply]
/-
**IndexedPartition.range_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartition`。
形式化陈述：range_piecewise (f : ι -> α -> β) : range (hs.piecewise f) = ⋃ i, f i '' s
 i
参数：f : ι -> α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `IndexedPartition.mem_index`：∀ {ι : Type u_1} {α : Type u_2} {s : ι → Set
 α} (self : IndexedPartition s) (x : α), x ∈ s (self.index x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IndexedPartition.mem_iff_index_eq`：mem_iff_index_eq {x i} : x in s i ↔ h
s.index x = i
-/
theorem range_piecewise (f : ι → α → β) : range (hs.piecewise f) = ⋃ i, f i '' s i := by
  refine ext fun x => ⟨?_, fun ⟨t, ⟨i, hi⟩, ht⟩ ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact mem_iUnion_of_mem (hs.index x) ⟨x, hs.mem_index x, rfl⟩
  · simp only [← hi, mem_image] at ht
    obtain ⟨a, ha1, ha2⟩ := ht
    refine ⟨a, ?_⟩
    simp only [hs.mem_iff_index_eq] at ha1
    simpa [hs.mem_iff_index_eq, ← ha1] using! ha2
/-
**IndexedPartition.range_piecewise_subset** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPart
ition`。
形式化陈述：range_piecewise_subset (f : ι -> α -> β) : range (hs.piecewise f) subseteq
 ⋃ i, range (f i)
参数：f : ι -> α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem range_piecewise_subset (f : ι → α → β) : range (hs.piecewise f) ⊆ ⋃ i, range (f i) :=
  fun x ⟨y, hy⟩ => by simpa [IndexedPartition.piecewise_apply] using ⟨hs.index y, y, hy⟩

/-- Given a collections of sets `s : ι → Set α` that forms an indexed partition, we can group
some of the sets to obtain a coarser partition. -/
/-
**IndexedPartition.coarserPartition** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartition`
。
形式化陈述：coarserPartition (hs : IndexedPartition s) {κ : Type*} (g : ι -> κ) (hg : 
g.Surjective) : IndexedPartition (fun k : κ => ⋃ i in g ⁻¹' {k}, s i) where eq_o
f_mem {x _i _j} hxi hxj
参数：hs : IndexedPartition s；g : ι -> κ；hg : g.Surjective。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collections of sets `s : ι → Set α` that forms an indexed partition, we 
can group
some of the sets to obtain a coarser partition.
-/
noncomputable def coarserPartition (hs : IndexedPartition s) {κ : Type*} (g : ι → κ)
    (hg : g.Surjective) :
    IndexedPartition (fun k : κ => ⋃ i ∈ g ⁻¹' {k}, s i) where
  eq_of_mem {x _i _j} hxi hxj := by
    obtain ⟨a, ⟨c, hc⟩, ha⟩ := hxi
    obtain ⟨b, ⟨d, hd⟩, hb⟩ := hxj
    grind =>
      instantiate [mem_iUnion]
      have hb : x ∈ s d
      have ha : x ∈ s c
      have : c = d := hs.eq_of_mem ha hb
      finish
  some k := hs.some ((singleton_nonempty k).preimage hg).some
  some_mem k := by
    refine mem_iUnion_of_mem ((singleton_nonempty k).preimage hg).some ?_
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop]
    constructor
    · simpa using ((singleton_nonempty k).preimage hg).some_mem
    · exact hs.some_mem ((singleton_nonempty k).preimage hg).some
  index x := g (hs.index x)
  mem_index x := mem_iUnion_of_mem (hs.index x) (by simp [hs.mem_index])

end IndexedPartition

