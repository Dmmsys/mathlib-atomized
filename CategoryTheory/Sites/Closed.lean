/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.Order.Closure
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Closed sieves

A natural closure operator on sieves is a closure operator on `Sieve X` for each `X` which commutes
with pullback.
We show that a Grothendieck topology `J` induces a natural closure operator, and define what the
closed sieves are. The collection of `J`-closed sieves forms a presheaf which is a sheaf for `J`,
and further this presheaf can be used to determine the Grothendieck topology from the sheaf
predicate.
Finally we show that a natural closure operator on sieves induces a Grothendieck topology, and hence
that natural closure operators are in bijection with Grothendieck topologies.

## Main definitions

* `CategoryTheory.GrothendieckTopology.close`: Sends a sieve `S` on `X` to the set of arrows
  which it covers. This has all the usual properties of a closure operator, as well as commuting
  with pullback.
* `CategoryTheory.GrothendieckTopology.closureOperator`: The bundled `ClosureOperator` given
  by `CategoryTheory.GrothendieckTopology.close`.
* `CategoryTheory.GrothendieckTopology.IsClosed`: A sieve `S` on `X` is closed for the topology `J`
  if it contains every arrow it covers.
* `CategoryTheory.Functor.closedSieves`: The presheaf sending `X` to the collection of `J`-closed
  sieves on `X`. This is additionally shown to be a sheaf for `J`, and if this is a sheaf for a
  different topology `J'`, then `J' ≤ J`.
* `CategoryTheory.topologyOfClosureOperator`: A closure operator on the
  set of sieves on every object which commutes with pullback additionally induces a Grothendieck
  topology, giving a bijection with `CategoryTheory.GrothendieckTopology.closureOperator`.


## Tags

closed sieve, closure, Grothendieck topology

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J₁ J₂ : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
@[simps]
/-
**CategoryTheory.GrothendieckTopology.close** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.GrothendieckTopology`。
形式化陈述：close {X : C} (S : Sieve X) : Sieve X where arrows _ f
参数：S : Sieve X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.arrow_stable`：arrow_stable (f : Y ⟶ 
X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) : J.Covers S (g ≫ f)

--- 原说明 ---
The `J`-closure of a sieve is the collection of arrows which it covers.
-/
def close {X : C} (S : Sieve X) : Sieve X where
  arrows _ f := J₁.Covers S f
  downward_closed hS := J₁.arrow_stable _ _ hS

/-- Any sieve is smaller than its closure. -/
/-
**CategoryTheory.GrothendieckTopology.le_close** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：le_close {X : C} (S : Sieve X) : S <= J₁.close S
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.covering_of_eq_top`：covering_of_eq_t
op : S = ⊤ -> S in J X
· 使用定理 `CategoryTheory.Sieve.pullback_eq_top_of_mem`：pullback_eq_top_of_mem (S :
 Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤

--- 原说明 ---
Any sieve is smaller than its closure.
-/
theorem le_close {X : C} (S : Sieve X) : S ≤ J₁.close S :=
  fun _ _ hg => J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)

/-- A sieve is closed for the Grothendieck topology if it contains every arrow it covers.
In the case of the usual topology on a topological space, this means that the open cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
/-
**CategoryTheory.GrothendieckTopology.IsClosed** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GrothendieckTopology`。
形式化陈述：IsClosed {X : C} (S : Sieve X) : Prop
参数：S : Sieve X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sieve is closed for the Grothendieck topology if it contains every arrow it co
vers.
In the case of the usual topology on a topological space, this means that the op
en cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def IsClosed {X : C} (S : Sieve X) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f → S f

/-- If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains. -/
/-
**CategoryTheory.GrothendieckTopology.covers_iff_mem_of_isClosed** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：covers_iff_mem_of_isClosed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : 
C} (f : Y ⟶ X) : J₁.Covers S f ↔ S f
参数：h : J₁.IsClosed S；f : Y ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.arrow_max`：arrow_max (f : Y ⟶ X) (S 
: Sieve X) (hf : S f) : J.Covers S f

--- 原说明 ---
If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains.
-/
theorem covers_iff_mem_of_isClosed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X) :
    J₁.Covers S f ↔ S f :=
  ⟨h _, J₁.arrow_max _ _⟩

/-- Being `J`-closed is stable under pullback. -/
/-
**CategoryTheory.GrothendieckTopology.isClosed_pullback** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isClosed_pullback {X Y : C} (f : Y ⟶ X) (S : Sieve X) : J₁.IsClosed S -> J
₁.IsClosed (S.pullback f)
参数：f : Y ⟶ X；S : Sieve X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.covers_iff`：covers_iff (S : Sieve X)
 (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g

--- 原说明 ---
Being `J`-closed is stable under pullback.
-/
theorem isClosed_pullback {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.IsClosed S → J₁.IsClosed (S.pullback f) :=
  fun hS Z g hg => hS (g ≫ f) (by rwa [J₁.covers_iff, Sieve.pullback_comp])

/-- The closure of a sieve `S` is the largest closed sieve which contains `S` (justifying the name
"closure").
-/
/-
**CategoryTheory.GrothendieckTopology.le_close_of_isClosed** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：le_close_of_isClosed {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClose
d T) : J₁.close S <= T
参数：h : S <= T；hT : J₁.IsClosed T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.pullback_monotone`：pullback_monotone (f : Y ⟶ X) : 
Monotone (Sieve.pullback f)

--- 原说明 ---
The closure of a sieve `S` is the largest closed sieve which contains `S` (justi
fying the name
"closure").
-/
theorem le_close_of_isClosed {X : C} {S T : Sieve X} (h : S ≤ T) (hT : J₁.IsClosed T) :
    J₁.close S ≤ T :=
  fun _ f hf => hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)

/-- The closure of a sieve is closed. -/
/-
**CategoryTheory.GrothendieckTopology.close_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：close_isClosed {X : C} (S : Sieve X) : J₁.IsClosed (J₁.close S)
参数：S : Sieve X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.arrow_trans`：arrow_trans (f : Y ⟶ X)
 (S R : Sieve X) (h : J.Covers S f) : (forall {Z : C} (g : Z ⟶ X), S g -> J.Cove
rs R g) -> J.Covers R f

--- 原说明 ---
The closure of a sieve is closed.
-/
theorem close_isClosed {X : C} (S : Sieve X) : J₁.IsClosed (J₁.close S) :=
  fun _ g hg => J₁.arrow_trans g _ S hg fun _ hS => hS

/-- A Grothendieck topology induces a natural family of closure operators on sieves. -/
@[simps! isClosed]
/-
**CategoryTheory.GrothendieckTopology.closureOperator** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.GrothendieckTopology`。
形式化陈述：closureOperator (X : C) : ClosureOperator (Sieve X)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close`：le_close {X : C} (S : Siev
e X) : S <= J₁.close S
· 使用定理 `CategoryTheory.GrothendieckTopology.close_isClosed`：close_isClosed {X : 
C} (S : Sieve X) : J₁.IsClosed (J₁.close S)
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close_of_isClosed`：le_close_of_is
Closed {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T) : J₁.close S <=
 T

--- 原说明 ---
A Grothendieck topology induces a natural family of closure operators on sieves.
-/
def closureOperator (X : C) : ClosureOperator (Sieve X) :=
  .ofPred J₁.close J₁.IsClosed J₁.le_close J₁.close_isClosed fun _ _ ↦ J₁.le_close_of_isClosed

/-- The sieve `S` is closed iff its closure is equal to itself. -/
/-
**CategoryTheory.GrothendieckTopology.isClosed_iff_close_eq_self** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：isClosed_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.clos
e S = S
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x

--- 原说明 ---
The sieve `S` is closed iff its closure is equal to itself.
-/
theorem isClosed_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.close S = S :=
  (J₁.closureOperator _).isClosed_iff
/-
**CategoryTheory.GrothendieckTopology.close_eq_self_of_isClosed** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：close_eq_self_of_isClosed {X : C} {S : Sieve X} (hS : J₁.IsClosed S) : J₁.
close S = S
参数：hS : J₁.IsClosed S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.GrothendieckTopology.isClosed_iff_close_eq_self`：isClosed
_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.close S = S
-/
theorem close_eq_self_of_isClosed {X : C} {S : Sieve X} (hS : J₁.IsClosed S) : J₁.close S = S :=
  (J₁.isClosed_iff_close_eq_self S).1 hS

/-- Closing under `J` is stable under pullback. -/
/-
**CategoryTheory.GrothendieckTopology.pullback_close** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) : J₁.close (S.pullback 
f) = (J₁.close S).pullback f
参数：f : Y ⟶ X；S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close_of_isClosed`：le_close_of_is
Closed {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T) : J₁.close S <=
 T
· 使用定理 `CategoryTheory.Sieve.pullback_monotone`：pullback_monotone (f : Y ⟶ X) : 
Monotone (Sieve.pullback f)
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close`：le_close {X : C} (S : Siev
e X) : S <= J₁.close S
· 使用定理 `CategoryTheory.GrothendieckTopology.isClosed_pullback`：isClosed_pullback
 {X Y : C} (f : Y ⟶ X) (S : Sieve X) : J₁.IsClosed S -> J₁.IsClosed (S.pullback 
f)
· 使用定理 `CategoryTheory.GrothendieckTopology.close_isClosed`：close_isClosed {X : 
C} (S : Sieve X) : J₁.IsClosed (J₁.close S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g

--- 原说明 ---
Closing under `J` is stable under pullback.
-/
theorem pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.close (S.pullback f) = (J₁.close S).pullback f := by
  apply le_antisymm
  · refine J₁.le_close_of_isClosed (Sieve.pullback_monotone _ (J₁.le_close S)) ?_
    apply J₁.isClosed_pullback _ _ (J₁.close_isClosed _)
  · intro Z g hg
    change _ ∈ J₁ _
    rw [← Sieve.pullback_comp]
    apply hg

@[gcongr, mono]
/-
**CategoryTheory.GrothendieckTopology.monotone_close** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GrothendieckTopology`。
形式化陈述：monotone_close {X : C} : Monotone (J₁.close : Sieve X -> Sieve X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
theorem monotone_close {X : C} : Monotone (J₁.close : Sieve X → Sieve X) :=
  (J₁.closureOperator _).monotone

@[simp]
/-
**CategoryTheory.GrothendieckTopology.close_close** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.GrothendieckTopology`。
形式化陈述：close_close {X : C} (S : Sieve X) : J₁.close (J₁.close S) = J₁.close S
参数：S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
theorem close_close {X : C} (S : Sieve X) : J₁.close (J₁.close S) = J₁.close S :=
  (J₁.closureOperator _).idempotent _

/--
The sieve `S` is in the topology iff its closure is the maximal sieve. This shows that the closure
operator determines the topology.
-/
/-
**CategoryTheory.GrothendieckTopology.close_eq_top_iff_mem** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：close_eq_top_iff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S in J₁ X
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y

--- 原说明 ---
The sieve `S` is in the topology iff its closure is the maximal sieve. This show
s that the closure
operator determines the topology.
-/
theorem close_eq_top_iff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S ∈ J₁ X := by
  constructor
  · intro h
    apply J₁.transitive (J₁.top_mem X)
    intro Y f hf
    change J₁.close S f
    rwa [h]
  · intro hS
    rw [_root_.eq_top_iff]
    intro Y f _
    apply J₁.pullback_stable _ hS

end GrothendieckTopology

variable (C) in
/-- The presheaf sending each object to the type of sieves on it. This will turn out to be a
subobject classifier for the category of presheaves. -/
@[simps]
/-
**CategoryTheory.Functor.sieves** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor Cᵒᵖ (Type (max v u))
参数：max v u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf sending each object to the type of sieves on it. This will turn out
 to be a
subobject classifier for the category of presheaves.
-/
def Functor.sieves : Cᵒᵖ ⥤ Type max v u where
  obj X := Sieve X.unop
  map f := ↾fun S ↦ S.pullback f.unop

/--
The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simps]
/-
**CategoryTheory.Functor.closedSieves** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.GrothendieckTopology C → CategoryTheory.Subfunctor (CategoryTheory.Functor
.sieves C)
参数：CategoryTheory.Functor.sieves C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf sending each object to the set of `J`-closed sieves on it. This pre
sheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves)
.
-/
def Functor.closedSieves : Subfunctor (Functor.sieves C) where
  obj X := {S : Sieve X.unop | J₁.IsClosed S}
  map f _ := J₁.isClosed_pullback f.unop _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of `J`-closed sieves is a `J`-sheaf.
The proof of this is adapted from [MM92], Chapter III, Section 7, Lemma 1.
-/
/-
**CategoryTheory.classifier_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：classifier_isSheaf : Presieve.IsSheaf J₁ (Functor.closedSieves J₁).toFunct
or
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.GrothendieckTopology.covers_iff_mem_of_isClosed`：covers_i
ff_mem_of_isClosed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X)
 : J₁.Covers S f ↔ S f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GrothendieckTopology.covers_iff`：covers_iff (S : Sieve X)
 (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.pullback_monotone`：pullback_monotone (f : Y ⟶ X) : 
Monotone (Sieve.pullback f)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `CategoryTheory.GrothendieckTopology.arrow_intersect`：arrow_intersect (f 
: Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) : J.Covers (S ⊓
 R) f
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Presieve.compatible_iff_sieveCompatible`：compatible_iff_s
ieveCompatible (x : FamilyOfElements P (S : Presieve X)) : x.Compatible ↔ x.Siev
eCompatible
· 使用定理 `CategoryTheory.Sieve.pullback_eq_top_of_mem`：pullback_eq_top_of_mem (S :
 Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
· 使用定理 `CategoryTheory.GrothendieckTopology.close_isClosed`：close_isClosed {X : 
C} (S : Sieve X) : J₁.IsClosed (J₁.close S)
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_close`：pullback_close {X Y 
: C} (f : Y ⟶ X) (S : Sieve X) : J₁.close (S.pullback f) = (J₁.close S).pullback
 f
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close_of_isClosed`：le_close_of_is
Closed {X : C} {S T : Sieve X} (h : S <= T) (hT : J₁.IsClosed T) : J₁.close S <=
 T
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.GrothendieckTopology.le_close`：le_close {X : C} (S : Siev
e X) : S <= J₁.close S

--- 原说明 ---
The presheaf of `J`-closed sieves is a `J`-sheaf.
The proof of this is adapted from [MM92], Chapter III, Section 7, Lemma 1.
-/
theorem classifier_isSheaf : Presieve.IsSheaf J₁ (Functor.closedSieves J₁).toFunctor := by
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    dsimp at S M N ⊢
    ext Y f
    dsimp only [Subtype.coe_mk]
    rw [← J₁.covers_iff_mem_of_isClosed hM, ← J₁.covers_iff_mem_of_isClosed hN]
    have q : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (_ : S g), M.pullback g = N.pullback g :=
      fun Z g hg => congr_arg Subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm)
    have MSNS : M ⊓ S = N ⊓ S := by
      ext
      grind [Sieve.inter_apply, Sieve.mem_iff_pullback_eq_top]
    constructor
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      rw [← MSNS]
      apply J₁.arrow_intersect f M S hf (J₁.pullback_stable _ hS)
    · intro hf
      rw [J₁.covers_iff]
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      rw [MSNS]
      apply J₁.arrow_intersect f N S hf (J₁.pullback_stable _ hS)
  · intro x hx
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    let M := Sieve.bind S fun Y f hf => (x f hf).1
    have : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1 := by
      intro Y f hf
      apply le_antisymm
      · rintro Z u ⟨W, g, f', hf', hg : (x f' hf').1.1 _, c⟩
        rw [Sieve.mem_iff_pullback_eq_top,
          ← show (x (u ≫ f) _).1 = (x f hf).1.pullback u from congr_arg Subtype.val (hx f u hf)]
        conv_lhs => congr; congr; rw [← c] -- Porting note: Originally `simp_rw [← c]`
        rw [show (x (g ≫ f') _).1 = _ from congr_arg Subtype.val (hx f' g hf')]
        apply Sieve.pullback_eq_top_of_mem _ hg
      · apply Sieve.le_pullback_bind S fun Y f hf => (x f hf).1
    refine ⟨⟨_, J₁.close_isClosed M⟩, ?_⟩
    intro Y f hf
    dsimp
    ext1
    dsimp
    rw [← J₁.pullback_close, this _ hf]
    apply le_antisymm (J₁.le_close_of_isClosed le_rfl (x f hf).2) (J₁.le_close _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sieve `S` is covering for `J` if and only if the subobject classifier
is a sheaf for `S`. -/
/-
**CategoryTheory.GrothendieckTopology.mem_iff_isSheafFor_closedSieves** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) {X : C}   (S : CategoryTheory.Sieve X),   S ∈ J X ↔ C
ategoryTheory.Presieve.IsSheafFor (CategoryTheory.Functor.closedSieves J).toFunc
tor S.arrows
参数：J : CategoryTheory.GrothendieckTopology C；S : CategoryTheory.Sieve X；Category
Theory.Functor.closedSieves J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.classifier_isSheaf`：classifier_isSheaf : Presieve.IsSheaf
 J₁ (Functor.closedSieves J₁).toFunctor
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GrothendieckTopology.close_eq_top_iff_mem`：close_eq_top_i
ff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S in J₁ X
· 使用定理 `CategoryTheory.GrothendieckTopology.close_isClosed`：close_isClosed {X : 
C} (S : Sieve X) : J₁.IsClosed (J₁.close S)
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CategoryTheory.Sieve.pullback_top`：pullback_top {f : Y ⟶ X} : (⊤ : Sieve
 X).pullback f = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_close`：pullback_close {X Y 
: C} (f : Y ⟶ X) (S : Sieve X) : J₁.close (S.pullback f) = (J₁.close S).pullback
 f
· 使用定理 `CategoryTheory.Sieve.pullback_eq_top_of_mem`：pullback_eq_top_of_mem (S :
 Sieve X) {f : Y ⟶ X} : S f -> S.pullback f = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2

--- 原说明 ---
A sieve `S` is covering for `J` if and only if the subobject classifier
is a sheaf for `S`.
-/
lemma GrothendieckTopology.mem_iff_isSheafFor_closedSieves
    (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    S ∈ J X ↔ Presieve.IsSheafFor (Functor.closedSieves J).toFunctor S.arrows := by
  refine ⟨fun hS ↦ classifier_isSheaf _ _ hS, fun H ↦ ?_⟩
  rw [← J.close_eq_top_iff_mem]
  have : J.IsClosed (⊤ : Sieve X) := by
    intro Y f _
    trivial
  suffices (⟨J.close S, J.close_isClosed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  refine H.isSeparatedFor.ext fun Y f hf ↦ ?_
  simp only [Subfunctor.toFunctor_obj, Functor.sieves_obj, Functor.closedSieves_obj, Set.coe_ofPred]
  ext1
  dsimp
  rw [Sieve.pullback_top, ← J.pullback_close, S.pullback_eq_top_of_mem hf,
    J.close_eq_top_iff_mem]
  apply J.top_mem

/-- If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. Note the converse is true by
`classifier_isSheaf` and `isSheaf_of_le`.
-/
/-
**CategoryTheory.le_topology_of_closedSieves_isSheaf** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：le_topology_of_closedSieves_isSheaf {J₁ J₂ : GrothendieckTopology C} (h : 
Presieve.IsSheaf J₁ (Functor.closedSieves J₂).toFunctor) : J₁ <= J₂
参数：h : Presieve.IsSheaf J₁ (Functor.closedSieves J₂).toFunctor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.mem_iff_isSheafFor_closedSieves`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothe
ndieckTopology C) {X : C}   (S : CategoryTheory.Sieve X),…

--- 原说明 ---
If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. Note the conve
rse is true by
`classifier_isSheaf` and `isSheaf_of_le`.
-/
theorem le_topology_of_closedSieves_isSheaf {J₁ J₂ : GrothendieckTopology C}
    (h : Presieve.IsSheaf J₁ (Functor.closedSieves J₂).toFunctor) : J₁ ≤ J₂ := by
  intro X S hS
  rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
  exact h _ hS

/-- If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂`. -/
/-
**CategoryTheory.topology_eq_iff_same_sheaves** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory`。
形式化陈述：topology_eq_iff_same_sheaves {J₁ J₂ : GrothendieckTopology C} : J₁ = J₂ ↔ 
forall P : Cᵒᵖ ⥤ Type (max v u), Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₂ P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.le_topology_of_closedSieves_isSheaf`：le_topology_of_close
dSieves_isSheaf {J₁ J₂ : GrothendieckTopology C} (h : Presieve.IsSheaf J₁ (Funct
or.closedSieves J₂).toFunctor) : J₁ <= J…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.classifier_isSheaf`：classifier_isSheaf : Presieve.IsSheaf
 J₁ (Functor.closedSieves J₁).toFunctor
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂
`.
-/
theorem topology_eq_iff_same_sheaves {J₁ J₂ : GrothendieckTopology C} :
    J₁ = J₂ ↔ ∀ P : Cᵒᵖ ⥤ Type (max v u), Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₂ P := by
  constructor
  · rintro rfl
    intro P
    rfl
  · intro h
    apply le_antisymm
    · apply le_topology_of_closedSieves_isSheaf
      rw [h]
      apply classifier_isSheaf
    · apply le_topology_of_closedSieves_isSheaf
      rw [← h]
      apply classifier_isSheaf

/--
A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simps]
/-
**CategoryTheory.topologyOfClosureOperator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：topologyOfClosureOperator (c : forall X : C, ClosureOperator (Sieve X)) (h
c : forall ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c _ (S.pullback f) = (c _ S).pul
lback f) : GrothendieckTopology C where sieves X
参数：c : forall X : C, ClosureOperator (Sieve X)；hc : forall ⦃X Y : C⦄ (f : Y ⟶ X)
 (S : Sieve X), c _ (S.pullback f) = (c _ S).pullback f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closure (increasing, inflationary and idempotent) operation on sieves that com
mutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
def topologyOfClosureOperator (c : ∀ X : C, ClosureOperator (Sieve X))
    (hc : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c _ (S.pullback f) = (c _ S).pullback f) :
    GrothendieckTopology C where
  sieves X := { S | c X S = ⊤ }
  top_mem' X := top_unique ((c X).le_closure _)
  pullback_stable' X Y S f hS := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq, hc, hS, Sieve.pullback_top]
  transitive' X S hS R hR := by
    rw [Set.mem_ofPred_eq] at hS
    rw [Set.mem_ofPred_eq, ← (c X).idempotent, eq_top_iff, ← hS]
    apply (c X).monotone fun Y f hf => _
    intro Y f hf
    rw [Sieve.mem_iff_pullback_eq_top, ← hc]
    apply hR hf

/--
The topology given by the closure operator `J.close` on a Grothendieck topology is the same as `J`.
-/
/-
**CategoryTheory.topologyOfClosureOperator_self** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory`。
形式化陈述：topologyOfClosureOperator_self : (topologyOfClosureOperator J₁.closureOper
ator fun _ _ => J₁.pullback_close) = J₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_close`：pullback_close {X Y 
: C} (f : Y ⟶ X) (S : Sieve X) : J₁.close (S.pullback f) = (J₁.close S).pullback
 f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.GrothendieckTopology.close_eq_top_iff_mem`：close_eq_top_i
ff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S in J₁ X

--- 原说明 ---
The topology given by the closure operator `J.close` on a Grothendieck topology 
is the same as `J`.
-/
theorem topologyOfClosureOperator_self :
    (topologyOfClosureOperator J₁.closureOperator fun _ _ => J₁.pullback_close) = J₁ := by
  ext X S
  apply GrothendieckTopology.close_eq_top_iff_mem
/-
**CategoryTheory.topologyOfClosureOperator_close** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：topologyOfClosureOperator_close (c : forall X : C, ClosureOperator (Sieve 
X)) (pb : forall ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c Y (S.pullback f) = (c X 
S).pullback f) (X : C) (S : Sieve X) : (topologyOfClosureOperator c pb).close S 
= c X S
参数：c : forall X : C, ClosureOperator (Sieve X)；pb : forall ⦃X Y : C⦄ (f : Y ⟶ X)
 (S : Sieve X), c Y (S.pullback f) = (c X S).pullback f；X : C；S : Sieve X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.mem_iff_pullback_eq_top`：mem_iff_pullback_eq_top (f
 : Y ⟶ X) : S f ↔ S.pullback f = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem topologyOfClosureOperator_close (c : ∀ X : C, ClosureOperator (Sieve X))
    (pb : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c Y (S.pullback f) = (c X S).pullback f) (X : C)
    (S : Sieve X) : (topologyOfClosureOperator c pb).close S = c X S := by
  ext Y f
  change c _ (Sieve.pullback f S) = ⊤ ↔ c _ S f
  rw [pb, Sieve.mem_iff_pullback_eq_top]

end CategoryTheory

