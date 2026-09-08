/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.GroupTheory.Submonoid.Centralizer
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Bundled subsemirings

We define some standard constructions on bundled subsemirings: `CompleteLattice` structure,
subsemiring `map`, `comap` and range (`rangeS`) of a `RingHom` etc.
-/

@[expose] public section


universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

section SubsemiringClass

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

/-
**SubsemiringClass.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `SubsemiringClass`。
形式化陈述：instCharZero [CharZero R] : CharZero s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
instance instCharZero [CharZero R] : CharZero s :=
  ⟨Function.Injective.of_comp (f := Subtype.val) (g := Nat.cast (R := s)) Nat.cast_injective⟩

end SubsemiringClass

end SubsemiringClass

variable [NonAssocSemiring S] [NonAssocSemiring T]

namespace Subsemiring

variable (s : Subsemiring R)

@[gcongr, mono]
/-
**Subsemiring.toSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R -> Submon
oid R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) :=
  fun _ _ => id

@[gcongr, mono]
/-
**Subsemiring.toSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R -> Submonoid R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subsemiring.toSubmonoid_strictMono`：toSubmonoid_strictMono : StrictMono 
(toSubmonoid : Subsemiring R -> Submonoid R)
-/
theorem toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) :=
  toSubmonoid_strictMono.monotone

@[gcongr, mono]
/-
**Subsemiring.toAddSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R -> 
AddSubmonoid R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  fun _ _ => id

@[gcongr, mono]
/-
**Subsemiring.toAddSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R -> AddSubmo
noid R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subsemiring.toAddSubmonoid_strictMono`：toAddSubmonoid_strictMono : Stric
tMono (toAddSubmonoid : Subsemiring R -> AddSubmonoid R)
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone

/-- Product of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
nonrec theorem list_prod_mem {R : Type*} [Semiring R] (s : Subsemiring R) {l : List R} :
    (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a `Subsemiring` is in the `Subsemiring`. -/
/-
**Subsemiring.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) {l : List R
}, (∀ x ∈ l, x ∈ s) → l.sum ∈ s
参数：s : Subsemiring R；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
Sum of a list of elements in a `Subsemiring` is in the `Subsemiring`.
-/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a `Subsemiring` of a `CommSemiring`
is in the `Subsemiring`. -/
/-
**Subsemiring.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (s : Subsemiring R) (m : Multiset
 R), (∀ a ∈ m, a ∈ s) → m.prod ∈ s
参数：s : Subsemiring R；m : Multiset R；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
Product of a multiset of elements in a `Subsemiring` of a `CommSemiring`
is in the `Subsemiring`.
-/
protected theorem multiset_prod_mem {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m

/-- Sum of a multiset of elements in a `Subsemiring` of a `NonAssocSemiring` is
in the `Subsemiring`. -/
/-
**Subsemiring.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) (m : Multis
et R), (∀ a ∈ m, a ∈ s) → m.sum ∈ s
参数：s : Subsemiring R；m : Multiset R；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
Sum of a multiset of elements in a `Subsemiring` of a `NonAssocSemiring` is
in the `Subsemiring`.
-/
protected theorem multiset_sum_mem (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

/-- Product of elements of a subsemiring of a `CommSemiring` indexed by a `Finset` is in the
`Subsemiring`. -/
/-
**Subsemiring.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (s : Subsemiring R) {ι : Type u_2
} {t : Finset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∏ i ∈ t, f i ∈ s
参数：s : Subsemiring R；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
Product of elements of a subsemiring of a `CommSemiring` indexed by a `Finset` i
s in the
`Subsemiring`.
-/
protected theorem prod_mem {R : Type*} [CommSemiring R] (s : Subsemiring R) {ι : Type*}
    {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in a `Subsemiring` of a `NonAssocSemiring` indexed by a `Finset`
is in the `Subsemiring`. -/
/-
**Subsemiring.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (s : Subsemiring R) {ι : Type u
_1} {t : Finset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∑ i ∈ t, f i ∈ s
参数：s : Subsemiring R；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
Sum of elements in a `Subsemiring` of a `NonAssocSemiring` indexed by a `Finset`
is in the `Subsemiring`.
-/
protected theorem sum_mem (s : Subsemiring R) {ι : Type*} {t : Finset ι} {f : ι → R}
    (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-- The ring equiv between the top element of `Subsemiring R` and `R`. -/
@[simps]
/-
**Subsemiring.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：topEquiv : (⊤ : Subsemiring R) ≃+* R where toFun r
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mem_top`：mem_top (x : R) : x in (⊤ : Subsemiring R)

--- 原说明 ---
The ring equiv between the top element of `Subsemiring R` and `R`.
-/
def topEquiv : (⊤ : Subsemiring R) ≃+* R where
  toFun r := r
  invFun r := ⟨r, Subsemiring.mem_top r⟩
  map_mul' := (⊤ : Subsemiring R).coe_mul
  map_add' := (⊤ : Subsemiring R).coe_add

/-- The preimage of a subsemiring along a ring homomorphism is a subsemiring. -/
@[simps coe toSubmonoid]
/-
**Subsemiring.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：comap (f : R ->+* S) (s : Subsemiring S) : Subsemiring R
参数：f : R ->+* S；s : Subsemiring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subsemiring along a ring homomorphism is a subsemiring.
-/
def comap (f : R →+* S) (s : Subsemiring S) : Subsemiring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubmonoid.comap (f : R →+ S) with carrier := f ⁻¹' s }

@[simp]
/-
**Subsemiring.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_comap {s : Subsemiring S} {f : R ->+* S} {x : R} : x in s.comap f ↔ f 
x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {s : Subsemiring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
/-
**Subsemiring.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：comap_comap (s : Subsemiring T) (g : S ->+* T) (f : R ->+* S) : (s.comap g
).comap f = s.comap (g.comp f)
参数：s : Subsemiring T；g : S ->+* T；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (s : Subsemiring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-- The image of a subsemiring along a ring homomorphism is a subsemiring. -/
@[simps coe toSubmonoid]
/-
**Subsemiring.map** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：map (f : R ->+* S) (s : Subsemiring R) : Subsemiring S
参数：f : R ->+* S；s : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subsemiring along a ring homomorphism is a subsemiring.
-/
def map (f : R →+* S) (s : Subsemiring R) : Subsemiring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }

@[simp]
/-
**Subsemiring.mem_map** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`。
形式化陈述：mem_map {f : R ->+* S} {s : Subsemiring R} {y : S} : y in s.map f ↔ exists
 x in s, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_map {f : R →+* S} {s : Subsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := Iff.rfl

@[simp]
/-
**Subsemiring.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_id : s.map (RingHom.id R) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id : s.map (RingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _
/-
**Subsemiring.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_map (g : S ->+* T) (f : R ->+* S) : (s.map f).map g = s.map (g.comp f)
参数：g : S ->+* T；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : S →+* T) (f : R →+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
/-
**Subsemiring.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_le_iff_le_comap {f : R ->+* S} {s : Subsemiring R} {t : Subsemiring S}
 : s.map f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : R →+* S} {s : Subsemiring R} {t : Subsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**Subsemiring.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：gc_map_comap (f : R ->+* S) : GaloisConnection (map f) (comap f)
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.map_le_iff_le_comap`：map_le_iff_le_comap {f : R ->+* S} {s :
 Subsemiring R} {t : Subsemiring S} : s.map f <= t ↔ s <= t.comap f
-/
theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/-- A subsemiring is isomorphic to its image under an injective function -/
/-
**Subsemiring.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：equivMapOfInjective (f : R ->+* S) (hf : Function.Injective f) : s ≃+* s.m
ap f
参数：f : R ->+* S；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsemiring is isomorphic to its image under an injective function
-/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
/-
**Subsemiring.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiri
ng`。
形式化陈述：coe_equivMapOfInjective_apply (f : R ->+* S) (hf : Function.Injective f) (
x : s) : (equivMapOfInjective s f hf x : S) = f x
参数：f : R ->+* S；hf : Function.Injective f；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subsemiring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-- The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]. -/
@[simps! coe toSubmonoid]
/-
**RingHom.rangeS** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：rangeS : Subsemiring S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism is a subsemiring. See Note [range copy pattern]
.
-/
def rangeS : Subsemiring S :=
  ((⊤ : Subsemiring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
/-
**RingHom.mem_rangeS** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_rangeS {f : R →+* S} {y : S} : y ∈ f.rangeS ↔ ∃ x, f x = y :=
  Iff.rfl
/-
**RingHom.rangeS_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeS_eq_map (f : R ->+* S) : f.rangeS = (⊤ : Subsemiring R).map f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rangeS_eq_map (f : R →+* S) : f.rangeS = (⊤ : Subsemiring R).map f := by
  ext
  simp
/-
**RingHom.mem_rangeS_self** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_rangeS_self (f : R ->+* S) (x : R) : f x in f.rangeS
参数：f : R ->+* S；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.mem_rangeS`：mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ 
exists x, f x = y
-/
theorem mem_rangeS_self (f : R →+* S) (x : R) : f x ∈ f.rangeS :=
  mem_rangeS.mpr ⟨x, rfl⟩
/-
**RingHom.map_rangeS** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_rangeS : f.rangeS.map g = (g.comp f).rangeS
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.rangeS_eq_map`：rangeS_eq_map (f : R ->+* S) : f.rangeS = (⊤ : Su
bsemiring R).map f
· 使用定理 `Subsemiring.map_map`：map_map (g : S ->+* T) (f : R ->+* S) : (s.map f).m
ap g = s.map (g.comp f)
-/
theorem map_rangeS : f.rangeS.map g = (g.comp f).rangeS := by
  simpa only [rangeS_eq_map] using (⊤ : Subsemiring R).map_map g f

variable {f} in
/-
**RingHom.rangeS_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeS_eq_top : f.rangeS = ⊤ ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rangeS_eq_top : f.rangeS = ⊤ ↔ Function.Surjective f := by
  simp [← Set.range_eq_univ, SetLike.ext'_iff]

/-- The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
/-
**RingHom.fintypeRangeS** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：fintypeRangeS [Fintype R] [DecidableEq S] (f : R ->+* S) : Fintype (rangeS
 f)
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of semirings is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`.
-/
instance fintypeRangeS [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (rangeS f) :=
  Set.fintypeRange f

end RingHom

namespace Subsemiring

/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (Subsemiring R) :=
  ⟨(Nat.castRingHom R).rangeS⟩
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

@[norm_cast]
/-
**Subsemiring.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : Nat -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
-/
theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : ℕ → R) :=
  (Nat.castRingHom R).coe_rangeS
/-
**Subsemiring.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_bot {x : R} : x in (⊥ : Subsemiring R) ↔ exists n : Nat, ↑n = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.mem_rangeS`：mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ 
exists x, f x = y
-/
theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_rangeS
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]
/-
**Subsemiring.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = 
⋂ s in S, ↑s
参数：S : Set (Subsemiring R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
/-
**Subsemiring.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_sInf {S : Set (Subsemiring R)} {x : R} : x in sInf S ↔ forall p in S, 
x in p
参数：Subsemiring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/-
**Subsemiring.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Subsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ 
i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → Subsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/-
**Subsemiring.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Subsemiring R} {x : R} : x in ⨅ i, S i ↔ fo
rall i, x in S i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf {ι : Sort*} {S : ι → Subsemiring R} {x : R} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/-
**Subsemiring.sInf_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：sInf_toSubmonoid (s : Set (Subsemiring R)) : (sInf s).toSubmonoid = ⨅ t in
 s, Subsemiring.toSubmonoid t
参数：s : Set (Subsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mk'_toSubmonoid`：∀ {R : Type u} [inst : NonAssocSemiring R] 
{s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}   (ha : ↑sa 
= s), (Subsemirin…
-/
theorem sInf_toSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, Subsemiring.toSubmonoid t :=
  mk'_toSubmonoid _ _

@[simp]
/-
**Subsemiring.sInf_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：sInf_toAddSubmonoid (s : Set (Subsemiring R)) : (sInf s).toAddSubmonoid = 
⨅ t in s, Subsemiring.toAddSubmonoid t
参数：s : Set (Subsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mk'_toAddSubmonoid`：∀ {R : Type u} [inst : NonAssocSemiring 
R] {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}   (ha : ↑
sa = s), (Subsemirin…
-/
theorem sInf_toAddSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _

/-- Subsemirings of a semiring form a complete lattice. -/
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subsemirings of a semiring form a complete lattice.
-/
instance : CompleteLattice (Subsemiring R) :=
  { completeLatticeOfInf (Subsemiring R) fun _ =>
      IsGLB.of_image
        (fun {s t : Subsemiring R} => show (s : Set R) ⊆ t ↔ s ≤ t from SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ natCast_mem s n
    top := ⊤
    le_top := fun _ _ _ => mem_top _
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }
/-
**Subsemiring.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ forall x : R, x in A
参数：A : Subsemiring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subsemiring.mem_top`：mem_top (x : R) : x in (⊤ : Subsemiring R)
-/
theorem eq_top_iff' (A : Subsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

section NonAssocSemiring

variable (R)

/-- The center of a non-associative semiring `R` is the set of elements that commute and associate
with everything in `R` -/
@[simps coe toSubmonoid]
/-
**Subsemiring.center** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：center : Subsemiring R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a non-associative semiring `R` is the set of elements that commute
 and associate
with everything in `R`
-/
def center : Subsemiring R :=
  { NonUnitalSubsemiring.center R with
    one_mem' := Set.one_mem_center }

/-- The center is commutative and associative.

This is not an instance as it forms a non-defeq diamond with
`NonUnitalSubringClass.toNonUnitalRing` in the `npow` field. -/
/-
**Subsemiring.center.commSemiring'** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring.center
`。
形式化陈述：(R : Type u) → [inst : NonAssocSemiring R] → CommSemiring ↥(Subsemiring.ce
nter R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center is commutative and associative.

This is not an instance as it forms a non-defeq diamond with
`NonUnitalSubringClass.toNonUnitalRing` in the `npow` field.
-/
abbrev center.commSemiring' : CommSemiring (center R) :=
  { Submonoid.center.commMonoid', (center R).toNonAssocSemiring with }

variable {R}

/-- The center of isomorphic (not necessarily associative) semirings are isomorphic. -/
/-
**Subsemiring.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : NonAssocSemiring R] →       [i
nst_1 : NonAssocSemiring S] → R ≃+* S → ↥(Subsemiring.center R) ≃+* ↥(Subsemirin
g.center S)
参数：Subsemiring.center R；Subsemiring.center S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic (not necessarily associative) semirings are isomorphic.
-/
@[simps!] def centerCongr (e : R ≃+* S) : center R ≃+* center S :=
  NonUnitalSubsemiring.centerCongr e

/-- The center of a (not necessarily associative) semiring
is isomorphic to the center of its opposite. -/
/-
**Subsemiring.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：{R : Type u} → [inst : NonAssocSemiring R] → ↥(Subsemiring.center R) ≃+* ↥
(Subsemiring.center Rᵐᵒᵖ)
参数：Subsemiring.center R；Subsemiring.center Rᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a (not necessarily associative) semiring
is isomorphic to the center of its opposite.
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ :=
  NonUnitalSubsemiring.centerToMulOpposite

end NonAssocSemiring

section Semiring

/-- The center is commutative. -/
/-
**Subsemiring.center.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring.center`
。
形式化陈述：{R : Type u_1} → [inst : Semiring R] → CommSemiring ↥(Subsemiring.center R
)
参数：Subsemiring.center R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center is commutative.
-/
instance center.commSemiring {R} [Semiring R] : CommSemiring (center R) where
  __ := (center R).toSemiring
  __ : CommMonoid (center R) := inferInstanceAs <| CommMonoid (Submonoid.center R)

-- no instance diamond, unlike the primed version
/-
**Subsemiring.** 是 Mathlib 中的一个示例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R} [Semiring R] :
    center.commSemiring.toSemiring = Subsemiring.toSemiring (center R) := by
  with_reducible_and_instances rfl
/-
**Subsemiring.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_center_iff {R} [Semiring R] {z : R} : z in center R ↔ forall g, g * z 
= z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {R} [Semiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Subsemigroup.mem_center_iff
/-
**Subsemiring.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：decidableMemCenter {R} [Semiring R] [DecidableEq R] [Fintype R] : Decidabl
ePred (· in center R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mem_center_iff`：mem_center_iff {R} [Semiring R] {z : R} : z 
in center R ↔ forall g, g * z = z * g
-/
instance decidableMemCenter {R} [Semiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/-
**Subsemiring.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：center_eq_top (R) [CommSemiring R] : center R = ⊤
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (R) [CommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end Semiring

section Centralizer

/-- The centralizer of a set as subsemiring. -/
/-
**Subsemiring.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：centralizer {R} [Semiring R] (s : Set R) : Subsemiring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a set as subsemiring.
-/
def centralizer {R} [Semiring R] (s : Set R) : Subsemiring R :=
  { Submonoid.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]
/-
**Subsemiring.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_centralizer {R} [Semiring R] (s : Set R) : (centralizer s : Set R) = s
.centralizer
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer {R} [Semiring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl
/-
**Subsemiring.centralizer_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：centralizer_toSubmonoid {R} [Semiring R] (s : Set R) : (centralizer s).toS
ubmonoid = Submonoid.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubmonoid {R} [Semiring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl
/-
**Subsemiring.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} : z in centralize
r s ↔ forall g in s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
/-
**Subsemiring.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：center_le_centralizer {R} [Semiring R] (s) : center R <= centralizer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer {R} [Semiring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
/-
**Subsemiring.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：centralizer_le {R} [Semiring R] (s t : Set R) (h : s subseteq t) : central
izer t <= centralizer s
参数：s t : Set R；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le {R} [Semiring R] (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
/-
**Subsemiring.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiri
ng`。
形式化陈述：centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} : centralizer s
 = ⊤ ↔ s subseteq center R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/-
**Subsemiring.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：centralizer_univ {R} [Semiring R] : centralizer Set.univ = center R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ {R} [Semiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)
/-
**Subsemiring.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Subsemiring`
。
形式化陈述：le_centralizer_centralizer {R} [Semiring R] {s : Subsemiring R} : s <= cen
tralizer (centralizer (s : Set R))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma le_centralizer_centralizer {R} [Semiring R] {s : Subsemiring R} :
    s ≤ centralizer (centralizer (s : Set R)) :=
  Set.subset_centralizer_centralizer

@[simp]
/-
**Subsemiring.centralizer_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Sub
semiring`。
形式化陈述：centralizer_centralizer_centralizer {R} [Semiring R] {s : Set R} : central
izer s.centralizer.centralizer = centralizer s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.centralizer_centralizer_centralizer`：centralizer_centralizer_central
izer (S : Set M) : S.centralizer.centralizer.centralizer = S.centralizer
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_centralizer_centralizer {R} [Semiring R] {s : Set R} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end Centralizer

/-- The `Subsemiring` generated by a set. -/
/-
**Subsemiring.closure** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：closure (s : Set R) : Subsemiring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Subsemiring` generated by a set.
-/
def closure (s : Set R) : Subsemiring R :=
  sInf { S | s ⊆ S }
/-
**Subsemiring.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : Subsemiring 
R, s subseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mem_sInf`：mem_sInf {S : Set (Subsemiring R)} {x : R} : x in 
sInf S ↔ forall p in S, x in p
-/
theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subsemiring generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**Subsemiring.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：subset_closure {s : Set R} : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.mem_closure`：mem_closure {x : R} {s : Set R} : x in closure 
s ↔ forall S : Subsemiring R, s subseteq S -> x in S

--- 原说明 ---
The subsemiring generated by a set includes the set.
-/
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**Subsemiring.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_closure_of_mem {s : Set R} {x : R} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
-/
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**Subsemiring.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
/-
**Subsemiring.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_le {s : Set R} {t : Subsemiring R} : closure s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
A subsemiring `S` includes `closure s` if and only if it includes `s`.
-/
theorem closure_le {s : Set R} {t : Subsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/-
**Subsemiring.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s

--- 原说明 ---
Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`.
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
/-
**Subsemiring.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s subseteq t) (h₂ :
 t <= closure s) : closure s = t
参数：h₁ : s subseteq t；h₂ : t <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
-/
theorem closure_eq_of_le {s : Set R} {t : Subsemiring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
/-
**Subsemiring.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} : x in K.map (f : 
R ->+* S) ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : R ≃+* S} {K : Subsemiring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K := by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x using 1
/-
**Subsemiring.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) : K.map (f : R -
>+* S) = K.comap f.symm
参数：f : R ≃+* S；K : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subsemiring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)
/-
**Subsemiring.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) : K.comap (f : R
 ->+* S) = K.map f.symm
参数：f : R ≃+* S；K : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Subsemiring.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : R ≃+* 
S) (K : Subsemiring R) : K.map (f : R ->+* S) = K.comap f.symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subsemiring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subsemiring

namespace Submonoid

/-- The additive closure of a submonoid is a subsemiring. -/
/-
**Submonoid.subsemiringClosure** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：subsemiringClosure (M : Submonoid R) : Subsemiring R
参数：M : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive closure of a submonoid is a subsemiring.
-/
def subsemiringClosure (M : Submonoid R) : Subsemiring R :=
  { AddSubmonoid.closure (M : Set R) with
    one_mem' := AddSubmonoid.mem_closure.mpr fun _ hy => hy M.one_mem
    mul_mem' := MulMemClass.mul_mem_add_closure }
/-
**Submonoid.subsemiringClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subsemiringClosure_coe : (M.subsemiringClosure : Set R) = AddSubmonoid.clo
sure (M : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subsemiringClosure_coe :
    (M.subsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl
/-
**Submonoid.subsemiringClosure_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subsemiringClosure_mem {x : R} : x in M.subsemiringClosure ↔ x in AddSubmo
noid.closure (M : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subsemiringClosure_mem {x : R} :
    x ∈ M.subsemiringClosure ↔ x ∈ AddSubmonoid.closure (M : Set R) :=
  Iff.rfl
/-
**Submonoid.subsemiringClosure_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id`。
形式化陈述：subsemiringClosure_toAddSubmonoid : M.subsemiringClosure.toAddSubmonoid = 
AddSubmonoid.closure (M : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subsemiringClosure_toAddSubmonoid :
    M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl
/-
**Submonoid.subsemiringClosure_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 
`Submonoid`。
形式化陈述：∀ {R : Type u} [inst : NonAssocSemiring R] (M : Submonoid R),   M.subsemir
ingClosure.toNonUnitalSubsemiring = NonUnitalSubsemiring.closure ↑M
参数：M : Submonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSubsemiring.closure_eq_of_le`：closure_eq_of_le {s : Set R} {t :
 NonUnitalSubsemiring R} (h₁ : s subseteq t) (h₂ : t <= closure s) : closure s =
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `NonUnitalSubsemiring.mem_closure_of_mem`：mem_closure_of_mem {s : Set R} 
{x : R} (hx : x in s) : x in closure s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
@[simp] lemma subsemiringClosure_toNonUnitalSubsemiring (M : Submonoid R) :
    M.subsemiringClosure.toNonUnitalSubsemiring = .closure M := by
  refine Eq.symm (NonUnitalSubsemiring.closure_eq_of_le ?_ fun _ hx ↦ ?_)
  · simp [Submonoid.subsemiringClosure_coe]
  · simp only [Subsemiring.mem_toNonUnitalSubsemiring, subsemiringClosure_mem] at hx
    induction hx using AddSubmonoid.closure_induction <;> aesop

/-- The `Subsemiring` generated by a multiplicative submonoid coincides with the
`Subsemiring.closure` of the submonoid itself . -/
/-
**Submonoid.subsemiringClosure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure
 (M : Set R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S
· 使用定理 `Subsemiring.mem_closure`：mem_closure {x : R} {s : Set R} : x in closure 
s ↔ forall S : Subsemiring R, s subseteq S -> x in S

--- 原说明 ---
The `Subsemiring` generated by a multiplicative submonoid coincides with the
`Subsemiring.closure` of the submonoid itself .
-/
theorem subsemiringClosure_eq_closure : M.subsemiringClosure = Subsemiring.closure (M : Set R) := by
  ext
  refine
    ⟨fun hx => ?_, fun hx =>
      (Subsemiring.mem_closure.mp hx) M.subsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

end Submonoid

namespace Subsemiring

@[simp]
/-
**Subsemiring.closure_submonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = c
losure s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall S :
 Submonoid M, s subseteq S -> x in S
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `Subsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) 
: closure s <= closure t
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_submonoid_closure (s : Set R) : closure ↑(Submonoid.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Submonoid.mem_closure.mp hy) (closure s).toSubmonoid subset_closure)
    (closure_mono Submonoid.subset_closure)

/-- The elements of the subsemiring closure of `M` are exactly the elements of the additive closure
of a multiplicative submonoid `M`. -/
/-
**Subsemiring.coe_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_closure_eq (s : Set R) : (closure s : Set R) = AddSubmonoid.closure (S
ubmonoid.closure s : Set R)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.subsemiringClosure_eq_closure`：subsemiringClosure_eq_closure :
 M.subsemiringClosure = Subsemiring.closure (M : Set R)
· 使用定理 `Subsemiring.closure_submonoid_closure`：closure_submonoid_closure (s : Se
t R) : closure ↑(Submonoid.closure s) = closure s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The elements of the subsemiring closure of `M` are exactly the elements of the a
dditive closure
of a multiplicative submonoid `M`.
-/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Submonoid.closure s : Set R) := by
  simp [← Submonoid.subsemiringClosure_toAddSubmonoid, Submonoid.subsemiringClosure_eq_closure]
/-
**Subsemiring.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_closure_iff {s : Set R} {x} : x in closure s ↔ x in AddSubmonoid.closu
re (Submonoid.closure s : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Subsemiring.coe_closure_eq`：coe_closure_eq (s : Set R) : (closure s : Se
t R) = AddSubmonoid.closure (Submonoid.closure s : Set R)
-/
theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Submonoid.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
/-
**Subsemiring.closure_addSubmonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemirin
g`。
形式化陈述：closure_addSubmonoid_closure {s : Set R} : closure ↑(AddSubmonoid.closure 
s) = closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S
· 使用定理 `Subsemiring.mem_closure_iff`：mem_closure_iff {s : Set R} {x} : x in clos
ure s ↔ x in AddSubmonoid.closure (Submonoid.closure s : Set R)
· 使用定理 `Submonoid.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall S :
 Submonoid M, s subseteq S -> x in S
· 使用定理 `Subsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) 
: closure s <= closure t
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
-/
theorem closure_addSubmonoid_closure {s : Set R} :
    closure ↑(AddSubmonoid.closure s) = closure s := by
  ext x
  refine ⟨fun hx => ?_, fun hx => closure_mono AddSubmonoid.subset_closure hx⟩
  rintro - ⟨H, rfl⟩
  rintro - ⟨J, rfl⟩
  refine (AddSubmonoid.mem_closure.mp (mem_closure_iff.mp hx)) H.toAddSubmonoid fun y hy => ?_
  refine (Submonoid.mem_closure.mp hy) H.toSubmonoid fun z hz => ?_
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
/-
**Subsemiring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(one : p 1 (one_mem _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (
add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem 
hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；one : p 1 (one_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x 
+ y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_
mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `0`, `1`, and al
l elements
of `s`, and is preserved under addition and multiplication, then `p` holds for a
ll elements
of the closure of `s`.
-/
theorem closure_induction {s : Set R} {p : (x : R) → x ∈ closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let K : Subsemiring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      one_mem' := ⟨_, one⟩
      zero_mem' := ⟨_, zero⟩ }
  closure_le (t := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
/-
**Subsemiring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(one : p 1 (one_mem _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (
add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem 
hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；one : p 1 (one_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x 
+ y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_
mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership for predicates with two arguments.
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ closure s → y ∈ closure s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x ∈ closure s) (hy : y ∈ closure s) :
    p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | one => exact one_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
/-
**Subsemiring.mem_closure_iff_exists_list** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring
`。
形式化陈述：mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} : x in closur
e s ↔ exists L : List (List R), (forall t in L, forall y in t, y in s) ∧ (L.map 
List.prod).sum = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.forall_mem_singleton`：∀ {α : Type u_1} {p : α → Prop} {a : α}, (∀ x
 ∈ [a], p x) ↔ p a
· 使用定理 `List.prod_singleton`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [S
td.LawfulRightIdentity (fun x1 x2 => x1 * x2) 1] {x : α},   [x].prod = x
· 使用定理 `Std.LawfulIdentity.toLawfulRightIdentity`：∀ {α : Sort u} {op : α → α → α
} {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulRightIdentity op 
o
· 使用定理 `List.forall_mem_nil`：∀ {α : Type u_1} (p : α → Prop), ∀ x ∈ [], p x
· 使用定理 `List.forall_mem_append`：∀ {α : Type u_1} {p : α → Prop} {l₁ l₂ : List α}
, (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `List.map_singleton`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α},
 List.map f [a] = [f a]
· 使用定理 `List.sum_singleton`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [S
td.LawfulRightIdentity (fun x1 x2 => x1 + x2) 0] {x : α},   [x].sum = x
· 使用定理 `AddSemigroup.to_isLawfulIdentity`：∀ {M : Type u_4} [inst : AddZeroClass 
M], Std.LawfulIdentity (fun x1 x2 => x1 + x2) 0
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.sum_append`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 + x2) 0]   [Std.Associative fun x1 x2 => x1 
+ x2]…
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `Subsemiring.mem_closure_iff`：mem_closure_iff {s : Set R} {x} : x in clos
ure s ↔ x in AddSubmonoid.closure (Submonoid.closure s : Set R)
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Subsemiring.list_prod_mem`：∀ {R : Type u_1} [inst : Semiring R] (s : Sub
semiring R) {l : List R}, (∀ x ∈ l, x ∈ s) → l.prod ∈ s
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
-/
theorem mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} :
    x ∈ closure s ↔ ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map List.prod).sum = x := by
  constructor
  · intro hx
    rw [mem_closure_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      suffices ∃ t : List R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x from
        let ⟨t, ht1, ht2⟩ := this
        ⟨[t], List.forall_mem_singleton.2 ht1, by
          rw [List.map_singleton, List.sum_singleton, ht2]⟩
      induction hx using Submonoid.closure_induction with
      | mem x hx => exact ⟨[x], List.forall_mem_singleton.2 hx, List.prod_singleton⟩
      | one => exact ⟨[], List.forall_mem_nil _, rfl⟩
      | mul x y _ _ ht hu =>
        obtain ⟨⟨t, ht1, ht2⟩, ⟨u, hu1, hu2⟩⟩ := And.intro ht hu
        exact ⟨t ++ u, List.forall_mem_append.2 ⟨ht1, hu1⟩, by rw [List.prod_append, ht2, hu2]⟩
    | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
    | add x y _ _ hL hM =>
      obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
      exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩
  · rintro ⟨L, HL1, rfl⟩
    exact
      list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_map.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => subset_closure <| HL1 t ht1 y hy

variable (R) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**Subsemiring.gi** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：(R : Type u) → [inst : NonAssocSemiring R] → GaloisInsertion Subsemiring.c
losure SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

/-- Closure of a subsemiring `S` equals `S`. -/
@[simp]
/-
**Subsemiring.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_eq (s : Subsemiring R) : closure (s : Set R) = s
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a subsemiring `S` equals `S`.
-/
theorem closure_eq (s : Subsemiring R) : closure (s : Set R) = s :=
  (Subsemiring.gi R).l_u_eq s

@[simp]
/-
**Subsemiring.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_empty : closure (∅ : Set R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_empty : closure (∅ : Set R) = ⊥ :=
  (Subsemiring.gi R).gc.l_bot

@[simp]
/-
**Subsemiring.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_univ : closure (Set.univ : Set R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.closure_eq`：closure_eq (s : Subsemiring R) : closure (s : Se
t R) = s
· 使用定理 `Subsemiring.coe_top`：coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
/-
**Subsemiring.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_union (s t : Set R) : closure (s union t) = closure s ⊔ closure t
参数：s t : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_union (s t : Set R) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subsemiring.gi R).gc.l_sup
/-
**Subsemiring.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_iUnion {ι} (s : ι -> Set R) : closure (⋃ i, s i) = ⨆ i, closure (s
 i)
参数：s : ι -> Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_iUnion {ι} (s : ι → Set R) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subsemiring.gi R).gc.l_iSup
/-
**Subsemiring.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t in s, closure t
参数：s : Set (Set R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_sUnion (s : Set (Set R)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subsemiring.gi R).gc.l_sSup

@[simp]
/-
**Subsemiring.closure_singleton_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_singleton_natCast (n : Nat) : closure {(n : R)} = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `natCast_mem`：natCast_mem [AddSubmonoidWithOneClass S R] (n : Nat) : (n :
 R) in s
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem closure_singleton_natCast (n : ℕ) : closure {(n : R)} = ⊥ :=
  bot_unique <| closure_le.2 <| Set.singleton_subset_iff.mpr <| natCast_mem _ _

@[simp]
/-
**Subsemiring.closure_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_singleton_zero : closure {(0 : R)} = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_singleton_natCast`：closure_singleton_natCast (n : Na
t) : closure {(n : R)} = ⊥
-/
theorem closure_singleton_zero : closure {(0 : R)} = ⊥ := mod_cast closure_singleton_natCast 0

@[simp]
/-
**Subsemiring.closure_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_singleton_one : closure {(1 : R)} = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_singleton_natCast`：closure_singleton_natCast (n : Na
t) : closure {(n : R)} = ⊥
-/
theorem closure_singleton_one : closure {(1 : R)} = ⊥ := mod_cast closure_singleton_natCast 1

@[simp]
/-
**Subsemiring.closure_insert_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_insert_natCast (n : Nat) (s : Set R) : closure (insert (n : R) s) 
= closure s
参数：n : Nat；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Subsemiring.closure_union`：closure_union (s t : Set R) : closure (s unio
n t) = closure s ⊔ closure t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsemiring.closure_singleton_natCast`：closure_singleton_natCast (n : Na
t) : closure {(n : R)} = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_insert_natCast (n : ℕ) (s : Set R) : closure (insert (n : R) s) = closure s := by
  rw [Set.insert_eq, closure_union]
  simp

@[simp]
/-
**Subsemiring.closure_insert_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_insert_zero (s : Set R) : closure (insert 0 s) = closure s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_insert_natCast`：closure_insert_natCast (n : Nat) (s 
: Set R) : closure (insert (n : R) s) = closure s
-/
theorem closure_insert_zero (s : Set R) : closure (insert 0 s) = closure s :=
  mod_cast closure_insert_natCast 0 s

@[simp]
/-
**Subsemiring.closure_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：closure_insert_one (s : Set R) : closure (insert 1 s) = closure s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_insert_natCast`：closure_insert_natCast (n : Nat) (s 
: Set R) : closure (insert (n : R) s) = closure s
-/
theorem closure_insert_one (s : Set R) : closure (insert 1 s) = closure s :=
  mod_cast closure_insert_natCast 1 s
/-
**Subsemiring.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_sup (s t : Subsemiring R) (f : R ->+* S) : (s ⊔ t).map f = s.map f ⊔ t
.map f
参数：s t : Subsemiring R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem map_sup (s t : Subsemiring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**Subsemiring.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_iSup {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring R) : (iSup s).ma
p f = ⨆ i, (s i).map f
参数：f : R ->+* S；s : ι -> Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**Subsemiring.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_inf (s t : Subsemiring R) (f : R ->+* S) (hf : Function.Injective f) :
 (s ⊓ t).map f = s.map f ⊓ t.map f
参数：s t : Subsemiring R；f : R ->+* S；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (s t : Subsemiring R) (f : R →+* S) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)
/-
**Subsemiring.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective 
f) (s : ι -> Subsemiring R) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : R ->+* S；hf : Function.Injective f；s : ι -> Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsemiring.coe_map`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemirin
g R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (s : Subsemiring R),   ↑(Subsem
iring.map…
· 使用定理 `Subsemiring.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subsemiring R} : (↑
(⨅ i, S i) : Set R) = ⋂ i, S i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : R →+* S) (hf : Function.Injective f)
    (s : ι → Subsemiring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**Subsemiring.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：comap_inf (s t : Subsemiring S) (f : R ->+* S) : (s ⊓ t).comap f = s.comap
 f ⊓ t.comap f
参数：s t : Subsemiring S；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem comap_inf (s t : Subsemiring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
/-
**Subsemiring.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：comap_iInf {ι : Sort*} (f : R ->+* S) (s : ι -> Subsemiring S) : (iInf s).
comap f = ⨅ i, (s i).comap f
参数：f : R ->+* S；s : ι -> Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subsemiring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**Subsemiring.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_bot (f : R ->+* S) : (⊥ : Subsemiring R).map f = ⊥
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem map_bot (f : R →+* S) : (⊥ : Subsemiring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**Subsemiring.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：comap_top (f : R ->+* S) : (⊤ : Subsemiring S).comap f = ⊤
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
-/
theorem comap_top (f : R →+* S) : (⊤ : Subsemiring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `Subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
/-
**Subsemiring.prod** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S)
参数：s : Subsemiring R；t : Subsemiring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is 
`s × t`
as a subsemiring of `R × S`.
-/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

@[norm_cast]
/-
**Subsemiring.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_prod (s : Subsemiring R) (t : Subsemiring S) : (s.prod t : Set (R × S)
) = (s : Set R) ×ˢ (t : Set S)
参数：s : Subsemiring R；t : Subsemiring S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : Subsemiring R) (t : Subsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl
/-
**Subsemiring.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} : p in s.prod
 t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : Subsemiring R} {t : Subsemiring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[gcongr, mono]
/-
**Subsemiring.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subsemiring S⦄ 
(ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
/-
**Subsemiring.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.
prod t
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.prod_mono`：prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ <= s₂)
 ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.prod t :=
  prod_mono (le_refl s)
/-
**Subsemiring.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.p
rod t
参数：t : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.prod_mono`：prod_mono ⦃s₁ s₂ : Subsemiring R⦄ (hs : s₁ <= s₂)
 ⦃t₁ t₂ : Subsemiring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_left (t : Subsemiring S) : Monotone fun s : Subsemiring R => s.prod t :=
  fun _ _ hs => prod_mono hs (le_refl t)
/-
**Subsemiring.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingH
om.fst R S)
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (s : Subsemiring R) : s.prod (⊤ : Subsemiring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod]
/-
**Subsemiring.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingH
om.snd R S)
参数：s : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.ext`：ext {S T : Subsemiring R} (h : forall x, x in S ↔ x in 
T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_prod (s : Subsemiring S) : (⊤ : Subsemiring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/-
**Subsemiring.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsemiring.top_prod`：top_prod (s : Subsemiring S) : (⊤ : Subsemiring R)
.prod s = s.comap (RingHom.snd R S)
· 使用定理 `Subsemiring.comap_top`：comap_top (f : R ->+* S) : (⊤ : Subsemiring S).co
map f = ⊤
-/
theorem top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[simp]
/-
**Subsemiring._root_.RingHom.rangeS_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiri
ng`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.RingHom.rangeS_prodMap (f : R →+* S) (g : S →+* T) :
    (f.prodMap g).rangeS = Subsemiring.prod f.rangeS g.rangeS :=
  SetLike.coe_injective Set.range_prodMap
/-
**Subsemiring.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring R] [inst_1 : NonAssoc
Semiring S],   Subsemiring.center (R × S) = (Subsemiring.center R).prod (Subsemi
ring.center S)
参数：R × S；Subsemiring.center R；Subsemiring.center S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/-- Product of subsemirings is isomorphic to their product as monoids. -/
/-
**Subsemiring.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t
参数：s : Subsemiring R；t : Subsemiring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of subsemirings is isomorphic to their product as monoids.
-/
def prodEquiv (s : Subsemiring R) (t : Subsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
/-
**Subsemiring.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R} (hS : 
Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑s
m = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).to
Submo…
· 使用定理 `Submonoid.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [Nonempty ι] {S
 : ι -> Submonoid M} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Submonoid M) : Se
t M) = ⋃ i, S i
· 使用定理 `AddSubmonoid.coe_iSup_of_directed`：∀ {M : Type u_1} [inst : AddZeroClass
 M] {ι : Sort u_4} [Nonempty ι] {S : ι → AddSubmonoid M},   Directed (fun x1 x2 
=> x1 ≤ x2) S → ↑(⨆ i, …
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : Subsemiring R :=
    Subsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubmonoid) (Submonoid.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩
/-
**Subsemiring.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subsemiring R} (hS : 
Directed (· <= ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, S i
参数：hS : Directed (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempt
y ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S 
i) ↔ exists i, x in S …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : Subsemiring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]
/-
**Subsemiring.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：mem_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : 
DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s
参数：Subsemiring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Subsemiring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempt
y ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S 
i) ↔ exists i, x in S …
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]
/-
**Subsemiring.coe_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：coe_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty) (hS : 
DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s
参数：Subsemiring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.mem_sSup_of_directedOn`：mem_sSup_of_directedOn {S : Set (Sub
semiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup
 S ↔ exists s in S, x in…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sSup_of_directedOn {S : Set (Subsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
/-
**Subsemiring.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> Subsemiring R} [h
S : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsMulCommuta
tive (⨆ i, S i : Subsemiring R)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι : Nonempt
y ι] {S : ι -> Subsemiring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemir
ing R) : Set R) = ⋃ i,…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用定理 `Subsemigroup.coe_iSup_of_directed`：coe_iSup_of_directed {S : ι -> Subsem
igroup M} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃
 i, S i
· 使用定理 `Subsemigroup.isMulCommutative_iSup`：isMulCommutative_iSup {S : ι -> Subs
emigroup M} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) 
: IsMulCommutative (⨆ i,…
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι]
    {S : ι → Subsemiring R} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (· ≤ ·) S) : IsMulCommutative (⨆ i, S i : Subsemiring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir
/-
**Subsemiring.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o Subsemiring R} [hS : forall i, IsMulCommutative (S i)] : Is
MulCommutative (⨆ i, S i : Subsemiring R)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : Sort*} [No
nempty ι] {S : ι -> Subsemiring R} [hS : forall i, IsMulCommutative (S i)] (dir 
: Directed (· <= ·) S) …
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subsemiring R} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subsemiring R) :=
  isMulCommutative_iSup S.monotone.directed_le

end Subsemiring

namespace RingHom

variable {s : Subsemiring R}
variable {σR σS : Type*}
variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

open Subsemiring

/-- Restriction of a ring homomorphism to a subsemiring of the codomain. -/
@[implicit_reducible]
/-
**RingHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：codRestrict (f : R ->+* S) (s : σS) (h : forall x, f x in s) : R ->+* s
参数：f : R ->+* S；s : σS；h : forall x, f x in s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…

--- 原说明 ---
Restriction of a ring homomorphism to a subsemiring of the codomain.
-/
def codRestrict (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) : R →+* s :=
  { (f : R →* S).codRestrict s h, (f : R →+ S).codRestrict s h with toFun := fun n => ⟨f n, h n⟩ }

@[simp]
/-
**RingHom.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：codRestrict_apply (f : R ->+* S) (s : σS) (h : forall x, f x in s) (x : R)
 : (f.codRestrict s h x : S) = f x
参数：f : R ->+* S；s : σS；h : forall x, f x in s；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply (f : R →+* S) (s : σS) (h : ∀ x, f x ∈ s) (x : R) :
    (f.codRestrict s h x : S) = f x :=
  rfl
/-
**RingHom.injective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：injective_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} : F
unction.Injective (f.codRestrict s h) ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
-/
theorem injective_codRestrict {f : R →+* S} {s : σS} {h : ∀ x, f x ∈ s} :
    Function.Injective (f.codRestrict s h) ↔ Function.Injective f :=
  Set.injective_codRestrict h
/-
**RingHom.rangeS_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeS_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} : rang
eS (codRestrict f s h) = Subsemiring.comap (SubsemiringClass.subtype s) f.rangeS
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_codRestrict`：∀ {α : Type u_1} {ι : Sort u_5} {f : ι → α} {s : 
Set α} (h : ∀ (x : ι), f x ∈ s),   Set.range (Set.codRestrict f s h) = Subtype.v
al ⁻¹' Set.…
-/
theorem rangeS_codRestrict {f : R →+* S} {s : σS} {h : ∀ x, f x ∈ s} :
    rangeS (codRestrict f s h) = Subsemiring.comap (SubsemiringClass.subtype s) f.rangeS :=
  SetLike.coe_injective <| Set.range_codRestrict h
/-
**RingHom.surjective_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：surjective_codRestrict {f : R ->+* S} {s : σS} {h : forall x, f x in s} : 
Function.Surjective (codRestrict f s h) ↔ f.rangeS = ofClass s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.surjective_codRestrict`：surjective_codRestrict {f : ι -> α} {s : Set
 α} (h : forall x, f x in s) : (s.codRestrict f h).Surjective ↔ range f = s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem surjective_codRestrict {f : R →+* S} {s : σS} {h : ∀ x, f x ∈ s} :
    Function.Surjective (codRestrict f s h) ↔ f.rangeS = ofClass s :=
  (Set.surjective_codRestrict h).trans <| .symm <| SetLike.coe_set_eq.symm

/-- The ring homomorphism from the preimage of `s` to `s`. -/
/-
**RingHom.restrict** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：restrict (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x in s) 
: s' ->+* s
参数：f : R ->+* S；s' : σR；s : σS；h : forall x in s', f x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the preimage of `s` to `s`.
-/
def restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) : s' →+* s :=
  (f.domRestrict s').codRestrict s fun x => h x x.2

@[simp]
/-
**RingHom.coe_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_restrict_apply (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', 
f x in s) (x : s') : (f.restrict s' s h x : S) = f x
参数：f : R ->+* S；s' : σR；s : σS；h : forall x in s', f x in s；x : s'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrict_apply (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) (x : s') :
    (f.restrict s' s h x : S) = f x :=
  rfl

@[simp]
/-
**RingHom.comp_restrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：comp_restrict (f : R ->+* S) (s' : σR) (s : σS) (h : forall x in s', f x i
n s) : (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (Subsemiri
ngClass.subtype s')
参数：f : R ->+* S；s' : σR；s : σS；h : forall x in s', f x in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_restrict (f : R →+* S) (s' : σR) (s : σS) (h : ∀ x ∈ s', f x ∈ s) :
    (SubsemiringClass.subtype s).comp (f.restrict s' s h) = f.comp (SubsemiringClass.subtype s') :=
  rfl

@[simp]
/-
**RingHom.domRestrict_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：domRestrict_comp_codRestrict (g : S ->+* T) (f : R ->+* S) (p : Subsemirin
g S) (h : forall c, f c in p) : (g.domRestrict p).comp (f.codRestrict p h) = g.c
omp f
参数：g : S ->+* T；f : R ->+* S；p : Subsemiring S；h : forall c, f c in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem domRestrict_comp_codRestrict (g : S →+* T) (f : R →+* S) (p : Subsemiring S)
    (h : ∀ c, f c ∈ p) :
    (g.domRestrict p).comp (f.codRestrict p h) = g.comp f :=
  rfl

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**RingHom.rangeSRestrict** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：rangeSRestrict (f : R ->+* S) : R ->+* f.rangeS
参数：f : R ->+* S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `RingHom.mem_rangeS_self`：mem_rangeS_self (f : R ->+* S) (x : R) : f x in
 f.rangeS

--- 原说明 ---
Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`.
-/
def rangeSRestrict (f : R →+* S) : R →+* f.rangeS :=
  f.codRestrict (R := R) (S := S) (σS := Subsemiring S) f.rangeS f.mem_rangeS_self

@[simp]
/-
**RingHom.coe_rangeSRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_rangeSRestrict (f : R ->+* S) (x : R) : (f.rangeSRestrict x : S) = f x
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rangeSRestrict (f : R →+* S) (x : R) : (f.rangeSRestrict x : S) = f x :=
  rfl
/-
**RingHom.rangeSRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeSRestrict_surjective (f : R ->+* S) : Function.Surjective f.rangeSRes
trict
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_rangeS`：mem_rangeS {f : R ->+* S} {y : S} : y in f.rangeS ↔ 
exists x, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem rangeSRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeSRestrict :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩
/-
**RingHom.rangeS_top_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeS_top_iff_surjective {f : R ->+* S} : f.rangeS = (⊤ : Subsemiring S) 
↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
· 使用定理 `Subsemiring.coe_top`：coe_top : ((⊤ : Subsemiring R) : Set R) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem rangeS_top_iff_surjective {f : R →+* S} :
    f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_rangeS, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/-
**RingHom.rangeS_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeS_top_of_surjective (f : R ->+* S) (hf : Function.Surjective f) : f.r
angeS = (⊤ : Subsemiring S)
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.rangeS_top_iff_surjective`：rangeS_top_iff_surjective {f : R ->+*
 S} : f.rangeS = (⊤ : Subsemiring S) ↔ Function.Surjective f

--- 原说明 ---
The range of a surjective ring homomorphism is the whole of the codomain.
-/
theorem rangeS_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.rangeS = (⊤ : Subsemiring S) :=
  rangeS_top_iff_surjective.2 hf

/-- If two ring homomorphisms are equal on a set, then they are equal on its subsemiring closure. -/
/-
**RingHom.eqOn_sclosure** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eqOn_sclosure {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn
 f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t

--- 原说明 ---
If two ring homomorphisms are equal on a set, then they are equal on its subsemi
ring closure.
-/
theorem eqOn_sclosure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusS g from closure_le.2 h
/-
**RingHom.eq_of_eqOn_stop** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_of_eqOn_stop {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : 
f = g
参数：h : Set.EqOn f g (⊤ : Subsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subsemiring.mem_top`：mem_top (x : R) : x in (⊤ : Subsemiring R)
-/
theorem eq_of_eqOn_stop {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subsemiring R)) : f = g :=
  ext fun _ => h (mem_top _)
/-
**RingHom.eq_of_eqOn_sdense** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h : s
.EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.eq_of_eqOn_stop`：eq_of_eqOn_stop {f g : R ->+* S} (h : Set.EqOn 
f g (⊤ : Subsemiring R)) : f = g
· 使用定理 `RingHom.eqOn_sclosure`：eqOn_sclosure {f g : R ->+* S} {s : Set R} (h : S
et.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_stop <| hs ▸ eqOn_sclosure h
/-
**RingHom.sclosure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：sclosure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (cl
osure s).comap f
参数：f : R ->+* S；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subsemiring.mem_comap`：mem_comap {s : Subsemiring S} {f : R ->+* S} {x :
 R} : x in s.comap f ↔ f x in s
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
-/
theorem sclosure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
/-
**RingHom.map_closureS** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_closureS (f : R ->+* S) (s : Set R) : (closure s).map f = closure (f '
' s)
参数：f : R ->+* S；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Subsemiring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection
 (map f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `Subsemiring.coe_comap`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemir
ing R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (s : Subsemiring S),   ↑(Subs
emiring.com…

--- 原说明 ---
The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set.
-/
theorem map_closureS (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subsemiring.gi S).gc (Subsemiring.gi R).gc
    fun _ ↦ coe_comap _ _

@[simp]
/-
**RingHom.domRestrict_comp_rangeSRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：domRestrict_comp_rangeSRestrict (g : S ->+* T) (f : R ->+* S) : (g.domRest
rict f.rangeS).comp (f.rangeSRestrict) = g.comp f
参数：g : S ->+* T；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
-/
theorem domRestrict_comp_rangeSRestrict (g : S →+* T) (f : R →+* S) :
    (g.domRestrict f.rangeS).comp (f.rangeSRestrict) = g.comp f :=
  rfl

end RingHom

namespace Subsemiring

open RingHom

/-- The ring homomorphism associated to an inclusion of subsemirings. -/
/-
**Subsemiring.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subsemiring`。
形式化陈述：inclusion {S T : Subsemiring R} (h : S <= T) : S ->+* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R

--- 原说明 ---
The ring homomorphism associated to an inclusion of subsemirings.
-/
def inclusion {S T : Subsemiring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2
/-
**Subsemiring.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：inclusion_injective {S T : Subsemiring R} (h : S <= T) : Function.Injectiv
e (inclusion h)
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inclusion_injective`：inclusion_injective (h : s subseteq t) : (inclu
sion h).Injective
-/
theorem inclusion_injective {S T : Subsemiring R} (h : S ≤ T) :
    Function.Injective (inclusion h) := Set.inclusion_injective h

@[simp]
/-
**Subsemiring.rangeS_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s
参数：s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe

@[simp]
/-
**Subsemiring.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：range_fst : (fst R S).rangeS = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.rangeS_top_of_surjective`：rangeS_top_of_surjective (f : R ->+* S
) (hf : Function.Surjective f) : f.rangeS = (⊤ : Subsemiring S)
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem range_fst : (fst R S).rangeS = ⊤ :=
  (fst R S).rangeS_top_of_surjective <| Prod.fst_surjective

@[simp]
/-
**Subsemiring.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：range_snd : (snd R S).rangeS = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.rangeS_top_of_surjective`：rangeS_top_of_surjective (f : R ->+* S
) (hf : Function.Surjective f) : f.rangeS = (⊤ : Subsemiring S)
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem range_snd : (snd R S).rangeS = ⊤ :=
  (snd R S).rangeS_top_of_surjective <| Prod.snd_surjective

@[simp]
/-
**Subsemiring.prod_bot_sup_bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) : s.prod ⊥ ⊔
 prod ⊥ t = s.prod t
参数：s : Subsemiring R；t : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Subsemiring.prod_mono_right`：prod_mono_right (s : Subsemiring R) : Monot
one fun t : Subsemiring S => s.prod t
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Subsemiring.prod_mono_left`：prod_mono_left (t : Subsemiring S) : Monoton
e fun s : Subsemiring R => s.prod t
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Prod.fst_mul_snd`：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N
) : (p.fst, 1) * (1, p.snd) = p
-/
theorem prod_bot_sup_bot_prod (s : Subsemiring R) (t : Subsemiring S) :
    s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subsemiring

namespace RingEquiv

variable {s t : Subsemiring R}

/-- Makes the identity isomorphism from a proof two subsemirings of a multiplicative
monoid are equal. -/
/-
**RingEquiv.subsemiringCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：subsemiringCongr (h : s = t) : s ≃+* t
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes the identity isomorphism from a proof two subsemirings of a multiplicative
monoid are equal.
-/
def subsemiringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.rangeS`. -/
/-
**RingEquiv.ofLeftInverseS** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverseS {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) 
: R ≃+* f.rangeS
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.rangeS`.
-/
def ofLeftInverseS {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.rangeS :=
  { f.rangeSRestrict with
    toFun := fun x => f.rangeSRestrict x
    invFun := fun x => (g ∘ f.rangeS.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <| by
        let ⟨x', hx'⟩ := RingHom.mem_rangeS.mp x.prop
        simp [← hx', h x'] }

@[simp]
/-
**RingEquiv.ofLeftInverseS_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverseS_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse
 g f) (x : R) : ↑(ofLeftInverseS h x) = f x
参数：h : Function.LeftInverse g f；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverseS_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverseS h x) = f x :=
  rfl

@[simp]
/-
**RingEquiv.ofLeftInverseS_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverseS_symm_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftIn
verse g f) (x : f.rangeS) : (ofLeftInverseS h).symm x = g x
参数：h : Function.LeftInverse g f；x : f.rangeS。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverseS_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.rangeS) : (ofLeftInverseS h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiringMap e s` is the induced equivalence between `s` and `s.map e` -/
/-
**RingEquiv.subsemiringMap** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map (e : R ->+*
 S)
参数：e : R ≃+* S；s : Subsemiring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence `e : R ≃+* S` of semirings and a subsemiring `s` of `R`,
`subsemiringMap e s` is the induced equivalence between `s` and `s.map e`
-/
def subsemiringMap (e : R ≃+* S) (s : Subsemiring R) : s ≃+* s.map (e : R →+* S) :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid, e.toMulEquiv.submonoidMap s.toSubmonoid with }

@[simp]
/-
**RingEquiv.subsemiringMap_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：subsemiringMap_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s) : ((sub
semiringMap e s) x : S) = e x
参数：e : R ≃+* S；s : Subsemiring R；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem subsemiringMap_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s) :
    ((subsemiringMap e s) x : S) = e x :=
  rfl

@[simp]
/-
**RingEquiv.subsemiringMap_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：subsemiringMap_symm_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s.map
 e.toRingHom) : ((subsemiringMap e s).symm x : R) = e.symm x
参数：e : R ≃+* S；s : Subsemiring R；x : s.map e.toRingHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem subsemiringMap_symm_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s.map e.toRingHom) :
    ((subsemiringMap e s).symm x : R) = e.symm x :=
  rfl

end RingEquiv

/-! ### Actions by `Subsemiring`s

These are just copies of the definitions about `Submonoid` starting from `Submonoid.mulAction`.
The only new result is `Subsemiring.module`.

When `R` is commutative, `Algebra.ofSubsemiring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subsemiring

variable {R' α β : Type*}

variable {S' : Type*} [SetLike S' R'] (s : S)

section NonAssocSemiring

variable [NonAssocSemiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.smul** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：smul [SMul R' α] (S : Subsemiring R') : SMul S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance smul [SMul R' α] (S : Subsemiring R') : SMul S α :=
  inferInstance
/-
**Subsemiring.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R
') • m
参数：g : S；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul R' α] {S : Subsemiring R'} (g : S) (m : α) : g • m = (g : R') • m :=
  rfl
/-
**Subsemiring.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：smulCommClass_left [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subs
emiring R') : SMulCommClass S α β
参数：S : Subsemiring R'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSMulCommClassSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul M'
 β]   [inst_2 : SMul α β] […
-/
instance smulCommClass_left [SMul R' β] [SMul α β] [SMulCommClass R' α β] (S : Subsemiring R') :
    SMulCommClass S α β :=
  inferInstance
/-
**Subsemiring.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：smulCommClass_right [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Sub
semiring R') : SMulCommClass α S β
参数：S : Subsemiring R'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSMulCommClassSubtypeMem_1`：∀ {M' : Type u_1} {α : Type u_2
} {β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul 
α β]   [inst_2 : SMul M' β] […
-/
instance smulCommClass_right [SMul α β] [SMul R' β] [SMulCommClass α R' β] (S : Subsemiring R') :
    SMulCommClass α S β :=
  inferInstance
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Semiring R] [MulAction R M] :
    SMulCommClass R (Subsemiring.center R) M :=
  inferInstanceAs <| SMulCommClass R (Submonoid.center R) M
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Semiring R] [MulAction R M] :
    SMulCommClass (Subsemiring.center R) R M :=
  inferInstanceAs <| SMulCommClass (Submonoid.center R) R M

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
/-
**Subsemiring.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：isScalarTower [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β] (S
 : Subsemiring R') : IsScalarTower S α β
参数：S : Subsemiring R'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instIsScalarTowerSubtypeMem`：∀ {M' : Type u_1} {α : Type u_2} 
{β : Type u_3} {S' : Type u_4} [inst : SetLike S' M'] (s : S') [inst_1 : SMul α 
β]   [inst_2 : SMul M' α] […

--- 原说明 ---
Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc
`.
-/
instance isScalarTower [SMul α β] [SMul R' α] [SMul R' β] [IsScalarTower R' α β]
    (S : Subsemiring R') :
    IsScalarTower S α β :=
  inferInstance
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {M' α : Type*} [SMul M' α] {S' : Type*}
    [SetLike S' M'] (s : S') [FaithfulSMul M' α] : FaithfulSMul s α :=
  ⟨fun h => Subtype.ext <| eq_of_smul_eq_smul h⟩
/-
**Subsemiring.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：faithfulSMul [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R') : Faithf
ulSMul S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.instFaithfulSMulSubtypeMem`：∀ {M' : Type u_5} {α : Type u_6}
 [inst : SMul M' α] {S' : Type u_7} [inst_1 : SetLike S' M'] (s : S')   [Faithfu
lSMul M' α], FaithfulSMul (↥…
-/
instance faithfulSMul [SMul R' α] [FaithfulSMul R' α] (S : Subsemiring R') : FaithfulSMul S α :=
  inferInstance
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {S' : Type*} [SetLike S' R'] [SubsemiringClass S' R'] (s : S')
    [Zero α] [SMulWithZero R' α] : SMulWithZero s α where
  smul_zero r := smul_zero (r : R')
  zero_smul := zero_smul R'

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance [Zero α] [SMulWithZero R' α] (S : Subsemiring R') : SMulWithZero S α :=
  inferInstance

end NonAssocSemiring

variable [Semiring R']

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：mulAction [MulAction R' α] (S : Subsemiring R') : MulAction S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance mulAction [MulAction R' α] (S : Subsemiring R') : MulAction S α :=
  inferInstance

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：distribMulAction [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R'
) : DistribMulAction S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance distribMulAction [AddMonoid α] [DistribMulAction R' α] (S : Subsemiring R') :
    DistribMulAction S α :=
  inferInstance

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：mulDistribMulAction [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring
 R') : MulDistribMulAction S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction R' α] (S : Subsemiring R') :
    MulDistribMulAction S α :=
  inferInstance
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {S' : Type*} [SetLike S' R'] [SubsemiringClass S' R'] (s : S')
    [Zero α] [MulActionWithZero R' α] : MulActionWithZero s α where
  smul_zero r := smul_zero (r : R')
  zero_smul := zero_smul R'

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.mulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：mulActionWithZero [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') :
 MulActionWithZero S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance mulActionWithZero [Zero α] [MulActionWithZero R' α] (S : Subsemiring R') :
    MulActionWithZero S α :=
  inferInstance
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [AddCommMonoid α] [Module R' α] {S' : Type*} [SetLike S' R']
    [SubsemiringClass S' R'] (s : S') : Module s α where
  toDistribMulAction := inferInstance
  add_smul r₁ r₂ := add_smul (r₁ : R') r₂
  zero_smul := zero_smul R'

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.module** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
形式化陈述：module [AddCommMonoid α] [Module R' α] (S : Subsemiring R') : Module S α
参数：S : Subsemiring R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance module [AddCommMonoid α] [Module R' α] (S : Subsemiring R') : Module S α :=
  inferInstance

/-- The action by a subsemiring is the action by the underlying semiring. -/
/-
**Subsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `Subsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying semiring.
-/
instance [Semiring α] [MulSemiringAction R' α] (S : Subsemiring R') : MulSemiringAction S α :=
  inferInstance

/-- The center of a semiring acts commutatively on that semiring. -/
/-
**Subsemiring.center.smulCommClass_left** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring.c
enter`。
形式化陈述：∀ {R' : Type u_1} [inst : Semiring R'], SMulCommClass (↥(Subsemiring.cente
r R')) R' R'
参数：↥(Subsemiring.center R')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.center.smulCommClass_left`：∀ {M : Type u_1} [inst : Monoid M],
 SMulCommClass (↥(Submonoid.center M)) M M

--- 原说明 ---
The center of a semiring acts commutatively on that semiring.
-/
instance center.smulCommClass_left : SMulCommClass (center R') R' R' :=
  Submonoid.center.smulCommClass_left

/-- The center of a semiring acts commutatively on that semiring. -/
/-
**Subsemiring.center.smulCommClass_right** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring.
center`。
形式化陈述：∀ {R' : Type u_1} [inst : Semiring R'], SMulCommClass R' (↥(Subsemiring.ce
nter R')) R'
参数：↥(Subsemiring.center R')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.center.smulCommClass_right`：∀ {M : Type u_1} [inst : Monoid M]
, SMulCommClass M (↥(Submonoid.center M)) M

--- 原说明 ---
The center of a semiring acts commutatively on that semiring.
-/
instance center.smulCommClass_right : SMulCommClass R' (center R') R' :=
  Submonoid.center.smulCommClass_right
/-
**Subsemiring.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Subs
emiring`。
形式化陈述：closure_le_centralizer_centralizer (s : Set R') : closure s <= centralizer
 (centralizer s)
参数：s : Set R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set R') :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a commutative semiring. -/
/-
**Subsemiring.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：isMulCommutative_closure {s : Set R'} (hcomm : forall x in s, forall y in 
s, x * y = y * x) : IsMulCommutative (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemiring.closure_le_centralizer_centralizer`：closure_le_centralizer_c
entralizer (s : Set R') : closure s <= centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `Subsemiring.instSubsemiringClass`：∀ {R : Type u} [inst : NonAssocSemirin
g R], SubsemiringClass (Subsemiring R) R
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a commutative semi
ring.
-/
theorem isMulCommutative_closure {s : Set R'} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative semiring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/-
**Subsemiring.closureCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subsemiring
`。
形式化陈述：closureCommSemiringOfComm {s : Set R'} (hcomm : forall x in s, forall y in
 s, x * y = y * x) : CommSemiring (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.isMulCommutative_closure`：isMulCommutative_closure {s : Set 
R'} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (cl
osure s)

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a commutative semi
ring.
-/
abbrev closureCommSemiringOfComm {s : Set R'} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    CommSemiring (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance
/-
**Subsemiring.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `Subsemirin
g`。
形式化陈述：instIsMulCommutative_closure {S : Type*} [SetLike S R'] [MulMemClass S R']
 (s : S) [IsMulCommutative s] : IsMulCommutative (closure (s : Set R'))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.isMulCommutative_closure`：isMulCommutative_closure {s : Set 
R'} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (cl
osure s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S R'] [MulMemClass S R'] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set R')) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

end Subsemiring

end Actions

namespace Subsemiring

/-
**Subsemiring.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_comap_eq (f : R ->+* S) (t : Subsemiring S) : (t.comap f).map f = t ⊓ 
f.rangeS
参数：f : R ->+* S；t : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : R →+* S) (t : Subsemiring S) : (t.comap f).map f = t ⊓ f.rangeS :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range
/-
**Subsemiring.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subsemiring`。
形式化陈述：map_comap_eq_self {f : R ->+* S} {t : Subsemiring S} (h : t <= f.rangeS) :
 (t.comap f).map f = t
参数：h : t <= f.rangeS。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subsemiring.map_comap_eq`：map_comap_eq (f : R ->+* S) (t : Subsemiring S
) : (t.comap f).map f = t ⊓ f.rangeS
-/
theorem map_comap_eq_self
    {f : R →+* S} {t : Subsemiring S} (h : t ≤ f.rangeS) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using map_comap_eq f t
/-
**Subsemiring.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemi
ring`。
形式化陈述：map_comap_eq_self_of_surjective {f : R ->+* S} (hf : Function.Surjective f
) (t : Subsemiring S) : (t.comap f).map f = t
参数：hf : Function.Surjective f；t : Subsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.map_comap_eq_self`：map_comap_eq_self {f : R ->+* S} {t : Sub
semiring S} (h : t <= f.rangeS) : (t.comap f).map f = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.rangeS_top_of_surjective`：rangeS_top_of_surjective (f : R ->+* S
) (hf : Function.Surjective f) : f.rangeS = (⊤ : Subsemiring S)
-/
theorem map_comap_eq_self_of_surjective
    {f : R →+* S} (hf : Function.Surjective f) (t : Subsemiring S) : (t.comap f).map f = t :=
  map_comap_eq_self <| by simp [hf]
/-
**Subsemiring.comap_map_eq_self_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subsemir
ing`。
形式化陈述：comap_map_eq_self_of_injective {f : R ->+* S} (hf : Function.Injective f) 
(s : Subsemiring R) : (s.map f).comap f = s
参数：hf : Function.Injective f；s : Subsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem comap_map_eq_self_of_injective
    {f : R →+* S} (hf : Function.Injective f) (s : Subsemiring R) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subsemiring

