/-
Copyright (c) 2020 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Subrings

We prove that subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `Subring R`, sending a subset of `R`
to the subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [Ring R] (S : Type u) [Ring S] (f g : R →+* S)`
`(A : Subring R) (B : Subring S) (s : Set R)`

* `instance : CompleteLattice (Subring R)` : the complete lattice structure on the subrings.

* `Subring.center` : the center of a ring `R`.

* `Subring.closure` : subring closure of a set, i.e., the smallest subring that includes the set.

* `Subring.gi` : `closure : Set M → Subring M` and coercion `(↑) : Subring M → et M`
  form a `GaloisInsertion`.

* `comap f B : Subring A` : the preimage of a subring `B` along the ring homomorphism `f`

* `map f A : Subring B` : the image of a subring `A` along the ring homomorphism `f`.

* `prod A B : Subring (R × S)` : the product of subrings

* `f.range : Subring B` : the range of the ring homomorphism `f`.

* `eqLocus f g : Subring R` : given ring homomorphisms `f g : R →+* S`,
     the subring of `R` where `f x = g x`

## Implementation notes

A subring is implemented as a subsemiring which is also an additive subgroup.
The initial PR was as a submonoid which is also an additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subring's underlying set.

## Tags
subring, subrings
-/

@[expose] public section

assert_not_exists IsOrderedRing

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

namespace Subring
variable {s t : Subring R}

@[gcongr, mono]
/-
**Subring.toSubsemiring_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toSubsemiring_strictMono : StrictMono (toSubsemiring : Subring R -> Subsem
iring R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemiring_strictMono : StrictMono (toSubsemiring : Subring R → Subsemiring R) :=
  fun _ _ => id

@[gcongr, mono]
/-
**Subring.toSubsemiring_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toSubsemiring_mono : Monotone (toSubsemiring : Subring R -> Subsemiring R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subring.toSubsemiring_strictMono`：toSubsemiring_strictMono : StrictMono 
(toSubsemiring : Subring R -> Subsemiring R)
-/
theorem toSubsemiring_mono : Monotone (toSubsemiring : Subring R → Subsemiring R) :=
  toSubsemiring_strictMono.monotone

@[gcongr, mono]
/-
**Subring.toAddSubgroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Subring R -> AddSub
group R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Subring R → AddSubgroup R) :=
  fun _ _ => id

@[gcongr, mono]
/-
**Subring.toAddSubgroup_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toAddSubgroup_mono : Monotone (toAddSubgroup : Subring R -> AddSubgroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subring.toAddSubgroup_strictMono`：toAddSubgroup_strictMono : StrictMono 
(toAddSubgroup : Subring R -> AddSubgroup R)
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Subring R → AddSubgroup R) :=
  toAddSubgroup_strictMono.monotone

@[mono]
/-
**Subring.toSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toSubmonoid_strictMono : StrictMono (fun s : Subring R => s.toSubmonoid)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmonoid_strictMono : StrictMono (fun s : Subring R => s.toSubmonoid) := fun _ _ => id

@[mono]
/-
**Subring.toSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：toSubmonoid_mono : Monotone (fun s : Subring R => s.toSubmonoid)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Subring.toSubmonoid_strictMono`：toSubmonoid_strictMono : StrictMono (fun
 s : Subring R => s.toSubmonoid)
-/
theorem toSubmonoid_mono : Monotone (fun s : Subring R => s.toSubmonoid) :=
  toSubmonoid_strictMono.monotone

end Subring

namespace Subring

variable (s : Subring R)

/-- Product of a list of elements in a subring is in the subring. -/
/-
**Subring.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (s : Subring R) {l : List R}, (∀ x ∈ l, x
 ∈ s) → l.prod ∈ s
参数：s : Subring R；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Product of a list of elements in a subring is in the subring.
-/
protected theorem list_prod_mem {R} [Ring R] (s : Subring R) {l : List R} :
    (∀ x ∈ l, x ∈ s) → l.prod ∈ s := list_prod_mem

/-- Sum of a list of elements in a subring is in the subring. -/
/-
**Subring.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) {l : List R}, (∀ x 
∈ l, x ∈ s) → l.sum ∈ s
参数：s : Subring R；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Sum of a list of elements in a subring is in the subring.
-/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Product of a multiset of elements in a subring of a `CommRing` is in the subring. -/
/-
**Subring.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (s : Subring R) (m : Multiset R), (∀ 
a ∈ m, a ∈ s) → m.prod ∈ s
参数：s : Subring R；m : Multiset R；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Product of a multiset of elements in a subring of a `CommRing` is in the subring
.
-/
protected theorem multiset_prod_mem {R} [CommRing R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem _

/-- Sum of a multiset of elements in a `Subring` of a `Ring` is
in the `Subring`. -/
/-
**Subring.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (s : Subring R) (m : Multiset R), (∀ a ∈ 
m, a ∈ s) → m.sum ∈ s
参数：s : Subring R；m : Multiset R；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Sum of a multiset of elements in a `Subring` of a `Ring` is
in the `Subring`.
-/
protected theorem multiset_sum_mem {R} [Ring R] (s : Subring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Product of elements of a subring of a `CommRing` indexed by a `Finset` is in the
subring. -/
/-
**Subring.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (s : Subring R) {ι : Type u_2} {t : F
inset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∏ i ∈ t, f i ∈ s
参数：s : Subring R；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Product of elements of a subring of a `CommRing` indexed by a `Finset` is in the
subring.
-/
protected theorem prod_mem {R : Type*} [CommRing R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∏ i ∈ t, f i) ∈ s :=
  prod_mem h

/-- Sum of elements in a `Subring` of a `Ring` indexed by a `Finset`
is in the `Subring`. -/
/-
**Subring.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (s : Subring R) {ι : Type u_2} {t : Finse
t ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∑ i ∈ t, f i ∈ s
参数：s : Subring R；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Sum of elements in a `Subring` of a `Ring` indexed by a `Finset`
is in the `Subring`.
-/
protected theorem sum_mem {R : Type*} [Ring R] (s : Subring R) {ι : Type*} {t : Finset ι}
    {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-! ## top -/


/-- The subring `R` of the ring `R`. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring `R` of the ring `R`.
-/
instance : Top (Subring R) :=
  ⟨{ (⊤ : Submonoid R), (⊤ : AddSubgroup R) with }⟩

@[simp]
/-
**Subring.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_top (x : R) : x in (⊤ : Subring R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : R) : x ∈ (⊤ : Subring R) :=
  Set.mem_univ x

@[simp, norm_cast]
/-
**Subring.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_top : ((⊤ : Subring R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Subring R) : Set R) = Set.univ :=
  rfl
/-
**Subring.toSubsemiring_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R], ⊤.toSubsemiring = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toSubsemiring_top : (⊤ : Subring R).toSubsemiring = ⊤ := rfl
/-
**Subring.toAddSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R], ⊤.toAddSubgroup = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddSubgroup_top : (⊤ : Subring R).toAddSubgroup = ⊤ := rfl
/-
**Subring.toSubsemiring_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] {S : Subring R}, S.toSubsemiring = 
⊤ ↔ S = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toSubsemiring_eq_top {S : Subring R} : S.toSubsemiring = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]
/-
**Subring.toAddSubgroup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} [inst : NonAssocRing R] {S : Subring R}, S.toAddSubgroup = 
⊤ ↔ S = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toAddSubgroup_eq_top {S : Subring R} : S.toAddSubgroup = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/-- The ring equiv between the top element of `Subring R` and `R`. -/
@[simps!]
/-
**Subring.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：topEquiv : (⊤ : Subring R) ≃+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equiv between the top element of `Subring R` and `R`.
-/
def topEquiv : (⊤ : Subring R) ≃+* R :=
  Subsemiring.topEquiv
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [NonAssocRing R] [Fintype R] : Fintype (⊤ : Subring R) :=
  inferInstanceAs <| Fintype (⊤ : Set R)
/-
**Subring.card_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：card_top (R) [NonAssocRing R] [Fintype R] : Fintype.card (⊤ : Subring R) =
 Fintype.card R
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem card_top (R) [NonAssocRing R] [Fintype R] : Fintype.card (⊤ : Subring R) = Fintype.card R :=
  Fintype.card_congr topEquiv.toEquiv

/-! ## comap -/


/-- The preimage of a subring along a ring homomorphism is a subring. -/
/-
**Subring.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：comap (f : R ->+* S) (s : Subring S) : Subring R
参数：f : R ->+* S；s : Subring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subring along a ring homomorphism is a subring.
-/
def comap (f : R →+* S) (s : Subring S) : Subring R :=
  { s.toSubmonoid.comap (f : R →* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
/-
**Subring.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_comap (s : Subring S) (f : R ->+* S) : (s.comap f : Set R) = f ⁻¹' s
参数：s : Subring S；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (s : Subring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/-
**Subring.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_comap {s : Subring S} {f : R ->+* S} {x : R} : x in s.comap f ↔ f x in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {s : Subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
/-
**Subring.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_comap (s : Subring T) (g : S ->+* T) (f : R ->+* S) : (s.comap g).co
map f = s.comap (g.comp f)
参数：s : Subring T；g : S ->+* T；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (s : Subring T) (g : S →+* T) (f : R →+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/


/-- The image of a subring along a ring homomorphism is a subring. -/
/-
**Subring.map** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：map (f : R ->+* S) (s : Subring R) : Subring S
参数：f : R ->+* S；s : Subring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subring along a ring homomorphism is a subring.
-/
def map (f : R →+* S) (s : Subring R) : Subring S :=
  { s.toSubmonoid.map (f : R →* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

@[simp]
/-
**Subring.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_map (f : R ->+* S) (s : Subring R) : (s.map f : Set S) = f '' s
参数：f : R ->+* S；s : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : R →+* S) (s : Subring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/-
**Subring.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s.map f ↔ exists x i
n s, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : R →+* S} {s : Subring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := Iff.rfl

@[simp]
/-
**Subring.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
**Subring.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
**Subring.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_le_iff_le_comap {f : R ->+* S} {s : Subring R} {t : Subring S} : s.map
 f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : R →+* S} {s : Subring R} {t : Subring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**Subring.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：gc_map_comap (f : R ->+* S) : GaloisConnection (map f) (comap f)
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.map_le_iff_le_comap`：map_le_iff_le_comap {f : R ->+* S} {s : Sub
ring R} {t : Subring S} : s.map f <= t ↔ s <= t.comap f
-/
theorem gc_map_comap (f : R →+* S) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/-- A subring is isomorphic to its image under an injective function -/
/-
**Subring.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：equivMapOfInjective (f : R ->+* S) (hf : Function.Injective f) : s ≃+* s.m
ap f
参数：f : R ->+* S；hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
A subring is isomorphic to its image under an injective function
-/
noncomputable def equivMapOfInjective (f : R →+* S) (hf : Function.Injective f) : s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (f.map_mul _ _)
    map_add' := fun _ _ => Subtype.ext (f.map_add _ _) }

@[simp]
/-
**Subring.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_equivMapOfInjective_apply (f : R ->+* S) (hf : Function.Injective f) (
x : s) : (equivMapOfInjective s f hf x : S) = f x
参数：f : R ->+* S；hf : Function.Injective f；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_equivMapOfInjective_apply (f : R →+* S) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end Subring

namespace RingHom

variable (g : S →+* T) (f : R →+* S)

/-! ## range -/


/-- The range of a ring homomorphism, as a subring of the target. See Note [range copy pattern]. -/
/-
**RingHom.range** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：range (f : R ->+* S) : Subring S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism, as a subring of the target. See Note [range co
py pattern].
-/
def range (f : R →+* S) : Subring S :=
  ((⊤ : Subring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
/-
**RingHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_range : (f.range : Set S) = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
/-
**RingHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl
/-
**RingHom.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：range_eq_map (f : R ->+* S) : f.range = Subring.map f ⊤
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
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
theorem range_eq_map (f : R →+* S) : f.range = Subring.map f ⊤ := by
  ext
  simp
/-
**RingHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_range_self (f : R ->+* S) (x : R) : f x in f.range
参数：f : R ->+* S；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
-/
theorem mem_range_self (f : R →+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩
/-
**RingHom.map_range** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_range : f.range.map g = (g.comp f).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.range_eq_map`：range_eq_map (f : R ->+* S) : f.range = Subring.ma
p f ⊤
· 使用定理 `Subring.map_map`：map_map (g : S ->+* T) (f : R ->+* S) : (s.map f).map g
 = s.map (g.comp f)
-/
theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : Subring R).map_map g f

/-- The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
/-
**RingHom.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：fintypeRange [Fintype R] [DecidableEq S] (f : R ->+* S) : Fintype (range f
)
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism is a fintype, if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`.
-/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →+* S) : Fintype (range f) :=
  Set.fintypeRange f

end RingHom

namespace Subring

/-! ## bot -/


/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## bot
-/
instance : Bot (Subring R) :=
  ⟨(Int.castRingHom R).range⟩
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Subring R) :=
  ⟨⊥⟩

@[norm_cast]
/-
**Subring.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_bot : ((⊥ : Subring R) : Set R) = Set.range ((↑) : Int -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
-/
theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.range ((↑) : ℤ → R) :=
  RingHom.coe_range (Int.castRingHom R)
/-
**Subring.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_bot {x : R} : x in (⊥ : Subring R) ↔ exists n : Int, ↑n = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
-/
theorem mem_bot {x : R} : x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, ↑n = x :=
  RingHom.mem_range

/-! ## inf -/


/-- The inf of two subrings is their intersection. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two subrings is their intersection.
-/
instance : Min (Subring R) :=
  ⟨fun s t =>
    { s.toSubmonoid ⊓ t.toSubmonoid, s.toAddSubgroup ⊓ t.toAddSubgroup with carrier := s ∩ t }⟩

@[simp, norm_cast]
/-
**Subring.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = (p : Set R) 
inter p'
参数：p p' : Subring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : Subring R) : ((p ⊓ p' : Subring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
/-
**Subring.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_inf {p p' : Subring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : Subring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Subring R) :=
  ⟨fun s =>
    Subring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, t.toSubmonoid) (⨅ t ∈ s, Subring.toAddSubgroup t)
      (by simp) (by simp)⟩

@[simp, norm_cast]
/-
**Subring.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_sInf (S : Set (Subring R)) : ((sInf S : Subring R) : Set R) = ⋂ s in S
, ↑s
参数：S : Set (Subring R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (Subring R)) : ((sInf S : Subring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
/-
**Subring.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_sInf {S : Set (Subring R)} {x : R} : x in sInf S ↔ forall p in S, x in
 p
参数：Subring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Subring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/-
**Subring.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S
 i
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
theorem coe_iInf {ι : Sort*} {S : ι → Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/-
**Subring.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Subring R} {x : R} : x in ⨅ i, S i ↔ forall
 i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → Subring R} {x : R} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/-
**Subring.sInf_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：sInf_toSubmonoid (s : Set (Subring R)) : (sInf s).toSubmonoid = ⨅ t in s, 
t.toSubmonoid
参数：s : Set (Subring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mk'_toSubmonoid`：∀ {R : Type u} [inst : NonAssocRing R] {s : Set
 R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (Su
bring.mk' s s…
-/
theorem sInf_toSubmonoid (s : Set (Subring R)) :
    (sInf s).toSubmonoid = ⨅ t ∈ s, t.toSubmonoid :=
  mk'_toSubmonoid _ _

@[simp]
/-
**Subring.sInf_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：sInf_toAddSubgroup (s : Set (Subring R)) : (sInf s).toAddSubgroup = ⨅ t in
 s, Subring.toAddSubgroup t
参数：s : Set (Subring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mk'_toAddSubgroup`：∀ {R : Type u} [inst : NonAssocRing R] {s : S
et R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}   (ha : ↑sa = s), (
Subring.mk' s s…
-/
theorem sInf_toAddSubgroup (s : Set (Subring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, Subring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- Subrings of a ring form a complete lattice. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subrings of a ring form a complete lattice.
-/
instance : CompleteLattice (Subring R) :=
  { completeLatticeOfInf (Subring R) fun _ =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx =>
      let ⟨n, hn⟩ := mem_bot.1 hx
      hn ▸ intCast_mem s n
    top := ⊤
    le_top := fun _s _x _hx => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _s _t _x => And.left
    inf_le_right := fun _s _t _x => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }
/-
**Subring.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：eq_top_iff' (A : Subring R) : A = ⊤ ↔ forall x : R, x in A
参数：A : Subring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subring.mem_top`：mem_top (x : R) : x in (⊤ : Subring R)
-/
theorem eq_top_iff' (A : Subring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

/-! ## Center of a ring -/


section

variable (R)

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
/-
**Subring.center** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：center : Subring R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a ring `R` is the set of elements that commute with everything in 
`R`
-/
def center : Subring R :=
  { Subsemiring.center R with
    carrier := Set.center R
    neg_mem' := Set.neg_mem_center }
/-
**Subring.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_center : ↑(center R) = Set.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
/-
**Subring.center_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：center_toSubsemiring : (center R).toSubsemiring = Subsemiring.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toSubsemiring : (center R).toSubsemiring = Subsemiring.center R :=
  rfl

variable {R}
/-
**Subring.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_center_iff {R : Type*} [Ring R] {z : R} : z in center R ↔ forall g, g 
* z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {R : Type*} [Ring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g :=
  Subsemigroup.mem_center_iff
/-
**Subring.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：decidableMemCenter {R} [Ring R] [DecidableEq R] [Fintype R] : DecidablePre
d (· in center R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mem_center_iff`：mem_center_iff {R : Type*} [Ring R] {z : R} : z 
in center R ↔ forall g, g * z = z * g
-/
instance decidableMemCenter {R} [Ring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/-
**Subring.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：center_eq_top (R) [CommRing R] : center R = ⊤
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (R) [CommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

/-- The center is commutative. -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center is commutative.
-/
instance {R} [Ring R] : CommRing (center R) where
  __ := (center R).toRing
  __ : CommSemiring (center R) := inferInstanceAs <| CommSemiring (Subsemiring.center R)

/-- The center of isomorphic (not necessarily associative) rings are isomorphic. -/
/-
**Subring.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : NonAssocRing R] → [inst_1 : No
nAssocRing S] → R ≃+* S → ↥(Subring.center R) ≃+* ↥(Subring.center S)
参数：Subring.center R；Subring.center S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic (not necessarily associative) rings are isomorphic.
-/
@[simps!] def centerCongr (e : R ≃+* S) : center R ≃+* center S :=
  NonUnitalSubsemiring.centerCongr e

/-- The center of a (not necessarily associative) ring
is isomorphic to the center of its opposite. -/
/-
**Subring.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：{R : Type u} → [inst : NonAssocRing R] → ↥(Subring.center R) ≃+* ↥(Subring
.center Rᵐᵒᵖ)
参数：Subring.center R；Subring.center Rᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a (not necessarily associative) ring
is isomorphic to the center of its opposite.
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ :=
  NonUnitalSubsemiring.centerToMulOpposite

end

section DivisionRing

variable {K : Type u} [DivisionRing K]

/-
**Subring.instField** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：instField : Field (center K) where inv a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField : Field (center K) where
  inv a := ⟨a⁻¹, Set.inv_mem_center a.prop⟩
  mul_inv_cancel _ ha := Subtype.ext <| mul_inv_cancel₀ <| Subtype.coe_injective.ne ha
  div a b := ⟨a / b, Set.div_mem_center a.prop b.prop⟩
  div_eq_mul_inv _ _ := Subtype.ext <| div_eq_mul_inv _ _
  inv_zero := Subtype.ext inv_zero
  -- TODO: use a nicer defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp]
/-
**Subring.center.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Subring.center`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (a : ↥(Subring.center K)), ↑a⁻¹ = (
↑a)⁻¹
参数：a : ↥(Subring.center K)；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center.coe_inv (a : center K) : ((a⁻¹ : center K) : K) = (a : K)⁻¹ :=
  rfl

@[simp]
/-
**Subring.center.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Subring.center`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (a b : ↥(Subring.center K)), ↑(a / 
b) = ↑a / ↑b
参数：a b : ↥(Subring.center K)；a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center.coe_div (a b : center K) : ((a / b : center K) : K) = (a : K) / (b : K) :=
  rfl

end DivisionRing

section Centralizer

/-- The centralizer of a set inside a ring as a `Subring`. -/
/-
**Subring.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：centralizer {R} [Ring R] (s : Set R) : Subring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a set inside a ring as a `Subring`.
-/
def centralizer {R} [Ring R] (s : Set R) : Subring R :=
  { Subsemiring.centralizer s with neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
/-
**Subring.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_centralizer {R} [Ring R] (s : Set R) : (centralizer s : Set R) = s.cen
tralizer
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer {R} [Ring R] (s : Set R) : (centralizer s : Set R) = s.centralizer :=
  rfl
/-
**Subring.centralizer_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_toSubmonoid {R} [Ring R] (s : Set R) : (centralizer s).toSubmo
noid = Submonoid.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubmonoid {R} [Ring R] (s : Set R) :
    (centralizer s).toSubmonoid = Submonoid.centralizer s :=
  rfl
/-
**Subring.centralizer_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_toSubsemiring {R} [Ring R] (s : Set R) : (centralizer s).toSub
semiring = Subsemiring.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubsemiring {R} [Ring R] (s : Set R) :
    (centralizer s).toSubsemiring = Subsemiring.centralizer s :=
  rfl
/-
**Subring.centralizer_toNonUnitalSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_toNonUnitalSubring {R} [Ring R] (s : Set R) : (centralizer s).
toNonUnitalSubring = NonUnitalSubring.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toNonUnitalSubring {R} [Ring R] (s : Set R) :
    (centralizer s).toNonUnitalSubring = NonUnitalSubring.centralizer s :=
  rfl
/-
**Subring.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_centralizer_iff {R} [Ring R] {s : Set R} {z : R} : z in centralizer s 
↔ forall g in s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {R} [Ring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g := Iff.rfl
/-
**Subring.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：center_le_centralizer {R} [Ring R] (s) : center R <= centralizer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer {R} [Ring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
/-
**Subring.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_le {R} [Ring R] (s t : Set R) (h : s subseteq t) : centralizer
 t <= centralizer s
参数：s t : Set R；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le {R} [Ring R] (s t : Set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
/-
**Subring.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_eq_top_iff_subset {R} [Ring R] {s : Set R} : centralizer s = ⊤
 ↔ s subseteq center R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {R} [Ring R] {s : Set R} : centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/-
**Subring.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：centralizer_univ {R} [Ring R] : centralizer Set.univ = center R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ {R} [Ring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/-! ## subring closure of a subset -/


/-- The `Subring` generated by a set. -/
/-
**Subring.closure** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：closure (s : Set R) : Subring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Subring` generated by a set.
-/
def closure (s : Set R) : Subring R :=
  sInf { S | s ⊆ S }
/-
**Subring.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : Subring R, s
 subseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mem_sInf`：mem_sInf {S : Set (Subring R)} {x : R} : x in sInf S ↔
 forall p in S, x in p
-/
theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : Subring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subring generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**Subring.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：subset_closure {s : Set R} : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.mem_closure`：mem_closure {x : R} {s : Set R} : x in closure s ↔ 
forall S : Subring R, s subseteq S -> x in S

--- 原说明 ---
The subring generated by a set includes the set.
-/
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**Subring.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_closure_of_mem {s : Set R} {x : R} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**Subring.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subring `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/-
**Subring.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_le {s : Set R} {t : Subring R} : closure s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
A subring `t` includes `closure s` if and only if it includes `s`.
-/
theorem closure_le {s : Set R} {t : Subring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/-
**Subring.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s

--- 原说明 ---
Subring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`.
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
/-
**Subring.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s subseteq t) (h₂ : t <
= closure s) : closure s = t
参数：h₁ : s subseteq t；h₂ : t <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
-/
theorem closure_eq_of_le {s : Set R} {t : Subring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
/-
**Subring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(one : p 1 (one_mem _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (
add_mem hx hy)) (neg : forall x hx, p x hx -> p (-x) (neg_mem hx)) (mul : forall
 x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closur
e s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；one : p 1 (one_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x 
+ y) (add_mem hx hy)；neg : forall x hx, p x hx -> p (-x) (neg_mem hx)；mul : fora
ll x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
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
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
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
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `0`, `1`, and al
l elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` 
holds for all
elements of the closure of `s`.
-/
theorem closure_induction {s : Set R} {p : (x : R) → x ∈ closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_closure hx))
    (zero : p 0 (zero_mem _)) (one : p 1 (one_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let K : Subring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ ↦ ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩
      one_mem' := ⟨_, one⟩ }
  closure_le (t := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
/-
**Subring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(one : p 1 (one_mem _)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (
add_mem hx hy)) (neg : forall x hx, p x hx -> p (-x) (neg_mem hx)) (mul : forall
 x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closur
e s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；one : p 1 (one_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x 
+ y) (add_mem hx hy)；neg : forall x hx, p x hx -> p (-x) (neg_mem hx)；mul : fora
ll x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
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
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
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
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership, for predicates with two arguments
.
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ closure s → y ∈ closure s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (neg_left : ∀ x y hx hy, p x y hx hy → p (-x) y (neg_mem hx) hy)
    (neg_right : ∀ x y hx hy, p x y hx hy → p x (-y) hx (neg_mem hy))
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
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h
/-
**Subring.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_closure_iff {s : Set R} {x} : x in closure s ↔ x in AddSubgroup.closur
e (Submonoid.closure s : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.closure_induction`：closure_induction {s : Set R} {p : (x : R) ->
 x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_closure hx
)) (zero : p 0 …
· 使用定理 `AddSubgroup.subset_closure`：∀ {G : Type u_1} [inst : AddGroup G] {k : Se
t G}, k ⊆ ↑(AddSubgroup.closure k)
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `AddSubgroup.closure_induction₂`：∀ {G : Type u_1} [inst : AddGroup G] {k 
: Set G}   {p : (x y : G) → x ∈ AddSubgroup.closure k → y ∈ AddSubgroup.closure 
k → Prop},   (∀ (x y…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `AddSubgroup.closure_induction`：∀ {G : Type u_1} [inst : AddGroup G] {k :
 Set G} {p : (g : G) → g ∈ AddSubgroup.closure k → Prop},   (∀ (x : G) (hx : x ∈
 k), p x ⋯) →     p…
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
（共 38 条，此处仅展示前 30 条）
-/
theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Submonoid.closure s : Set R) :=
  ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Submonoid.subset_closure hx)
    | zero => exact zero_mem _
    | one => exact AddSubgroup.subset_closure (one_mem _)
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg _ _ hx => exact neg_mem hx
    | mul _ _ _hx _hy hx hy =>
      clear _hx _hy
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem _ _ hx hy => exact AddSubgroup.subset_closure (mul_mem hx hy)
      | zero_left => simp
      | zero_right => simp
      | add_left _ _ _ _ _ _ h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂
      | add_right _ _ _ _ _ _ h₁ h₂ => simpa [mul_add] using add_mem h₁ h₂
      | neg_left _ _ _ _ h => simpa [neg_mul] using neg_mem h
      | neg_right _ _ _ _ h => simpa [mul_neg] using neg_mem h,
    fun h => by
      induction h using AddSubgroup.closure_induction with
      | mem x hx =>
        induction hx using Submonoid.closure_induction with
        | mem _ h => exact subset_closure h
        | one => exact one_mem _
        | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | zero => exact zero_mem _
      | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | neg _ _ h => exact neg_mem h⟩
/-
**Subring.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Subring`
。
形式化陈述：closure_le_centralizer_centralizer {R} [Ring R] (s : Set R) : closure s <=
 centralizer (centralizer s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer {R} [Ring R] (s : Set R) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all elements of `s : Set R` commute pairwise, then `closure s` is a commutative ring. -/
/-
**Subring.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：isMulCommutative_closure {R} [Ring R] {s : Set R} (hcomm : forall x in s, 
forall y in s, x * y = y * x) : IsMulCommutative (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subring.closure_le_centralizer_centralizer`：closure_le_centralizer_centr
alizer {R} [Ring R] (s : Set R) : closure s <= centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all elements of `s : Set R` commute pairwise, then `closure s` is a commutati
ve ring.
-/
theorem isMulCommutative_closure {R} [Ring R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all elements of `s : Set R` commute pairwise, then `closure s` is a commutative ring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/-
**Subring.closureCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subring`。
形式化陈述：closureCommRingOfComm {R} [Ring R] {s : Set R} (hcomm : forall x in s, for
all y in s, x * y = y * x) : CommRing (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.isMulCommutative_closure`：isMulCommutative_closure {R} [Ring R] 
{s : Set R} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommuta
tive (closure s)

--- 原说明 ---
If all elements of `s : Set R` commute pairwise, then `closure s` is a commutati
ve ring.
-/
abbrev closureCommRingOfComm {R} [Ring R] {s : Set R} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    CommRing (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance
/-
**Subring.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：instIsMulCommutative_closure {S R : Type*} [Ring R] [SetLike S R] [MulMemC
lass S R] (s : S) [IsMulCommutative s] : IsMulCommutative (closure (s : Set R))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.isMulCommutative_closure`：isMulCommutative_closure {R} [Ring R] 
{s : Set R} (hcomm : forall x in s, forall y in s, x * y = y * x) : IsMulCommuta
tive (closure s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S R : Type*} [Ring R] [SetLike S R] [MulMemClass S R] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂
/-
**Subring.exists_list_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：exists_list_of_mem_closure {R} [Ring R] {s : Set R} {x : R} (hx : x in clo
sure s) : exists L : List (List R), (forall t in L, forall y in t, y in s ∨ y = 
(-1 : R)) ∧ (L.map List.prod).sum = x
参数：hx : x in closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.closure_induction`：∀ {G : Type u_1} [inst : AddGroup G] {k :
 Set G} {p : (g : G) → g ∈ AddSubgroup.closure k → Prop},   (∀ (x : G) (hx : x ∈
 k), p x ⋯) →     p…
· 使用定理 `Submonoid.exists_list_of_mem_closure`：exists_list_of_mem_closure {s : Se
t M} {x : M} (hx : x in closure s) : exists l : List M, (forall y in l, y in s) 
∧ l.prod = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `List.forall_mem_nil`：∀ {α : Type u_1} (p : α → Prop), ∀ x ∈ [], p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.forall_mem_append`：∀ {α : Type u_1} {p : α → Prop} {l₁ l₂ : List α}
, (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.sum_append`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Zero α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 + x2) 0]   [Std.Associative fun x1 x2 => x1 
+ x2]…
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `AddSemigroup.to_isLawfulIdentity`：∀ {M : Type u_4} [inst : AddZeroClass 
M], Std.LawfulIdentity (fun x1 x2 => x1 + x2) 0
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `List.forall_mem_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α} {P : β → Prop}, (∀ i ∈ List.map f l, P i) ↔ ∀ j ∈ l, P (f j)
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
（共 37 条，此处仅展示前 30 条）
-/
theorem exists_list_of_mem_closure {R} [Ring R] {s : Set R} {x : R} (hx : x ∈ closure s) :
    ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1 : R)) ∧ (L.map List.prod).sum = x := by
  rw [mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨[l], by simp_all⟩
  | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
  | add _ _ _ _ hL hM =>
    obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
    exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
      rw [List.map_append, List.sum_append, HL2, HM2]⟩
  | neg _ _ hL =>
    obtain ⟨L, hL⟩ := hL
    exact ⟨L.map (List.cons (-1)),
      List.forall_mem_map.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp +contextual [List.map_cons, add_comm])⟩

variable (R) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**Subring.gi** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：(R : Type u) → [inst : NonAssocRing R] → GaloisInsertion Subring.closure S
etLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

/-- Closure of a subring `S` equals `S`. -/
@[simp]
/-
**Subring.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_eq (s : Subring R) : closure (s : Set R) = s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a subring `S` equals `S`.
-/
theorem closure_eq (s : Subring R) : closure (s : Set R) = s :=
  (Subring.gi R).l_u_eq s

@[simp]
/-
**Subring.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
  (Subring.gi R).gc.l_bot

@[simp]
/-
**Subring.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_univ : closure (Set.univ : Set R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.closure_eq`：closure_eq (s : Subring R) : closure (s : Set R) = s
· 使用定理 `Subring.coe_top`：coe_top : ((⊤ : Subring R) : Set R) = Set.univ
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
/-
**Subring.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
  (Subring.gi R).gc.l_sup
/-
**Subring.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
  (Subring.gi R).gc.l_iSup
/-
**Subring.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
  (Subring.gi R).gc.l_sSup

@[simp]
/-
**Subring.closure_singleton_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_singleton_intCast (n : Int) : closure {(n : R)} = ⊥
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `intCast_mem`：intCast_mem (n : Int) : (n : R) in s
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem closure_singleton_intCast (n : ℤ) : closure {(n : R)} = ⊥ :=
  bot_unique <| closure_le.2 <| Set.singleton_subset_iff.mpr <| intCast_mem _ _

@[simp]
/-
**Subring.closure_singleton_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_singleton_natCast (n : Nat) : closure {(n : R)} = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Subring.closure_singleton_intCast`：closure_singleton_intCast (n : Int) :
 closure {(n : R)} = ⊥
-/
theorem closure_singleton_natCast (n : ℕ) : closure {(n : R)} = ⊥ :=
  mod_cast closure_singleton_intCast n

@[simp]
/-
**Subring.closure_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
· 使用定理 `Subring.closure_singleton_natCast`：closure_singleton_natCast (n : Nat) :
 closure {(n : R)} = ⊥
-/
theorem closure_singleton_zero : closure {(0 : R)} = ⊥ := mod_cast closure_singleton_natCast 0

@[simp]
/-
**Subring.closure_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
· 使用定理 `Subring.closure_singleton_natCast`：closure_singleton_natCast (n : Nat) :
 closure {(n : R)} = ⊥
-/
theorem closure_singleton_one : closure {(1 : R)} = ⊥ := mod_cast closure_singleton_natCast 1

@[simp]
/-
**Subring.closure_insert_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_insert_intCast (n : Int) (s : Set R) : closure (insert (n : R) s) 
= closure s
参数：n : Int；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Subring.closure_union`：closure_union (s t : Set R) : closure (s union t)
 = closure s ⊔ closure t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subring.closure_singleton_intCast`：closure_singleton_intCast (n : Int) :
 closure {(n : R)} = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_insert_intCast (n : ℤ) (s : Set R) : closure (insert (n : R) s) = closure s := by
  rw [Set.insert_eq, closure_union]
  simp

@[simp]
/-
**Subring.closure_insert_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_insert_natCast (n : Nat) (s : Set R) : closure (insert (n : R) s) 
= closure s
参数：n : Nat；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Subring.closure_insert_intCast`：closure_insert_intCast (n : Int) (s : Se
t R) : closure (insert (n : R) s) = closure s
-/
theorem closure_insert_natCast (n : ℕ) (s : Set R) : closure (insert (n : R) s) = closure s :=
  mod_cast closure_insert_intCast n s

@[simp]
/-
**Subring.closure_insert_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
· 使用定理 `Subring.closure_insert_natCast`：closure_insert_natCast (n : Nat) (s : Se
t R) : closure (insert (n : R) s) = closure s
-/
theorem closure_insert_zero (s : Set R) : closure (insert 0 s) = closure s :=
  mod_cast closure_insert_natCast 0 s

@[simp]
/-
**Subring.closure_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
· 使用定理 `Subring.closure_insert_natCast`：closure_insert_natCast (n : Nat) (s : Se
t R) : closure (insert (n : R) s) = closure s
-/
theorem closure_insert_one (s : Set R) : closure (insert 1 s) = closure s :=
  mod_cast closure_insert_natCast 1 s
/-
**Subring.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_sup (s t : Subring R) (f : R ->+* S) : (s ⊔ t).map f = s.map f ⊔ t.map
 f
参数：s t : Subring R；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_sup (s t : Subring R) (f : R →+* S) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**Subring.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_iSup {ι : Sort*} (f : R ->+* S) (s : ι -> Subring R) : (iSup s).map f 
= ⨆ i, (s i).map f
参数：f : R ->+* S；s : ι -> Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : R →+* S) (s : ι → Subring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**Subring.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_inf (s t : Subring R) (f : R ->+* S) (hf : Function.Injective f) : (s 
⊓ t).map f = s.map f ⊓ t.map f
参数：s t : Subring R；f : R ->+* S；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (s t : Subring R) (f : R →+* S) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)
/-
**Subring.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : R ->+* S) (hf : Function.Injective 
f) (s : ι -> Subring R) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : R ->+* S；hf : Function.Injective f；s : ι -> Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subring R} : (↑(⨅ i, S 
i) : Set R) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : R →+* S) (hf : Function.Injective f)
    (s : ι → Subring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**Subring.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_inf (s t : Subring S) (f : R ->+* S) : (s ⊓ t).comap f = s.comap f ⊓
 t.comap f
参数：s t : Subring S；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_inf (s t : Subring S) (f : R →+* S) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
/-
**Subring.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_iInf {ι : Sort*} (f : R ->+* S) (s : ι -> Subring S) : (iInf s).coma
p f = ⨅ i, (s i).comap f
参数：f : R ->+* S；s : ι -> Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : R →+* S) (s : ι → Subring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**Subring.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_bot (f : R ->+* S) : (⊥ : Subring R).map f = ⊥
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_bot (f : R →+* S) : (⊥ : Subring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**Subring.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_top (f : R ->+* S) : (⊤ : Subring S).comap f = ⊤
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
-/
theorem comap_top (f : R →+* S) : (⊤ : Subring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `Subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a subring of `R × S`. -/
/-
**Subring.prod** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：prod (s : Subring R) (t : Subring S) : Subring (R × S)
参数：s : Subring R；t : Subring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Subring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×̂ t`
as a subring of `R × S`.
-/
def prod (s : Subring R) (t : Subring S) : Subring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubgroup.prod t.toAddSubgroup with carrier := s ×ˢ t }

@[norm_cast]
/-
**Subring.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_prod (s : Subring R) (t : Subring S) : (s.prod t : Set (R × S)) = (s :
 Set R) ×ˢ (t : Set S)
参数：s : Subring R；t : Subring S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : Subring R) (t : Subring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl
/-
**Subring.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p in s.prod t ↔ p.1
 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[gcongr, mono]
/-
**Subring.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁
 <= t₂) : s₁.prod t₁ <= s₂.prod t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : Subring S⦄ (ht : t₁ ≤ t₂) :
    s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
/-
**Subring.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.prod t
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.prod_mono`：prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ 
: Subring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.prod t :=
  prod_mono (le_refl s)
/-
**Subring.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.prod t
参数：t : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.prod_mono`：prod_mono ⦃s₁ s₂ : Subring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ 
: Subring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.prod t := fun _ _ hs =>
  prod_mono hs (le_refl t)
/-
**Subring.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：prod_top (s : Subring R) : s.prod (⊤ : Subring S) = s.comap (RingHom.fst R
 S)
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (s : Subring R) : s.prod (⊤ : Subring S) = s.comap (RingHom.fst R S) :=
  ext fun x => by simp [mem_prod]
/-
**Subring.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.comap (RingHom.snd R
 S)
参数：s : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
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
theorem top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.comap (RingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/-
**Subring.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：top_prod_top : (⊤ : Subring R).prod (⊤ : Subring S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subring.top_prod`：top_prod (s : Subring S) : (⊤ : Subring R).prod s = s.
comap (RingHom.snd R S)
· 使用定理 `Subring.comap_top`：comap_top (f : R ->+* S) : (⊤ : Subring S).comap f = 
⊤
-/
theorem top_prod_top : (⊤ : Subring R).prod (⊤ : Subring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
/-
**Subring.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonAssocRing R] [inst_1 : NonAssocRing
 S],   Subring.center (R × S) = (Subring.center R).prod (Subring.center S)
参数：R × S；Subring.center R；Subring.center S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/-- Product of subrings is isomorphic to their product as rings. -/
/-
**Subring.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：prodEquiv (s : Subring R) (t : Subring S) : s.prod t ≃+* s × t
参数：s : Subring R；t : Subring S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Product of subrings is isomorphic to their product as rings.
-/
def prodEquiv (s : Subring R) (t : Subring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _x _y => rfl
    map_add' := fun _x _y => rfl }

/-- The underlying set of a non-empty directed sSup of subrings is just a union of the subrings.
  Note that this fails without the directedness assumption (the union of two subrings is
  typically not a subring) -/
/-
**Subring.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Dire
cted (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.mk'`：mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = 
s) {sa : AddSubgroup R} (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid
 …
· 使用定理 `Submonoid.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [Nonempty ι] {S
 : ι -> Submonoid M} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Submonoid M) : Se
t M) = ⋃ i, S i
· 使用定理 `AddSubgroup.coe_iSup_of_directed`：∀ {G : Type u_1} [inst : AddGroup G] {
ι : Sort u_2} [Nonempty ι] {S : ι → AddSubgroup G},   Directed (fun x1 x2 => x1 
≤ x2) S → ↑(⨆ i, S i) …
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

--- 原说明 ---
The underlying set of a non-empty directed sSup of subrings is just a union of t
he subrings.
  Note that this fails without the directedness assumption (the union of two sub
rings is
  typically not a subring)
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S)
    {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : Subring R :=
    Subring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubmonoid) (⨆ i, (S i).toAddSubgroup)
      (Submonoid.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩
/-
**Subring.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subring R} (hS : Dire
cted (· <= ·) S) : ((⨆ i, S i : Subring R) : Set R) = ⋃ i, S i
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
· 使用定理 `Subring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempty ι]
 {S : ι -> Subring R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exi
sts i, x in S i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subring R} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]
/-
**Subring.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : Dire
ctedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s
参数：Subring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
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
· 使用定理 `Subring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempty ι]
 {S : ι -> Subring R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exi
sts i, x in S i
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]
/-
**Subring.coe_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty) (hS : Dire
ctedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s
参数：Subring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.mem_sSup_of_directedOn`：mem_sSup_of_directedOn {S : Set (Subring
 R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exi
sts s in S, x in s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sSup_of_directedOn {S : Set (Subring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
/-
**Subring.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> Subring R} [hS : 
forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsMulCommutative
 (⨆ i, S i : Subring R)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι : Nonempty ι]
 {S : ι -> Subring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subring R) : Set
 R) = ⋃ i, S i
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
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `SubringClass.nonUnitalSubringClass`：∀ (S : Type u_1) (R : Type u) [inst 
: SetLike S R] [inst_1 : NonAssocRing R] [SubringClass S R],   NonUnitalSubringC
lass S R
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
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι → Subring R}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : Subring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, coe_iSup_of_directed dir,
    Subsemigroup.coe_iSup_of_directed dir] using! Subsemigroup.isMulCommutative_iSup dir
/-
**Subring.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o Subring R} [hS : forall i, IsMulCommutative (S i)] : IsMulC
ommutative (⨆ i, S i : Subring R)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : Sort*} [Nonemp
ty ι] {S : ι -> Subring R} [hS : forall i, IsMulCommutative (S i)] (dir : Direct
ed (· <= ·) S) : Is…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o Subring R} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : Subring R) :=
  Subring.isMulCommutative_iSup S.monotone.directed_le
/-
**Subring.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} : x in K.map (f : R ->
+* S) ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : R ≃+* S} {K : Subring R} {x : S} :
    x ∈ K.map (f : R →+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x
/-
**Subring.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) : K.map (f : R ->+* 
S) = K.comap f.symm
参数：f : R ≃+* S；K : Subring R。
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
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : Subring R) :
    K.map (f : R →+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)
/-
**Subring.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) : K.comap (f : R ->+
* S) = K.map f.symm
参数：f : R ≃+* S；K : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Subring.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : R ≃+* S) (
K : Subring R) : K.map (f : R ->+* S) = K.comap f.symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : Subring S) :
    K.comap (f : R →+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end Subring

namespace RingHom

variable {s : Subring R}

open Subring

/-- Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**RingHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：rangeRestrict (f : R ->+* S) : R ->+* f.range
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a ring homomorphism to its range interpreted as a subsemiring.

This is the bundled version of `Set.rangeFactorization`.
-/
def rangeRestrict (f : R →+* S) : R →+* f.range :=
  f.codRestrict f.range fun x => ⟨x, rfl⟩

@[simp]
/-
**RingHom.coe_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_rangeRestrict (f : R ->+* S) (x : R) : (f.rangeRestrict x : S) = f x
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_rangeRestrict (f : R →+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl
/-
**RingHom.rangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeRestrict_surjective (f : R ->+* S) : Function.Surjective f.rangeRestr
ict
参数：f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem rangeRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩
/-
**RingHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：range_eq_top {f : R ->+* S} : f.range = (⊤ : Subring S) ↔ Function.Surject
ive f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
· 使用定理 `Subring.coe_top`：coe_top : ((⊤ : Subring R) : Set R) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem range_eq_top {f : R →+* S} :
    f.range = (⊤ : Subring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/-
**RingHom.range_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：range_eq_top_of_surjective (f : R ->+* S) (hf : Function.Surjective f) : f
.range = (⊤ : Subring S)
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.range_eq_top`：range_eq_top {f : R ->+* S} : f.range = (⊤ : Subri
ng S) ↔ Function.Surjective f

--- 原说明 ---
The range of a surjective ring homomorphism is the whole of the codomain.
-/
theorem range_eq_top_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : Subring S) :=
  range_eq_top.2 hf

@[simp]
/-
**RingHom.domRestrict_comp_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：domRestrict_comp_rangeRestrict (g : S ->+* T) (f : R ->+* S) : (g.domRestr
ict f.range).comp (f.rangeRestrict) = g.comp f
参数：g : S ->+* T；f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem domRestrict_comp_rangeRestrict (g : S →+* T) (f : R →+* S) :
    (g.domRestrict f.range).comp (f.rangeRestrict) = g.comp f :=
  rfl

@[simp]
/-
**RingHom.range_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：range_prodMap {R' S' : Type*} [Ring R'] [Ring S'] (f : R ->+* S) (g : R' -
>+* S') : (f.prodMap g).range = f.range.prod g.range
参数：f : R ->+* S；g : R' ->+* S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
-/
theorem range_prodMap {R' S' : Type*} [Ring R'] [Ring S'] (f : R →+* S) (g : R' →+* S') :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

section eqLocus

variable {S : Type v} [Semiring S]

/-- The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R -/
/-
**RingHom.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：eqLocus (f g : R ->+* S) : Subring R
参数：f g : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a subring of R
-/
def eqLocus (f g : R →+* S) : Subring R :=
  { (f : R →* S).eqLocusM g, (f : R →+ S).eqLocus g with carrier := { x | f x = g x } }

@[simp]
/-
**RingHom.mem_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_eqLocus {f g : R ->+* S} {x : R} : x in f.eqLocus g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocus {f g : R →+* S} {x : R} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

@[simp]
/-
**RingHom.eqLocus_same** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eqLocus_same (f : R ->+* S) : f.eqLocus f = ⊤
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem eqLocus_same (f : R →+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its subring closure. -/
/-
**RingHom.eqOn_set_closure** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eqOn_set_closure {f g : R ->+* S} {s : Set R} (h : Set.EqOn f g s) : Set.E
qOn f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t

--- 原说明 ---
If two ring homomorphisms are equal on a set, then they are equal on its subring
 closure.
-/
theorem eqOn_set_closure {f g : R →+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
/-
**RingHom.eq_of_eqOn_set_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_of_eqOn_set_top {f g : R ->+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f
 = g
参数：h : Set.EqOn f g (⊤ : Subring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_set_top {f g : R →+* S} (h : Set.EqOn f g (⊤ : Subring R)) : f = g :=
  ext fun _x => h trivial
/-
**RingHom.eq_of_eqOn_set_dense** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R ->+* S} (h 
: s.EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.eq_of_eqOn_set_top`：eq_of_eqOn_set_top {f g : R ->+* S} (h : Set
.EqOn f g (⊤ : Subring R)) : f = g
· 使用定理 `RingHom.eqOn_set_closure`：eqOn_set_closure {f g : R ->+* S} {s : Set R} 
(h : Set.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h

end eqLocus

/-
**RingHom.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：closure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (clo
sure s).comap f
参数：f : R ->+* S；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subring.mem_comap`：mem_comap {s : Subring S} {f : R ->+* S} {x : R} : x 
in s.comap f ↔ f x in s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set. -/
/-
**RingHom.map_closure** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_closure (f : R ->+* S) (s : Set R) : (closure s).map f = closure (f ''
 s)
参数：f : R ->+* S；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Subring.gc_map_comap`：gc_map_comap (f : R ->+* S) : GaloisConnection (ma
p f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The image under a ring homomorphism of the subring generated by a set equals
the subring generated by the image of the set.
-/
theorem map_closure (f : R →+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subring.gi S).gc (Subring.gi R).gc
    fun _ ↦ rfl

end RingHom

namespace Subring

open RingHom

/-
**Subring.mem_closure_image_of** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：mem_closure_image_of (f : R ->+* S) {s : Set R} {x : R} (hx : x in Subring
.closure s) : f x in Subring.closure (f '' s)
参数：f : R ->+* S；hx : x in Subring.closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_closure`：map_closure (f : R ->+* S) (s : Set R) : (closure s
).map f = closure (f '' s)
· 使用定理 `Subring.mem_map`：mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s
.map f ↔ exists x in s, f x = y
-/
theorem mem_closure_image_of (f : R →+* S) {s : Set R} {x : R} (hx : x ∈ Subring.closure s) :
    f x ∈ Subring.closure (f '' s) := by
  rw [← f.map_closure, Subring.mem_map]
  exact ⟨x, hx, rfl⟩

/-- The ring homomorphism associated to an inclusion of subrings. -/
/-
**Subring.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subring`。
形式化陈述：inclusion {S T : Subring R} (h : S <= T) : S ->+* T
参数：h : S <= T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
The ring homomorphism associated to an inclusion of subrings.
-/
def inclusion {S T : Subring R} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/-
**Subring.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：coe_inclusion {S T : Subring R} (h : S <= T) (x : S) : (Subring.inclusion 
h x : R) = x
参数：h : S <= T；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_inclusion {S T : Subring R} (h : S ≤ T) (x : S) :
    (Subring.inclusion h x : R) = x := by simp [Subring.inclusion]
/-
**Subring.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：inclusion_injective {S T : Subring R} (h : S <= T) : Function.Injective (S
ubring.inclusion h)
参数：h : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `RingHom.injective_codRestrict`：injective_codRestrict {f : R ->+* S} {s :
 σS} {h : forall x, f x in s} : Function.Injective (f.codRestrict s h) ↔ Functio
n.Injective f
· 使用引理 `Subring.subtype_injective`：subtype_injective (s : Subring R) : Function.
Injective s.subtype
-/
theorem inclusion_injective {S T : Subring R} (h : S ≤ T) :
    Function.Injective (Subring.inclusion h) :=
  RingHom.injective_codRestrict.mpr S.subtype_injective

@[simp]
/-
**Subring.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：range_subtype (s : Subring R) : s.subtype.range = s
参数：s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_subtype (s : Subring R) : s.subtype.range = s :=
  SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe
/-
**Subring.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
/-
**Subring.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
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
**Subring.prod_bot_sup_bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.prod ⊥ ⊔ prod ⊥ 
t = s.prod t
参数：s : Subring R；t : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Subring.prod_mono_right`：prod_mono_right (s : Subring R) : Monotone fun 
t : Subring S => s.prod t
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Subring.prod_mono_left`：prod_mono_left (t : Subring S) : Monotone fun s 
: Subring R => s.prod t
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
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
theorem prod_bot_sup_bot_prod (s : Subring R) (t : Subring S) : s.prod ⊥ ⊔ prod ⊥ t = s.prod t :=
  le_antisymm (sup_le (prod_mono_right s bot_le) (prod_mono_left t bot_le)) fun p hp =>
    Prod.fst_mul_snd p ▸
      mul_mem
        ((le_sup_left : s.prod ⊥ ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨hp.1, SetLike.mem_coe.2 <| one_mem ⊥⟩)
        ((le_sup_right : prod ⊥ t ≤ s.prod ⊥ ⊔ prod ⊥ t) ⟨SetLike.mem_coe.2 <| one_mem ⊥, hp.2⟩)

end Subring

namespace RingEquiv

variable {s t : Subring R}

/-- Makes the identity isomorphism from a proof two subrings of a multiplicative
monoid are equal. -/
/-
**RingEquiv.subringCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：subringCongr (h : s = t) : s ≃+* t
参数：h : s = t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Makes the identity isomorphism from a proof two subrings of a multiplicative
monoid are equal.
-/
def subringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

@[simp]
/-
**RingEquiv.subringCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：subringCongr_symm (h : s = t) : (subringCongr h).symm = subringCongr h.sym
m
参数：h : s = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem subringCongr_symm (h : s = t) :
    (subringCongr h).symm = subringCongr h.symm := rfl

@[simp]
/-
**RingEquiv.coe_subringCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_subringCongr_apply (h : s = t) (x : s) : (subringCongr h x).val = x.va
l
参数：h : s = t；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem coe_subringCongr_apply (h : s = t) (x : s) :
    (subringCongr h x).val = x.val := rfl

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`. -/
/-
**RingEquiv.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverse {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse g f) :
 R ≃+* f.range
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R

--- 原说明 ---
Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`.
-/
def ofLeftInverse {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ f.range.subtype) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := RingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**RingEquiv.ofLeftInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverse_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInverse 
g f) (x : R) : ↑(ofLeftInverse h x) = f x
参数：h : Function.LeftInverse g f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem ofLeftInverse_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/-
**RingEquiv.ofLeftInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverse_symm_apply {g : S -> R} {f : R ->+* S} (h : Function.LeftInv
erse g f) (x : f.range) : (ofLeftInverse h).symm x = g x
参数：h : Function.LeftInverse g f；x : f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem ofLeftInverse_symm_apply {g : S → R} {f : R →+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of rings and a subring `s` of `R`,
`subringMap e s` is the induced equivalence between `s` and `s.map e` -/
/-
**RingEquiv.subringMap** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence `e : R ≃+* S` of rings and a subring `s` of `R`,
`subringMap e s` is the induced equivalence between `s` and `s.map e`
-/
def subringMap (e : R ≃+* S) : s ≃+* s.map e.toRingHom :=
  e.subsemiringMap s.toSubsemiring

set_option backward.isDefEq.respectTransparency false in
/-- A ring isomorphism `e : R ≃+* S` descends to subrings `s' ≃+* s` provided
`x ∈ s' ↔ e x ∈ s`. -/
@[simps!]
/-
**RingEquiv.restrict** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：restrict {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring 
S] {σR : Type*} {σS : Type*} [SetLike σR R] [SetLike σS S] [SubsemiringClass σR 
R] [SubsemiringClass σS S] (e : R ≃+* S) (s' : σR) (s : σS) (h : forall x, x in 
s' ↔ e x in s) : s' ≃+* s where __
参数：e : R ≃+* S；s' : σR；s : σS；h : forall x, x in s' ↔ e x in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring isomorphism `e : R ≃+* S` descends to subrings `s' ≃+* s` provided
`x ∈ s' ↔ e x ∈ s`.
-/
def restrict {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]
    {σR : Type*} {σS : Type*} [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R]
    [SubsemiringClass σS S] (e : R ≃+* S) (s' : σR) (s : σS) (h : ∀ x, x ∈ s' ↔ e x ∈ s) :
    s' ≃+* s where
  __ := RingHom.restrict e _ _ fun _ ↦ (h _).1
  invFun := RingHom.restrict e.symm _ _ fun y hy ↦ by
    obtain ⟨x, rfl⟩ := e.surjective y; simp [(h _).2 hy]
  left_inv y := by simp [← Subtype.val_inj]
  right_inv x := by simp [← Subtype.val_inj]

end RingEquiv

namespace Subring

variable {s : Set R}

@[elab_as_elim]
/-
**Subring.InClosure.recOn** 是 Mathlib 中的一个定理，位于命名空间 `Subring.InClosure`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {s : Set R} {C : R → Prop} {x : R},   x ∈
 Subring.closure s →     C 1 → C (-1) → (∀ z ∈ s, ∀ (n : R), C n → C (z * n)) → 
(∀ {x y : R}, C x → C y → C (x + y)) → C x
参数：-1；∀ z ∈ s, ∀ (n : R), C n → C (z * n)；∀ {x y : R}, C x → C y → C (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Subring.exists_list_of_mem_closure`：exists_list_of_mem_closure {R} [Ring
 R] {s : Set R} {x : R} (hx : x in closure s) : exists L : List (List R), (foral
l t in L, forall y in t,…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `List.forall_mem_nil`：∀ {α : Type u_1} (p : α → Prop), ∀ x ∈ [], p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
-/
protected theorem InClosure.recOn {R} [Ring R] {s : Set R}
    {C : R → Prop} {x : R} (hx : x ∈ closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction L with
  | nil => exact h0
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact h1
    | cons hd tl ih =>
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact hneg1
    | cons hd tl ih =>
      rw [List.prod_cons, neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction hd with
  | nil => exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> rcases HL.1 with hhd | hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩
/-
**Subring.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：closure_preimage_le (f : R ->+* S) (s : Set S) : closure (f ⁻¹' s) <= (clo
sure s).comap f
参数：f : R ->+* S；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subring.mem_comap`：mem_comap {s : Subring S} {f : R ->+* S} {x : R} : x 
in s.comap f ↔ f x in s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
-/
theorem closure_preimage_le (f : R →+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end Subring

/-! ## Actions by `Subring`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.

When `R` is commutative, `Algebra.ofSubring` provides a stronger result than those found in
this file, which uses the same scalar action.
-/


section Actions

namespace Subring

variable {α β : Type*}


/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example [SMul R α] (S : Subring R) : SMul S α := by infer_instance
/-
**Subring.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m
参数：g : S；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul R α] {S : Subring R} (g : S) (m : α) : g • m = (g : R) • m :=
  rfl
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [SMul R β] [SMul α β] [SMulCommClass R α β] (S : Subring R) :
    SMulCommClass S α β := by infer_instance
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [SMul α β] [SMul R β] [SMulCommClass α R β] (S : Subring R) :
    SMulCommClass α S β := by infer_instance

/-- Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc`. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `IsScalarTower S R R` which is needed by `smul_mul_assoc
`.
-/
example [SMul α β] [SMul R α] [SMul R β] [IsScalarTower R α β] (S : Subring R) :
    IsScalarTower S α β := by infer_instance
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [SMul R α] [FaithfulSMul R α] (S : Subring R) : FaithfulSMul S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example {R} [Ring R] [MulAction R α] (S : Subring R) : MulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example {R} [Ring R] [AddMonoid α] [DistribMulAction R α] (S : Subring R) :
    DistribMulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example {R} [Ring R] [Monoid α] [MulDistribMulAction R α] (S : Subring R) :
    MulDistribMulAction S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example [Zero α] [SMulWithZero R α] (S : Subring R) : SMulWithZero S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example {R} [Ring R] [Zero α] [MulActionWithZero R α] (S : Subring R) :
    MulActionWithZero S α := by infer_instance

/-- The action by a subring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subring is the action by the underlying ring.
-/
example {R} [Ring R] [AddCommMonoid α] [Module R α] (S : Subring R) :
    Module S α := by infer_instance

/-- The action by a subsemiring is the action by the underlying ring. -/
/-
**Subring.** 是 Mathlib 中的一个示例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subsemiring is the action by the underlying ring.
-/
example {R} [Ring R] [Semiring α] [MulSemiringAction R α] (S : Subring R) :
    MulSemiringAction S α := by infer_instance

/-- The center of a semiring acts commutatively on that semiring. -/
/-
**Subring.center.smulCommClass_left** 是 Mathlib 中的一个定理，位于命名空间 `Subring.center`。
形式化陈述：∀ {R : Type u_3} [inst : Ring R], SMulCommClass (↥(Subring.center R)) R R
参数：↥(Subring.center R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.center.smulCommClass_left`：∀ {R' : Type u_1} [inst : Semirin
g R'], SMulCommClass (↥(Subsemiring.center R')) R' R'

--- 原说明 ---
The center of a semiring acts commutatively on that semiring.
-/
instance center.smulCommClass_left {R} [Ring R] : SMulCommClass (center R) R R :=
  Subsemiring.center.smulCommClass_left

/-- The center of a semiring acts commutatively on that semiring. -/
/-
**Subring.center.smulCommClass_right** 是 Mathlib 中的一个定理，位于命名空间 `Subring.center`。
形式化陈述：∀ {R : Type u_3} [inst : Ring R], SMulCommClass R (↥(Subring.center R)) R
参数：↥(Subring.center R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemiring.center.smulCommClass_right`：∀ {R' : Type u_1} [inst : Semiri
ng R'], SMulCommClass R' (↥(Subsemiring.center R')) R'

--- 原说明 ---
The center of a semiring acts commutatively on that semiring.
-/
instance center.smulCommClass_right {R} [Ring R] : SMulCommClass R (center R) R :=
  Subsemiring.center.smulCommClass_right

/-- The center of a semiring acts commutatively on any `R`-module -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a semiring acts commutatively on any `R`-module
-/
instance {R M : Type*} [Ring R] [MulAction R M] :
    SMulCommClass R (Subring.center R) M :=
  inferInstanceAs <| SMulCommClass R (Submonoid.center R) M

/-- The center of a semiring acts commutatively on any `R`-module -/
/-
**Subring.** 是 Mathlib 中的一个实例，位于命名空间 `Subring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a semiring acts commutatively on any `R`-module
-/
instance {R M : Type*} [Ring R] [MulAction R M] :
    SMulCommClass (Subring.center R) R M :=
  inferInstanceAs <| SMulCommClass (Submonoid.center R) R M

end Subring

end Actions

namespace Subring

/-
**Subring.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_comap_eq (f : R ->+* S) (t : Subring S) : (t.comap f).map f = t ⊓ f.ra
nge
参数：f : R ->+* S；t : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : R →+* S) (t : Subring S) : (t.comap f).map f = t ⊓ f.range :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range
/-
**Subring.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_comap_eq_self {f : R ->+* S} {t : Subring S} (h : t <= f.range) : (t.c
omap f).map f = t
参数：h : t <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subring.map_comap_eq`：map_comap_eq (f : R ->+* S) (t : Subring S) : (t.c
omap f).map f = t ⊓ f.range
-/
theorem map_comap_eq_self
    {f : R →+* S} {t : Subring S} (h : t ≤ f.range) : (t.comap f).map f = t := by
  simpa only [inf_of_le_left h] using Subring.map_comap_eq f t
/-
**Subring.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：map_comap_eq_self_of_surjective {f : R ->+* S} (hf : Function.Surjective f
) (t : Subring S) : (t.comap f).map f = t
参数：hf : Function.Surjective f；t : Subring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.map_comap_eq_self`：map_comap_eq_self {f : R ->+* S} {t : Subring
 S} (h : t <= f.range) : (t.comap f).map f = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.range_eq_top_of_surjective`：range_eq_top_of_surjective (f : R ->
+* S) (hf : Function.Surjective f) : f.range = (⊤ : Subring S)
-/
theorem map_comap_eq_self_of_surjective
    {f : R →+* S} (hf : Function.Surjective f) (t : Subring S) : (t.comap f).map f = t :=
  map_comap_eq_self <| by simp [hf]
/-
**Subring.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_map_eq (f : R ->+* S) (s : Subring R) : (s.map f).comap f = s ⊔ clos
ure (f ⁻¹' {0})
参数：f : R ->+* S；s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.mem_map`：mem_map {f : R ->+* S} {s : Subring R} {y : S} : y in s
.map f ↔ exists x in s, f x = y
· 使用定理 `Subring.mem_comap`：mem_comap {s : Subring S} {f : R ->+* S} {x : R} : x 
in s.comap f ↔ f x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.closure_eq`：closure_eq (s : Subring R) : closure (s : Set R) = s
· 使用定理 `Subring.closure_union`：closure_union (s t : Set R) : closure (s union t)
 = closure s ⊔ closure t
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Subring.add_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x + y ∈ s
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `Subring.map_le_iff_le_comap`：map_le_iff_le_comap {f : R ->+* S} {s : Sub
ring R} {t : Subring S} : s.map f <= t ↔ s <= t.comap f
· 使用定理 `Subring.map_sup`：map_sup (s t : Subring R) (f : R ->+* S) : (s ⊔ t).map 
f = s.map f ⊔ t.map f
· 使用定理 `RingHom.map_closure`：map_closure (f : R ->+* S) (s : Set R) : (closure s
).map f = closure (f '' s)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
-/
theorem comap_map_eq (f : R →+* S) (s : Subring R) :
    (s.map f).comap f = s ⊔ closure (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y ∈ f ⁻¹' {0} := by simp [hxy]
    rw [← closure_eq s, ← closure_union, ← add_sub_cancel y x]
    exact Subring.add_mem _ (subset_closure <| Or.inl hy) (subset_closure <| Or.inr hxy)
  · rw [← map_le_iff_le_comap, map_sup, f.map_closure]
    apply le_of_eq
    rw [sup_eq_left, closure_le]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (s.map f).zero_mem)
/-
**Subring.comap_map_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_map_eq_self {f : R ->+* S} {s : Subring R} (h : f ⁻¹' {0} subseteq s
) : (s.map f).comap f = s
参数：h : f ⁻¹' {0} subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_eq_sup`：left_eq_sup : a = a ⊔ b ↔ b <= a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `Subring.comap_map_eq`：comap_map_eq (f : R ->+* S) (s : Subring R) : (s.m
ap f).comap f = s ⊔ closure (f ⁻¹' {0})
-/
theorem comap_map_eq_self {f : R →+* S} {s : Subring R}
    (h : f ⁻¹' {0} ⊆ s) : (s.map f).comap f = s := by
  convert! comap_map_eq f s
  rwa [left_eq_sup, closure_le]
/-
**Subring.comap_map_eq_self_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subring`。
形式化陈述：comap_map_eq_self_of_injective {f : R ->+* S} (hf : Function.Injective f) 
(s : Subring R) : (s.map f).comap f = s
参数：hf : Function.Injective f；s : Subring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem comap_map_eq_self_of_injective
    {f : R →+* S} (hf : Function.Injective f) (s : Subring R) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ hf)

end Subring

/-
**AddSubgroup.int_mul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : Int) {g : R} (h : g in G)
 : (k : R) * g in G
参数：k : Int；h : g in G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `AddSubgroup.zsmul_mem`：∀ {G : Type u_1} [inst : AddGroup G] (K : AddSubg
roup G) {x : G}, x ∈ K → ∀ (n : ℤ), n • x ∈ K
-/
theorem AddSubgroup.int_mul_mem {G : AddSubgroup R} (k : ℤ) {g : R} (h : g ∈ G) :
    (k : R) * g ∈ G := by
  convert AddSubgroup.zsmul_mem G h k
  rw [zsmul_eq_mul]
