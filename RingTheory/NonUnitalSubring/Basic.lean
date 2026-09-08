/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.GroupTheory.Subsemigroup.Center
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring.
We prove that non-unital subrings are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set R` to `NonUnitalSubring R`, sending a subset of
`R` to the non-unital subring it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `instance : CompleteLattice (NonUnitalSubring R)` : the complete lattice structure on the
  non-unital subrings.

* `NonUnitalSubring.center` : the center of a non-unital ring `R`.

* `NonUnitalSubring.closure` : non-unital subring closure of a set, i.e., the smallest
  non-unital subring that includes the set.

* `NonUnitalSubring.gi` : `closure : Set M → NonUnitalSubring M` and coercion
  `coe : NonUnitalSubring M → Set M`
  form a `GaloisInsertion`.

* `comap f B : NonUnitalSubring A` : the preimage of a non-unital subring `B` along the
  non-unital ring homomorphism `f`

* `map f A : NonUnitalSubring B` : the image of a non-unital subring `A` along the
  non-unital ring homomorphism `f`.

* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings

* `f.range : NonUnitalSubring B` : the range of the non-unital ring homomorphism `f`.

* `eq_locus f g : NonUnitalSubring R` : given non-unital ring homomorphisms `f g : R →ₙ+* S`,
     the non-unital subring of `R` where `f x = g x`

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

@[expose] public section


universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

namespace NonUnitalSubring

variable (s : NonUnitalSubring R)

/-- Sum of a list of elements in a non-unital subring is in the non-unital subring. -/
/-
**NonUnitalSubring.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R) {
l : List R}, (∀ x ∈ l, x ∈ s) → l.sum ∈ s
参数：s : NonUnitalSubring R；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
Sum of a list of elements in a non-unital subring is in the non-unital subring.
-/
protected theorem list_sum_mem {l : List R} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in a `NonUnitalSubring` of a `NonUnitalRing` is
in the `NonUnitalSubring`. -/
/-
**NonUnitalSubring.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`
。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
 (m : Multiset R),   (∀ a ∈ m, a ∈ s) → m.sum ∈ s
参数：s : NonUnitalSubring R；m : Multiset R；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
Sum of a multiset of elements in a `NonUnitalSubring` of a `NonUnitalRing` is
in the `NonUnitalSubring`.
-/
protected theorem multiset_sum_mem {R} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem _

/-- Sum of elements in a `NonUnitalSubring` of a `NonUnitalRing` indexed by a `Finset`
is in the `NonUnitalSubring`. -/
/-
**NonUnitalSubring.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
 {ι : Type u_2} {t : Finset ι} {f : ι → R},   (∀ c ∈ t, f c ∈ s) → ∑ i ∈ t, f i 
∈ s
参数：s : NonUnitalSubring R；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
Sum of elements in a `NonUnitalSubring` of a `NonUnitalRing` indexed by a `Finse
t`
is in the `NonUnitalSubring`.
-/
protected theorem sum_mem {R : Type*} [NonUnitalNonAssocRing R] (s : NonUnitalSubring R)
    {ι : Type*} {t : Finset ι} {f : ι → R} (h : ∀ c ∈ t, f c ∈ s) : (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

/-! ## top -/


/-- The non-unital subring `R` of the ring `R`. -/
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-unital subring `R` of the ring `R`.
-/
instance : Top (NonUnitalSubring R) :=
  ⟨{ (⊤ : Subsemigroup R), (⊤ : AddSubgroup R) with }⟩

@[simp]
/-
**NonUnitalSubring.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_top (x : R) : x in (⊤ : NonUnitalSubring R)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : R) : x ∈ (⊤ : NonUnitalSubring R) :=
  Set.mem_univ x

@[simp]
/-
**NonUnitalSubring.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_top : ((⊤ : NonUnitalSubring R) : Set R) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : NonUnitalSubring R) : Set R) = Set.univ :=
  rfl

@[simp]
/-
**NonUnitalSubring.toNonUnitalSubsemiring_top** 是 Mathlib 中的一个引理，位于命名空间 `NonUnit
alSubring`。
形式化陈述：toNonUnitalSubsemiring_top : (⊤ : NonUnitalSubring R).toNonUnitalSubsemiri
ng = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNonUnitalSubsemiring_top : (⊤ : NonUnitalSubring R).toNonUnitalSubsemiring = ⊤ := rfl
/-
**NonUnitalSubring.toAddSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R], ⊤.toAddSubgroup = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddSubgroup_top : (⊤ : NonUnitalSubring R).toAddSubgroup = ⊤ := rfl

@[simp]
/-
**NonUnitalSubring.toNonUnitalSubsemiring_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `NonU
nitalSubring`。
形式化陈述：toNonUnitalSubsemiring_eq_top {S : NonUnitalSubring R} : S.toNonUnitalSubs
emiring = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toNonUnitalSubsemiring_eq_top {S : NonUnitalSubring R} :
    S.toNonUnitalSubsemiring = ⊤ ↔ S = ⊤ := by simp [← SetLike.coe_set_eq]
/-
**NonUnitalSubring.toAddSubgroup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubr
ing`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocRing R] {S : NonUnitalSubring R}, 
S.toAddSubgroup = ⊤ ↔ S = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toAddSubgroup_eq_top {S : NonUnitalSubring R} : S.toAddSubgroup = ⊤ ↔ S = ⊤ := by
  simp [← SetLike.coe_set_eq]

/-- The ring equiv between the top element of `NonUnitalSubring R` and `R`. -/
@[simps!]
/-
**NonUnitalSubring.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：topEquiv : (⊤ : NonUnitalSubring R) ≃+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equiv between the top element of `NonUnitalSubring R` and `R`.
-/
def topEquiv : (⊤ : NonUnitalSubring R) ≃+* R := NonUnitalSubsemiring.topEquiv

end NonUnitalSubring

end Basic

section Hom

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  [FunLike F R S] [NonUnitalRingHomClass F R S] (s : NonUnitalSubring R)

/-! ## comap -/


/-- The preimage of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
/-
**NonUnitalSubring.comap** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [No
nUnitalNonAssocRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s 
: NonUnitalSubring S) : NonUnitalSubring R
参数：f : F；s : NonUnitalSubring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSu
bring`.
-/
def comap {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring S) :
    NonUnitalSubring R :=
  { s.toSubsemigroup.comap (f : R →ₙ* S), s.toAddSubgroup.comap (f : R →+ S) with
    carrier := f ⁻¹' s.carrier }

@[simp]
/-
**NonUnitalSubring.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_comap (s : NonUnitalSubring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s
参数：s : NonUnitalSubring S；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (s : NonUnitalSubring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_comap {s : NonUnitalSubring S} {f : F} {x : R} : x in s.comap f ↔ f x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {s : NonUnitalSubring S} {f : F} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
/-
**NonUnitalSubring.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：comap_comap (s : NonUnitalSubring T) (g : S ->ₙ+* T) (f : R ->ₙ+* S) : (s.
comap g).comap f = s.comap (g.comp f)
参数：s : NonUnitalSubring T；g : S ->ₙ+* T；f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
-/
theorem comap_comap (s : NonUnitalSubring T) (g : S →ₙ+* T) (f : R →ₙ+* S) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ## map -/

/-- The image of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubring`. -/
/-
**NonUnitalSubring.map** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：map {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonU
nitalNonAssocRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : 
NonUnitalSubring R) : NonUnitalSubring S
参数：f : F；s : NonUnitalSubring R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a `NonUnitalSubring` along a ring homomorphism is a `NonUnitalSubri
ng`.
-/
def map {F : Type w} {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) (s : NonUnitalSubring R) :
    NonUnitalSubring S :=
  { s.toSubsemigroup.map (f : R →ₙ* S), s.toAddSubgroup.map (f : R →+ S) with
    carrier := f '' s.carrier }

@[simp]
/-
**NonUnitalSubring.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_map (f : F) (s : NonUnitalSubring R) : (s.map f : Set S) = f '' s
参数：f : F；s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : F) (s : NonUnitalSubring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_map {f : F} {s : NonUnitalSubring R} {y : S} : y in s.map f ↔ exists x
 in s, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_map {f : F} {s : NonUnitalSubring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Set.mem_image _ _ _

@[simp]
/-
**NonUnitalSubring.map_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_id : s.map (NonUnitalRingHom.id R) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id : s.map (NonUnitalRingHom.id R) = s :=
  SetLike.coe_injective <| Set.image_id _
/-
**NonUnitalSubring.map_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_map (g : S ->ₙ+* T) (f : R ->ₙ+* S) : (s.map f).map g = s.map (g.comp 
f)
参数：g : S ->ₙ+* T；f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : S →ₙ+* T) (f : R →ₙ+* S) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.coe_injective <| Set.image_image _ _ _
/-
**NonUnitalSubring.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：map_le_iff_le_comap {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring
 S} : s.map f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubring R} {t : NonUnitalSubring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**NonUnitalSubring.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：gc_map_comap (f : F) : GaloisConnection (map f : NonUnitalSubring R -> Non
UnitalSubring S) (comap f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {s : N
onUnitalSubring R} {t : NonUnitalSubring S} : s.map f <= t ↔ s <= t.comap f
-/
theorem gc_map_comap (f : F) :
    GaloisConnection (map f : NonUnitalSubring R → NonUnitalSubring S) (comap f) := fun _S _T =>
  map_le_iff_le_comap

/-- A `NonUnitalSubring` is isomorphic to its image under an injective function -/
/-
**NonUnitalSubring.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：equivMapOfInjective (f : F) (hf : Function.Injective (f : R -> S)) : s ≃+*
 s.map f
参数：f : F；hf : Function.Injective (f : R -> S)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
A `NonUnitalSubring` is isomorphic to its image under an injective function
-/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R → S)) :
    s ≃+* s.map f :=
  {
    Equiv.Set.image f s
      hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]
/-
**NonUnitalSubring.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubring`。
形式化陈述：coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) 
: (equivMapOfInjective s f hf x : S) = f x
参数：f : F；hf : Function.Injective f；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v} {T : Type*}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] [NonUnitalNonAssocRing T]
  (g : S →ₙ+* T) (f : R →ₙ+* S)

/-! ## range -/

/-- The range of a ring homomorphism, as a `NonUnitalSubring` of the target.
See Note [range copy pattern]. -/
/-
**NonUnitalRingHom.range** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：range {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAss
ocRing S] (f : R ->ₙ+* S) : NonUnitalSubring S
参数：f : R ->ₙ+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism, as a `NonUnitalSubring` of the target.
See Note [range copy pattern].
-/
def range {R : Type u} {S : Type v} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R →ₙ+* S) : NonUnitalSubring S :=
  ((⊤ : NonUnitalSubring R).map f).copy (Set.range f) Set.image_univ.symm

@[simp]
/-
**NonUnitalRingHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_range : (f.range : Set S) = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range : (f.range : Set S) = Set.range f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mem_range {f : R ->ₙ+* S} {y : S} : y in f.range ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range {f : R →ₙ+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl
/-
**NonUnitalRingHom.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：range_eq_map (f : R ->ₙ+* S) : f.range = NonUnitalSubring.map f ⊤
参数：f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
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
theorem range_eq_map (f : R →ₙ+* S) : f.range = NonUnitalSubring.map f ⊤ := by ext; simp
/-
**NonUnitalRingHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mem_range_self (f : R ->ₙ+* S) (x : R) : f x in f.range
参数：f : R ->ₙ+* S；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalRingHom.mem_range`：mem_range {f : R ->ₙ+* S} {y : S} : y in f.r
ange ↔ exists x, f x = y
-/
theorem mem_range_self (f : R →ₙ+* S) (x : R) : f x ∈ f.range :=
  mem_range.mpr ⟨x, rfl⟩
/-
**NonUnitalRingHom.map_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：map_range : f.range.map g = (g.comp f).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.map.congr_simp`：∀ {F : Type w} {R : Type u} {S : Type v
} [inst : NonUnitalNonAssocRing R] [inst_1 : NonUnitalNonAssocRing S]   [inst_2 
: FunLike F R S] [ins…
· 使用定理 `NonUnitalRingHom.range_eq_map`：range_eq_map (f : R ->ₙ+* S) : f.range = 
NonUnitalSubring.map f ⊤
· 使用定理 `NonUnitalSubring.map_map`：map_map (g : S ->ₙ+* T) (f : R ->ₙ+* S) : (s.m
ap f).map g = s.map (g.comp f)
-/
theorem map_range : f.range.map g = (g.comp f).range := by
  simpa only [range_eq_map] using (⊤ : NonUnitalSubring R).map_map g f

/-- The range of a ring homomorphism is a fintype if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`. -/
/-
**NonUnitalRingHom.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
形式化陈述：fintypeRange [Fintype R] [DecidableEq S] (f : R ->ₙ+* S) : Fintype (range 
f)
参数：f : R ->ₙ+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism is a fintype if the domain is a fintype.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype S`.
-/
instance fintypeRange [Fintype R] [DecidableEq S] (f : R →ₙ+* S) : Fintype (range f) :=
  Set.fintypeRange f

end NonUnitalRingHom

namespace NonUnitalSubring

section Order

variable {R : Type u} [NonUnitalNonAssocRing R]

/-! ## bot -/


/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## bot
-/
instance : Bot (NonUnitalSubring R) :=
  ⟨(0 : R →ₙ+* R).range⟩
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NonUnitalSubring R) :=
  ⟨⊥⟩
/-
**NonUnitalSubring.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalRingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem coe_bot : ((⊥ : NonUnitalSubring R) : Set R) = {0} :=
  (NonUnitalRingHom.coe_range (0 : R →ₙ+* R)).trans (@Set.range_const R R _ 0)
/-
**NonUnitalSubring.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_bot {x : R} : x in (⊥ : NonUnitalSubring R) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.coe_bot`：coe_bot : ((⊥ : NonUnitalSubring R) : Set R) =
 {0}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : R} : x ∈ (⊥ : NonUnitalSubring R) ↔ x = 0 :=
  show x ∈ ((⊥ : NonUnitalSubring R) : Set R) ↔ x = 0 by rw [coe_bot, Set.mem_singleton_iff]

/-! ## inf -/

/-- The inf of two `NonUnitalSubring`s is their intersection. -/
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two `NonUnitalSubring`s is their intersection.
-/
instance : Min (NonUnitalSubring R) :=
  ⟨fun s t =>
    { s.toSubsemigroup ⊓ t.toSubsemigroup, s.toAddSubgroup ⊓ t.toAddSubgroup with
      carrier := s ∩ t }⟩

@[simp]
/-
**NonUnitalSubring.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_inf (p p' : NonUnitalSubring R) : ((p ⊓ p' : NonUnitalSubring R) : Set
 R) = (p : Set R) inter p'
参数：p p' : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : NonUnitalSubring R) :
    ((p ⊓ p' : NonUnitalSubring R) : Set R) = (p : Set R) ∩ p' :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_inf {p p' : NonUnitalSubring R} {x : R} : x in p ⊓ p' ↔ x in p ∧ x in 
p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : NonUnitalSubring R} {x : R} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (NonUnitalSubring R) :=
  ⟨fun s =>
    NonUnitalSubring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t)
      (⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t) (by simp) (by simp)⟩

@[simp, norm_cast]
/-
**NonUnitalSubring.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_sInf (S : Set (NonUnitalSubring R)) : ((sInf S : NonUnitalSubring R) :
 Set R) = ⋂ s in S, ↑s
参数：S : Set (NonUnitalSubring R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (NonUnitalSubring R)) :
    ((sInf S : NonUnitalSubring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
/-
**NonUnitalSubring.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x in sInf S ↔ forall p i
n S, x in p
参数：NonUnitalSubring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (NonUnitalSubring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/-
**NonUnitalSubring.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubring R} : (↑(⨅ i, S i) : Set R)
 = ⋂ i, S i
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
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/-
**NonUnitalSubring.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubring R} {x : R} : x in ⨅ i, S i
 ↔ forall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} {x : R} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/-
**NonUnitalSubring.sInf_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) : (sInf s).toSubsemigro
up = ⨅ t in s, NonUnitalSubring.toSubsemigroup t
参数：s : Set (NonUnitalSubring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mk'_toSubsemigroup`：∀ {R : Type u} [inst : NonUnitalNon
AssocRing R] {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup 
R}   (ha : ↑sa = s), (Non…
-/
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
/-
**NonUnitalSubring.sInf_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) : (sInf s).toAddSubgroup
 = ⨅ t in s, NonUnitalSubring.toAddSubgroup t
参数：s : Set (NonUnitalSubring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mk'_toAddSubgroup`：∀ {R : Type u} [inst : NonUnitalNonA
ssocRing R] {s : Set R} {sm : Subsemigroup R} (hm : ↑sm = s) {sa : AddSubgroup R
}   (ha : ↑sa = s), (Non…
-/
theorem sInf_toAddSubgroup (s : Set (NonUnitalSubring R)) :
    (sInf s).toAddSubgroup = ⨅ t ∈ s, NonUnitalSubring.toAddSubgroup t :=
  mk'_toAddSubgroup _ _

/-- `NonUnitalSubring`s of a ring form a complete lattice. -/
/-
**NonUnitalSubring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`NonUnitalSubring`s of a ring form a complete lattice.
-/
instance : CompleteLattice (NonUnitalSubring R) :=
  { completeLatticeOfInf (NonUnitalSubring R) fun _s =>
      IsGLB.of_image (@fun _ _ : NonUnitalSubring R => SetLike.coe_subset_coe)
        isGLB_biInf with
    bot := ⊥
    bot_le := fun s _x hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _s _t₁ _t₂ h₁ h₂ _x hx => ⟨h₁ hx, h₂ hx⟩ }
/-
**NonUnitalSubring.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：eq_top_iff' (A : NonUnitalSubring R) : A = ⊤ ↔ forall x : R, x in A
参数：A : NonUnitalSubring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `NonUnitalSubring.mem_top`：mem_top (x : R) : x in (⊤ : NonUnitalSubring R
)
-/
theorem eq_top_iff' (A : NonUnitalSubring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

end Order

/-! ## Center of a ring -/

section Center
variable {R : Type u}

section NonUnitalNonAssocRing
variable (R) [NonUnitalNonAssocRing R]

/-- The center of a ring `R` is the set of elements that commute with everything in `R` -/
/-
**NonUnitalSubring.center** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：center : NonUnitalSubring R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.neg_mem_center`：neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha
 : a in Set.center M) : -a in Set.center M where comm _

--- 原说明 ---
The center of a ring `R` is the set of elements that commute with everything in 
`R`
-/
def center : NonUnitalSubring R :=
  { NonUnitalSubsemiring.center R with
    neg_mem' := Set.neg_mem_center }
/-
**NonUnitalSubring.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_center : ↑(center R) = Set.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
/-
**NonUnitalSubring.center_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubring`。
形式化陈述：center_toNonUnitalSubsemiring : (center R).toNonUnitalSubsemiring = NonUni
talSubsemiring.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toNonUnitalSubsemiring :
    (center R).toNonUnitalSubsemiring = NonUnitalSubsemiring.center R :=
  rfl

/-- The center is commutative and associative. -/
/-
**NonUnitalSubring.center.instNonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `NonUn
italSubring.center`。
形式化陈述：(R : Type u) → [inst : NonUnitalNonAssocRing R] → NonUnitalCommRing ↥(NonU
nitalSubring.center R)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
The center is commutative and associative.
-/
instance center.instNonUnitalCommRing : NonUnitalCommRing (center R) where
  __ : NonUnitalCommSemiring (center R) :=
    inferInstanceAs <| NonUnitalCommSemiring (NonUnitalSubsemiring.center R)
  __ := (inferInstance : NonUnitalNonAssocRing (center R))

variable {R}

/-- The center of isomorphic (not necessarily unital or associative) rings are isomorphic. -/
/-
**NonUnitalSubring.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：{R : Type u} →   [inst : NonUnitalNonAssocRing R] →     {S : Type u_1} →  
     [inst_1 : NonUnitalNonAssocRing S] → R ≃+* S → ↥(NonUnitalSubring.center R)
 ≃+* ↥(NonUnitalSubring.center S)
参数：NonUnitalSubring.center R；NonUnitalSubring.center S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic (not necessarily unital or associative) rings are isomo
rphic.
-/
@[simps!] def centerCongr {S} [NonUnitalNonAssocRing S] (e : R ≃+* S) : center R ≃+* center S :=
  NonUnitalSubsemiring.centerCongr e

/-- The center of a (not necessarily unital or associative) ring
is isomorphic to the center of its opposite. -/
/-
**NonUnitalSubring.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：{R : Type u} → [inst : NonUnitalNonAssocRing R] → ↥(NonUnitalSubring.cente
r R) ≃+* ↥(NonUnitalSubring.center Rᵐᵒᵖ)
参数：NonUnitalSubring.center R；NonUnitalSubring.center Rᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a (not necessarily unital or associative) ring
is isomorphic to the center of its opposite.
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ :=
  NonUnitalSubsemiring.centerToMulOpposite

end NonUnitalNonAssocRing

section NonUnitalRing
variable [NonUnitalRing R]

-- no instance diamond, unlike the unital version
/-
**NonUnitalSubring.** 是 Mathlib 中的一个示例，位于命名空间 `NonUnitalSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (center.instNonUnitalCommRing _).toNonUnitalRing =
      NonUnitalSubringClass.toNonUnitalRing (center R) := by
  with_reducible_and_instances rfl
/-
**NonUnitalSubring.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_center_iff {z : R} : z in center R ↔ forall g, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ fo
rall g, g * z = z * g
-/
theorem mem_center_iff {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g := Subsemigroup.mem_center_iff
/-
**NonUnitalSubring.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· in cente
r R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mem_center_iff`：mem_center_iff {z : R} : z in center R 
↔ forall g, g * z = z * g
-/
instance decidableMemCenter [DecidableEq R] [Fintype R] : DecidablePred (· ∈ center R) := fun _ =>
  decidable_of_iff' _ mem_center_iff

@[simp]
/-
**NonUnitalSubring.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：center_eq_top (R) [NonUnitalCommRing R] : center R = ⊤
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (R) [NonUnitalCommRing R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end NonUnitalRing

section Centralizer

variable {R : Type*} [NonUnitalRing R]

/-- The centralizer of a set as non-unital subring. -/
/-
**NonUnitalSubring.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：centralizer (s : Set R) : NonUnitalSubring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a set as non-unital subring.
-/
def centralizer (s : Set R) : NonUnitalSubring R :=
  { NonUnitalSubsemiring.centralizer s with
    carrier := s.centralizer
    neg_mem' := Set.neg_mem_centralizer }

@[simp, norm_cast]
/-
**NonUnitalSubring.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_centralizer (s : Set R) : (centralizer s : Set R) = s.centralizer
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl
/-
**NonUnitalSubring.centralizer_toNonUnitalSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalSubring`。
形式化陈述：centralizer_toNonUnitalSubsemiring (s : Set R) : (centralizer s).toNonUnit
alSubsemiring = NonUnitalSubsemiring.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toNonUnitalSubsemiring (s : Set R) :
    (centralizer s).toNonUnitalSubsemiring = NonUnitalSubsemiring.centralizer s :=
  rfl
/-
**NonUnitalSubring.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：mem_centralizer_iff {s : Set R} {z : R} : z in centralizer s ↔ forall g in
 s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
/-
**NonUnitalSubring.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
ring`。
形式化陈述：center_le_centralizer (s) : center R <= centralizer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
/-
**NonUnitalSubring.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：centralizer_le (s t : Set R) (h : s subseteq t) : centralizer t <= central
izer s
参数：s t : Set R；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le (s t : Set R) (h : s ⊆ t) :
    centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
/-
**NonUnitalSubring.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubring`。
形式化陈述：centralizer_eq_top_iff_subset {s : Set R} : centralizer s = ⊤ ↔ s subseteq
 center R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/-
**NonUnitalSubring.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`
。
形式化陈述：centralizer_univ : centralizer Set.univ = center R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

end Center

/-! ## `NonUnitalSubring` closure of a subset -/

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- The `NonUnitalSubring` generated by a set. -/
/-
**NonUnitalSubring.closure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：closure (s : Set R) : NonUnitalSubring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalSubring` generated by a set.
-/
def closure (s : Set R) : NonUnitalSubring R :=
  sInf {S | s ⊆ S}
/-
**NonUnitalSubring.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : NonUnitalSub
ring R, s subseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mem_sInf`：mem_sInf {S : Set (NonUnitalSubring R)} {x : 
R} : x in sInf S ↔ forall p in S, x in p
-/
theorem mem_closure {x : R} {s : Set R} : x ∈ closure s ↔ ∀ S : NonUnitalSubring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The `NonUnitalSubring` generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**NonUnitalSubring.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：subset_closure {s : Set R} : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.mem_closure`：mem_closure {x : R} {s : Set R} : x in clo
sure s ↔ forall S : NonUnitalSubring R, s subseteq S -> x in S

--- 原说明 ---
The `NonUnitalSubring` generated by a set includes the set.
-/
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _x hx => mem_closure.2 fun _S hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**NonUnitalSubring.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubrin
g`。
形式化陈述：mem_closure_of_mem {s : Set R} {x : R} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
-/
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**NonUnitalSubring.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subring`。
形式化陈述：notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A `NonUnitalSubring` `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/-
**NonUnitalSubring.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：closure_le {s : Set R} {t : NonUnitalSubring R} : closure s <= t ↔ s subse
teq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
A `NonUnitalSubring` `t` includes `closure s` if and only if it includes `s`.
-/
theorem closure_le {s : Set R} {t : NonUnitalSubring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- `NonUnitalSubring` closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/-
**NonUnitalSubring.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s

--- 原说明 ---
`NonUnitalSubring` closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`.
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
/-
**NonUnitalSubring.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`
。
形式化陈述：closure_eq_of_le {s : Set R} {t : NonUnitalSubring R} (h₁ : s subseteq t) 
(h₂ : t <= closure s) : closure s = t
参数：h₁ : s subseteq t；h₂ : t <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t
-/
theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubring R} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
/-
**NonUnitalSubring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (neg : f
orall x hx, p x hx -> p (-x) (neg_mem hx)) (mul : forall x y hx hy, p x hx -> p 
y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；n
eg : forall x hx, p x hx -> p (-x) (neg_mem hx)；mul : forall x y hx hy, p x hx -
> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `0`, `1`, and al
l elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` 
holds for all
elements of the closure of `s`.
-/
theorem closure_induction {s : Set R} {p : (x : R) → x ∈ closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_closure hx)) (zero : p 0 (zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let K : NonUnitalSubring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      neg_mem' := fun ⟨_, hpx⟩ ↦ ⟨_, neg _ _ hpx⟩
      zero_mem' := ⟨_, zero⟩ }
  closure_le (t := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership, for predicates with two arguments. -/
@[elab_as_elim]
/-
**NonUnitalSubring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (neg : f
orall x hx, p x hx -> p (-x) (neg_mem hx)) (mul : forall x y hx hy, p x hx -> p 
y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in closure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；n
eg : forall x hx, p x hx -> p (-x) (neg_mem hx)；mul : forall x y hx hy, p x hx -
> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership, for predicates with two arguments
.
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ closure s → y ∈ closure s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
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
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | neg _ _ h => exact neg_left _ _ _ _ h
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | neg _ _ h => exact neg_right _ _ _ _ h
/-
**NonUnitalSubring.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_closure_iff {s : Set R} {x} : x in closure s ↔ x in AddSubgroup.closur
e (Subsemigroup.closure s : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.closure_induction`：closure_induction {s : Set R} {p : (
x : R) -> x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_c
losure hx)) (zero : p 0 …
· 使用定理 `AddSubgroup.subset_closure`：∀ {G : Type u_1} [inst : AddGroup G] {k : Se
t G}, k ⊆ ↑(AddSubgroup.closure k)
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
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
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
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
· 使用定理 `Subsemigroup.closure_induction`：closure_induction {p : (x : M) -> x in c
losure s -> Prop} (mem : forall (x) (h : x in s), p x (subset_closure h)) (mul :
 forall x y hx hy, p…
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
（共 33 条，此处仅展示前 30 条）
-/
theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubgroup.closure (Subsemigroup.closure s : Set R) :=
  ⟨fun h => by
    induction h using closure_induction with
    | mem _ hx => exact AddSubgroup.subset_closure (Subsemigroup.subset_closure hx)
    | zero => exact zero_mem _
    | add _ _ _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
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
    | mem _ hx => induction hx using Subsemigroup.closure_induction with
      | mem _ h => exact subset_closure h
      | mul _ _ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | neg _ _ h => exact neg_mem h⟩
/-
**NonUnitalSubring.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 
`NonUnitalSubring`。
形式化陈述：closure_le_centralizer_centralizer {R : Type*} [NonUnitalRing R] (s : Set 
R) : closure s <= centralizer (centralizer s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer {R : Type*} [NonUnitalRing R] (s : Set R) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
semiring. -/
/-
**NonUnitalSubring.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subring`。
形式化陈述：isMulCommutative_closure {R : Type*} [NonUnitalRing R] {s : Set R} (hcomm 
: forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalSubring.closure_le_centralizer_centralizer`：closure_le_centrali
zer_centralizer {R : Type*} [NonUnitalRing R] (s : Set R) : closure s <= central
izer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a non-unital commu
tative
semiring.
-/
theorem isMulCommutative_closure {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
ring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/-
**NonUnitalSubring.closureNonUnitalCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `N
onUnitalSubring`。
形式化陈述：closureNonUnitalCommRingOfComm {R : Type*} [NonUnitalRing R] {s : Set R} (
hcomm : forall x in s, forall y in s, x * y = y * x) : NonUnitalCommRing (closur
e s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.isMulCommutative_closure`：isMulCommutative_closure {R :
 Type*} [NonUnitalRing R] {s : Set R} (hcomm : forall x in s, forall y in s, x *
 y = y * x) : IsMulCommutative …

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a non-unital commu
tative
ring.
-/
abbrev closureNonUnitalCommRingOfComm {R : Type*} [NonUnitalRing R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : NonUnitalCommRing (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance
/-
**NonUnitalSubring.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubring`。
形式化陈述：instIsMulCommutative_closure {S R : Type*} [NonUnitalRing R] [SetLike S R]
 [MulMemClass S R] (s : S) [IsMulCommutative s] : IsMulCommutative (closure (s :
 Set R))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.isMulCommutative_closure`：isMulCommutative_closure {R :
 Type*} [NonUnitalRing R] {s : Set R} (hcomm : forall x in s, forall y in s, x *
 y = y * x) : IsMulCommutative …
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S R : Type*} [NonUnitalRing R]
    [SetLike S R] [MulMemClass S R] (s : S) [IsMulCommutative s] :
    IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable (R) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**NonUnitalSubring.gi** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：(R : Type u) → [inst : NonUnitalNonAssocRing R] → GaloisInsertion NonUnita
lSubring.closure SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure R _) SetLike.coe where
  choice s _ := closure s
  gc _s _t := closure_le
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl

/-- Closure of a `NonUnitalSubring` `S` equals `S`. -/
@[simp]
/-
**NonUnitalSubring.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：closure_eq (s : NonUnitalSubring R) : closure (s : Set R) = s
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a `NonUnitalSubring` `S` equals `S`.
-/
theorem closure_eq (s : NonUnitalSubring R) : closure (s : Set R) = s :=
  (NonUnitalSubring.gi R).l_u_eq s

@[simp]
/-
**NonUnitalSubring.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
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
  (NonUnitalSubring.gi R).gc.l_bot

@[simp]
/-
**NonUnitalSubring.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：closure_univ : closure (Set.univ : Set R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.closure_eq`：closure_eq (s : NonUnitalSubring R) : closu
re (s : Set R) = s
· 使用定理 `NonUnitalSubring.coe_top`：coe_top : ((⊤ : NonUnitalSubring R) : Set R) =
 Set.univ
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
/-
**NonUnitalSubring.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
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
  (NonUnitalSubring.gi R).gc.l_sup
/-
**NonUnitalSubring.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
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
  (NonUnitalSubring.gi R).gc.l_iSup
/-
**NonUnitalSubring.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
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
  (NonUnitalSubring.gi R).gc.l_sSup
/-
**NonUnitalSubring.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_sup (s t : NonUnitalSubring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.m
ap f
参数：s t : NonUnitalSubring R；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem map_sup (s t : NonUnitalSubring R) (f : F) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**NonUnitalSubring.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_iSup {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring R) : (iSup s).map 
f = ⨆ i, (s i).map f
参数：f : F；s : ι -> NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι → NonUnitalSubring R) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**NonUnitalSubring.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_inf (s t : NonUnitalSubring R) (f : F) (hf : Function.Injective f) : (
s ⊓ t).map f = s.map f ⊓ t.map f
参数：s t : NonUnitalSubring R；f : F；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (s t : NonUnitalSubring R) (f : F) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)
/-
**NonUnitalSubring.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f) (s :
 ι -> NonUnitalSubring R) : (iInf s).map f = ⨅ i, (s i).map f
参数：f : F；hf : Function.Injective f；s : ι -> NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubri
ng R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι → NonUnitalSubring R) : (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**NonUnitalSubring.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f
 ⊓ t.comap f
参数：s t : NonUnitalSubring S；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem comap_inf (s t : NonUnitalSubring S) (f : F) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
/-
**NonUnitalSubring.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：comap_iInf {ι : Sort*} (f : F) (s : ι -> NonUnitalSubring S) : (iInf s).co
map f = ⨅ i, (s i).comap f
参数：f : F；s : ι -> NonUnitalSubring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι → NonUnitalSubring S) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**NonUnitalSubring.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：map_bot (f : R ->ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥
参数：f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem map_bot (f : R →ₙ+* S) : (⊥ : NonUnitalSubring R).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**NonUnitalSubring.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：comap_top (f : R ->ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤
参数：f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
-/
theorem comap_top (f : R →ₙ+* S) : (⊤ : NonUnitalSubring S).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- Given `NonUnitalSubring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is `s ×ˢ t`
as a `NonUnitalSubring` of `R × S`. -/
/-
**NonUnitalSubring.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring 
(R × S)
参数：s : NonUnitalSubring R；t : NonUnitalSubring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `NonUnitalSubring`s `s`, `t` of rings `R`, `S` respectively, `s.prod t` is
 `s ×ˢ t`
as a `NonUnitalSubring` of `R × S`.
-/
def prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : NonUnitalSubring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubgroup.prod t.toAddSubgroup with
    carrier := s ×ˢ t }

@[norm_cast]
/-
**NonUnitalSubring.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：coe_prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) : (s.prod t : S
et (R × S)) = (s : Set R) ×ˢ t
参数：s : NonUnitalSubring R；t : NonUnitalSubring S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : NonUnitalSubring R) (t : NonUnitalSubring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ t :=
  rfl
/-
**NonUnitalSubring.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_prod {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S} : p
 in s.prod t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : NonUnitalSubring R} {t : NonUnitalSubring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[gcongr, mono]
/-
**NonUnitalSubring.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalS
ubring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄
    (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
/-
**NonUnitalSubring.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：prod_mono_right (s : NonUnitalSubring R) : Monotone fun t : NonUnitalSubri
ng S => s.prod t
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.prod_mono`：prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs :
 s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod 
t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_right (s : NonUnitalSubring R) :
    Monotone fun t : NonUnitalSubring S => s.prod t :=
  prod_mono (le_refl s)
/-
**NonUnitalSubring.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：prod_mono_left (t : NonUnitalSubring S) : Monotone fun s : NonUnitalSubrin
g R => s.prod t
参数：t : NonUnitalSubring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.prod_mono`：prod_mono ⦃s₁ s₂ : NonUnitalSubring R⦄ (hs :
 s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod 
t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_left (t : NonUnitalSubring S) : Monotone fun s : NonUnitalSubring R => s.prod t :=
  fun _s₁ _s₂ hs => prod_mono hs (le_refl t)
/-
**NonUnitalSubring.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：prod_top (s : NonUnitalSubring R) : s.prod (⊤ : NonUnitalSubring S) = s.co
map (NonUnitalRingHom.fst R S)
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (s : NonUnitalSubring R) :
    s.prod (⊤ : NonUnitalSubring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod]
/-
**NonUnitalSubring.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：top_prod (s : NonUnitalSubring S) : (⊤ : NonUnitalSubring R).prod s = s.co
map (NonUnitalRingHom.snd R S)
参数：s : NonUnitalSubring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.ext`：ext {S T : NonUnitalSubring R} (h : forall x, x in
 S ↔ x in T) : S = T
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
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
theorem top_prod (s : NonUnitalSubring S) :
    (⊤ : NonUnitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/-
**NonUnitalSubring.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubring.top_prod`：top_prod (s : NonUnitalSubring S) : (⊤ : NonU
nitalSubring R).prod s = s.comap (NonUnitalRingHom.snd R S)
· 使用定理 `NonUnitalSubring.comap_top`：comap_top (f : R ->ₙ+* S) : (⊤ : NonUnitalSu
bring S).comap f = ⊤
-/
theorem top_prod_top : (⊤ : NonUnitalSubring R).prod (⊤ : NonUnitalSubring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
/-
**NonUnitalSubring.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalNonAssocRing R] [inst_1 : Non
UnitalNonAssocRing S],   NonUnitalSubring.center (R × S) = (NonUnitalSubring.cen
ter R).prod (NonUnitalSubring.center S)
参数：R × S；NonUnitalSubring.center R；NonUnitalSubring.center S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/-- Product of `NonUnitalSubring`s is isomorphic to their product as rings. -/
/-
**NonUnitalSubring.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+*
 s × t
参数：s : NonUnitalSubring R；t : NonUnitalSubring S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R

--- 原说明 ---
Product of `NonUnitalSubring`s is isomorphic to their product as rings.
-/
def prodEquiv (s : NonUnitalSubring R) (t : NonUnitalSubring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- The underlying set of a non-empty directed Sup of `NonUnitalSubring`s is just a union of the
`NonUnitalSubring`s. Note that this fails without the directedness assumption (the union of two
`NonUnitalSubring`s is typically not a `NonUnitalSubring`) -/
/-
**NonUnitalSubring.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubr
ing`。
形式化陈述：mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubring R} (
hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.mk'`：mk'_toSubsemigroup {s : Set R} {sm : Subsemigroup 
R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s) : (NonUnitalSubring.mk' s 
sm sa hm h…
· 使用定理 `Subsemigroup.coe_iSup_of_directed`：coe_iSup_of_directed {S : ι -> Subsem
igroup M} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃
 i, S i
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
The underlying set of a non-empty directed Sup of `NonUnitalSubring`s is just a 
union of the
`NonUnitalSubring`s. Note that this fails without the directedness assumption (t
he union of two
`NonUnitalSubring`s is typically not a `NonUnitalSubring`)
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : NonUnitalSubring R :=
    NonUnitalSubring.mk' (⋃ i, (S i : Set R)) (⨆ i, (S i).toSubsemigroup) (⨆ i, (S i).toAddSubgroup)
      (Subsemigroup.coe_iSup_of_directed hS) (AddSubgroup.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx ↦ Set.mem_iUnion.2 ⟨i, hx⟩
/-
**NonUnitalSubring.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubr
ing`。
形式化陈述：coe_iSup_of_directed {ι} [Nonempty ι] {S : ι -> NonUnitalSubring R} (hS : 
Directed (· <= ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, S i
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
· 使用定理 `NonUnitalSubring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : No
nempty ι] {S : ι -> NonUnitalSubring R} (hS : Directed (· <= ·) S) {x : R} : (x 
in ⨆ i, S i) ↔ exists i, x …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → NonUnitalSubring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]
/-
**NonUnitalSubring.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bring`。
形式化陈述：mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty) (
hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s
参数：NonUnitalSubring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
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
· 使用定理 `NonUnitalSubring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : No
nempty ι] {S : ι -> NonUnitalSubring R} (hS : Directed (· <= ·) S) {x : R} : (x 
in ⨆ i, S i) ↔ exists i, x …
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists,
    exists_prop]
/-
**NonUnitalSubring.coe_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bring`。
形式化陈述：coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty) (
hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s
参数：NonUnitalSubring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.mem_sSup_of_directedOn`：mem_sSup_of_directedOn {S : Set
 (NonUnitalSubring R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S) {x : R} :
 x in sSup S ↔ exists s in S,…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
/-
**NonUnitalSubring.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
ring`。
形式化陈述：isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubring 
R} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsMulCo
mmutative (⨆ i, S i : NonUnitalSubring R)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [Nonempt
y ι] {S : ι -> NonUnitalSubring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Non
UnitalSubring R) : Set R) =…
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
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalSubsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) : ((⨆
 i, S i : NonUnitalSubsemiring …
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : S
ort*} [Nonempty ι] {S : ι -> NonUnitalSubsemiring R} [hS : forall i, IsMulCommut
ative (S i)] (dir : Directed (· …
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι → NonUnitalSubring R}
    [hS : ∀ i, IsMulCommutative (S i)] (dir : Directed (· ≤ ·) S) :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) := by
  simpa [isMulCommutative_iff, ← SetLike.mem_coe, NonUnitalSubsemiring.coe_iSup_of_directed dir,
    coe_iSup_of_directed dir] using NonUnitalSubsemiring.isMulCommutative_iSup dir
/-
**NonUnitalSubring.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `NonUnita
lSubring`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o NonUnitalSubring R} [hS : forall i, IsMulCommutative (S i)]
 : IsMulCommutative (⨆ i, S i : NonUnitalSubring R)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `NonUnitalSubring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : Sort*
} [Nonempty ι] {S : ι -> NonUnitalSubring R} [hS : forall i, IsMulCommutative (S
 i)] (dir : Directed (· <= ·…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirectedOrder ι]
    {S : ι →o NonUnitalSubring R} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubring R) :=
  isMulCommutative_iSup S.monotone.directed_le
/-
**NonUnitalSubring.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubring R} {x : S} : x in K.map 
(f : R ->ₙ+* S) ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubring R} {x : S} :
    x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K :=
  @Set.mem_image_equiv _ _ (K : Set R) f.toEquiv x
/-
**NonUnitalSubring.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubring`。
形式化陈述：map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubring R) : K.map (f 
: R ->ₙ+* S) = K.comap f.symm
参数：f : R ≃+* S；K : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubring R) :
    K.map (f : R →ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)
/-
**NonUnitalSubring.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubring`。
形式化陈述：comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubring S) : K.comap (
f : R ->ₙ+* S) = K.map f.symm
参数：f : R ≃+* S；K : NonUnitalSubring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `NonUnitalSubring.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : R
 ≃+* S) (K : NonUnitalSubring R) : K.map (f : R ->ₙ+* S) = K.comap f.symm
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubring S) :
    K.comap (f : R →ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubring

namespace NonUnitalRingHom

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalSubring

/-- Restriction of a ring homomorphism to its range interpreted as a `NonUnitalSubring`.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**NonUnitalRingHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：rangeRestrict (f : R ->ₙ+* S) : R ->ₙ+* f.range
参数：f : R ->ₙ+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a ring homomorphism to its range interpreted as a `NonUnitalSubri
ng`.

This is the bundled version of `Set.rangeFactorization`.
-/
def rangeRestrict (f : R →ₙ+* S) : R →ₙ+* f.range :=
  NonUnitalRingHom.codRestrict f f.range fun x => ⟨x, rfl⟩

@[simp]
/-
**NonUnitalRingHom.coe_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom
`。
形式化陈述：coe_rangeRestrict (f : R ->ₙ+* S) (x : R) : (f.rangeRestrict x : S) = f x
参数：f : R ->ₙ+* S；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
-/
theorem coe_rangeRestrict (f : R →ₙ+* S) (x : R) : (f.rangeRestrict x : S) = f x :=
  rfl
/-
**NonUnitalRingHom.rangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
RingHom`。
形式化陈述：rangeRestrict_surjective (f : R ->ₙ+* S) : Function.Surjective f.rangeRest
rict
参数：f : R ->ₙ+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHom.mem_range`：mem_range {f : R ->ₙ+* S} {y : S} : y in f.r
ange ↔ exists x, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem rangeRestrict_surjective (f : R →ₙ+* S) : Function.Surjective f.rangeRestrict :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := mem_range.mp hy
  ⟨x, Subtype.ext hx⟩
/-
**NonUnitalRingHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：range_eq_top {f : R ->ₙ+* S} : f.range = (⊤ : NonUnitalSubring S) ↔ Functi
on.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalRingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
· 使用定理 `NonUnitalSubring.coe_top`：coe_top : ((⊤ : NonUnitalSubring R) : Set R) =
 Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem range_eq_top {f : R →ₙ+* S} :
    f.range = (⊤ : NonUnitalSubring S) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective ring homomorphism is the whole of the codomain. -/
@[simp]
/-
**NonUnitalRingHom.range_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alRingHom`。
形式化陈述：range_eq_top_of_surjective (f : R ->ₙ+* S) (hf : Function.Surjective f) : 
f.range = (⊤ : NonUnitalSubring S)
参数：f : R ->ₙ+* S；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalRingHom.range_eq_top`：range_eq_top {f : R ->ₙ+* S} : f.range = 
(⊤ : NonUnitalSubring S) ↔ Function.Surjective f

--- 原说明 ---
The range of a surjective ring homomorphism is the whole of the codomain.
-/
theorem range_eq_top_of_surjective (f : R →ₙ+* S) (hf : Function.Surjective f) :
    f.range = (⊤ : NonUnitalSubring S) :=
  range_eq_top.2 hf

/-- The `NonUnitalSubring` of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a `NonUnitalSubring` of R -/
/-
**NonUnitalRingHom.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：eqLocus (f g : R ->ₙ+* S) : NonUnitalSubring R
参数：f g : R ->ₙ+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalSubring` of elements `x : R` such that `f x = g x`, i.e.,
  the equalizer of f and g as a `NonUnitalSubring` of R
-/
def eqLocus (f g : R →ₙ+* S) : NonUnitalSubring R :=
  { (f : R →ₙ* S).eqLocus g, (f : R →+ S).eqLocus g with carrier := {x | f x = g x} }

@[simp]
/-
**NonUnitalRingHom.mem_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mem_eqLocus {f g : R ->ₙ+* S} {x : R} : x in f.eqLocus g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocus {f g : R →ₙ+* S} {x : R} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

@[simp]
/-
**NonUnitalRingHom.eqLocus_same** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：eqLocus_same (f : R ->ₙ+* S) : f.eqLocus f = ⊤
参数：f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem eqLocus_same (f : R →ₙ+* S) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two ring homomorphisms are equal on a set, then they are equal on its
`NonUnitalSubring` closure. -/
/-
**NonUnitalRingHom.eqOn_set_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`
。
形式化陈述：eqOn_set_closure {f g : R ->ₙ+* S} {s : Set R} (h : Set.EqOn f g s) : Set.
EqOn f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
If two ring homomorphisms are equal on a set, then they are equal on its
`NonUnitalSubring` closure.
-/
theorem eqOn_set_closure {f g : R →ₙ+* S} {s : Set R} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from closure_le.2 h
/-
**NonUnitalRingHom.eq_of_eqOn_set_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHo
m`。
形式化陈述：eq_of_eqOn_set_top {f g : R ->ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubri
ng R)) : f = g
参数：h : Set.EqOn f g (⊤ : NonUnitalSubring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_set_top {f g : R →ₙ+* S} (h : Set.EqOn f g (⊤ : NonUnitalSubring R)) : f = g :=
  ext fun _x => h trivial
/-
**NonUnitalRingHom.eq_of_eqOn_set_dense** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRing
Hom`。
形式化陈述：eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R ->ₙ+* S} (h
 : s.EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.eq_of_eqOn_set_top`：eq_of_eqOn_set_top {f g : R ->ₙ+* S
} (h : Set.EqOn f g (⊤ : NonUnitalSubring R)) : f = g
· 使用定理 `NonUnitalRingHom.eqOn_set_closure`：eqOn_set_closure {f g : R ->ₙ+* S} {s
 : Set R} (h : Set.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_set_dense {s : Set R} (hs : closure s = ⊤) {f g : R →ₙ+* S} (h : s.EqOn f g) :
    f = g :=
  eq_of_eqOn_set_top <| hs ▸ eqOn_set_closure h
/-
**NonUnitalRingHom.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingH
om`。
形式化陈述：closure_preimage_le (f : R ->ₙ+* S) (s : Set S) : closure (f ⁻¹' s) <= (cl
osure s).comap f
参数：f : R ->ₙ+* S；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `NonUnitalSubring.mem_comap`：mem_comap {s : NonUnitalSubring S} {f : F} {
x : R} : x in s.comap f ↔ f x in s
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
-/
theorem closure_preimage_le (f : R →ₙ+* S) (s : Set S) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the `NonUnitalSubring` generated by a set equals
the `NonUnitalSubring` generated by the image of the set. -/
/-
**NonUnitalRingHom.map_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：map_closure (f : R ->ₙ+* S) (s : Set R) : (closure s).map f = closure (f '
' s)
参数：f : R ->ₙ+* S；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubring.gc_map_comap`：gc_map_comap (f : F) : GaloisConnection (
map f : NonUnitalSubring R -> NonUnitalSubring S) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The image under a ring homomorphism of the `NonUnitalSubring` generated by a set
 equals
the `NonUnitalSubring` generated by the image of the set.
-/
theorem map_closure (f : R →ₙ+* S) (s : Set R) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubring.gi S).gc
    (NonUnitalSubring.gi R).gc fun _ ↦ rfl

end NonUnitalRingHom

namespace NonUnitalSubring

variable {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]

open NonUnitalRingHom

@[simp]
/-
**NonUnitalSubring.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：range_subtype (s : NonUnitalSubring R) : (NonUnitalSubringClass.subtype s)
.range = s
参数：s : NonUnitalSubring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubring.instNonUnitalSubringClass`：∀ {R : Type u} [inst : NonUn
italNonAssocRing R], NonUnitalSubringClass (NonUnitalSubring R) R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalRingHom.coe_srange`：coe_srange : (srange f : Set S) = Set.range
 f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_subtype (s : NonUnitalSubring R) : (NonUnitalSubringClass.subtype s).range = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe
/-
**NonUnitalSubring.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：range_fst : NonUnitalRingHom.srange (fst R S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.range_fst`：range_fst : NonUnitalRingHom.srange (fst
 R S) = ⊤
-/
theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalSubsemiring.range_fst
/-
**NonUnitalSubring.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring`。
形式化陈述：range_snd : NonUnitalRingHom.srange (snd R S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.range_snd`：range_snd : NonUnitalRingHom.srange (snd
 R S) = ⊤
-/
theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalSubsemiring.range_snd

end NonUnitalSubring

namespace RingEquiv

variable {R : Type u} {S : Type v} [NonUnitalRing R] [NonUnitalRing S] {s t : NonUnitalSubring R}

/-- Makes the identity isomorphism from a proof two `NonUnitalSubring`s of a multiplicative
monoid are equal. -/
/-
**RingEquiv.nonUnitalSubringCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：nonUnitalSubringCongr (h : s = t) : s ≃+* t
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes the identity isomorphism from a proof two `NonUnitalSubring`s of a multipl
icative
monoid are equal.
-/
def nonUnitalSubringCongr (h : s = t) : s ≃+* t :=
  {
    Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`. -/
/-
**RingEquiv.ofLeftInverse'** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：ofLeftInverse' {g : S -> R} {f : R ->ₙ+* S} (h : Function.LeftInverse g f)
 : R ≃+* f.range
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a ring homomorphism with a left inverse to a ring isomorphism to its
`RingHom.range`.
-/
def ofLeftInverse' {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) : R ≃+* f.range :=
  { f.rangeRestrict with
    toFun := fun x => f.rangeRestrict x
    invFun := fun x => (g ∘ NonUnitalSubringClass.subtype f.range) x
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**RingEquiv.ofLeftInverse'_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalRing R] [inst_1 : NonUnitalRi
ng S] {g : S → R} {f : R →ₙ+* S}   (h : Function.LeftInverse g ⇑f) (x : R), ↑((R
ingEquiv.ofLeftInverse' h) x) = f x
参数：h : Function.LeftInverse g ⇑f；x : R；(RingEquiv.ofLeftInverse' h) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse'_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f) (x : R) :
    ↑(ofLeftInverse' h x) = f x :=
  rfl

@[simp]
/-
**RingEquiv.ofLeftInverse'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalRing R] [inst_1 : NonUnitalRi
ng S] {g : S → R} {f : R →ₙ+* S}   (h : Function.LeftInverse g ⇑f) (x : ↥f.range
), (RingEquiv.ofLeftInverse' h).symm x = g ↑x
参数：h : Function.LeftInverse g ⇑f；x : ↥f.range；RingEquiv.ofLeftInverse' h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse'_symm_apply {g : S → R} {f : R →ₙ+* S} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse' h).symm x = g x :=
  rfl

end RingEquiv

namespace NonUnitalSubring

variable {F : Type w} {R : Type u} {S : Type v}
  [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
  [FunLike F R S] [NonUnitalRingHomClass F R S]

/-
**NonUnitalSubring.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubri
ng`。
形式化陈述：closure_preimage_le (f : F) (s : Set S) : closure ((f : R -> S) ⁻¹' s) <= 
(closure s).comap f
参数：f : F；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubring.closure_le`：closure_le {s : Set R} {t : NonUnitalSubrin
g R} : closure s <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `NonUnitalSubring.mem_comap`：mem_comap {s : NonUnitalSubring S} {f : F} {
x : R} : x in s.comap f ↔ f x in s
· 使用定理 `NonUnitalSubring.subset_closure`：subset_closure {s : Set R} : s subseteq
 closure s
-/
theorem closure_preimage_le (f : F) (s : Set S) :
    closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _x hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

end NonUnitalSubring

end Hom

