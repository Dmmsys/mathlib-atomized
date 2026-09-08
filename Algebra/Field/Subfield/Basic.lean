/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file concerns the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `instance : CompleteLattice (Subfield K)` : the complete lattice structure on the subfields.

* `Subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `Subfield.gi` : `closure : Set M → Subfield M` and coercion `(↑) : Subfield M → Set M`
  form a `GaloisInsertion`.

* `comap f B : Subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : Subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `f.fieldRange : Subfield L` : the range of the ring homomorphism `f`.

* `eqLocusField f g : Subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

@[expose] public section


universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

namespace Subfield

variable (s t : Subfield K)

section DerivedFromSubfieldClass

/-- Product of a list of elements in a subfield is in the subfield. -/
/-
**Subfield.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {l : List K}, (∀ x
 ∈ l, x ∈ s) → l.prod ∈ s
参数：s : Subfield K；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Product of a list of elements in a subfield is in the subfield.
-/
protected theorem list_prod_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.prod ∈ s :=
  list_prod_mem

/-- Sum of a list of elements in a subfield is in the subfield. -/
/-
**Subfield.list_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {l : List K}, (∀ x
 ∈ l, x ∈ s) → l.sum ∈ s
参数：s : Subfield K；∀ x ∈ l, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_sum_mem`：∀ {M : Type u_1} {B : Type u_3} [inst : AddMonoid M] [inst
_1 : SetLike B M] [AddSubmonoidClass B M] {S : B}   {l : List M}, (∀ x ∈ l, x ∈ 
S)…
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Sum of a list of elements in a subfield is in the subfield.
-/
protected theorem list_sum_mem {l : List K} : (∀ x ∈ l, x ∈ s) → l.sum ∈ s :=
  list_sum_mem

/-- Sum of a multiset of elements in a `Subfield` is in the `Subfield`. -/
/-
**Subfield.multiset_sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) (m : Multiset K), 
(∀ a ∈ m, a ∈ s) → m.sum ∈ s
参数：s : Subfield K；m : Multiset K；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   (m : Multiset M), (∀
 a ∈ m…
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Sum of a multiset of elements in a `Subfield` is in the `Subfield`.
-/
protected theorem multiset_sum_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s :=
  multiset_sum_mem m

/-- Sum of elements in a `Subfield` indexed by a `Finset` is in the `Subfield`. -/
/-
**Subfield.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K) {ι : Type u_1} {t 
: Finset ι} {f : ι → K},   (∀ c ∈ t, f c ∈ s) → ∑ i ∈ t, f i ∈ s
参数：s : Subfield K；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Sum of elements in a `Subfield` indexed by a `Finset` is in the `Subfield`.
-/
protected theorem sum_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∑ i ∈ t, f i) ∈ s :=
  sum_mem h

end DerivedFromSubfieldClass

/-! ### top -/


/-- The subfield of `K` containing all elements of `K`. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfield of `K` containing all elements of `K`.
-/
instance : Top (Subfield K) :=
  ⟨{ (⊤ : Subring K) with inv_mem' := fun x _ => Subring.mem_top x }⟩
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Subfield K) :=
  ⟨⊤⟩

@[simp]
/-
**Subfield.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_top (x : K) : x in (⊤ : Subfield K)
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : K) : x ∈ (⊤ : Subfield K) :=
  Set.mem_univ x

@[simp, norm_cast]
/-
**Subfield.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_top : ((⊤ : Subfield K) : Set K) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Subfield K) : Set K) = Set.univ :=
  rfl

/-- The ring equiv between the top element of `Subfield K` and `K`. -/
/-
**Subfield.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：topEquiv : (⊤ : Subfield K) ≃+* K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equiv between the top element of `Subfield K` and `K`.
-/
def topEquiv : (⊤ : Subfield K) ≃+* K :=
  Subsemiring.topEquiv

/-! ### comap -/


variable (f : K →+* L)

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
/-
**Subfield.comap** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：comap (s : Subfield L) : Subfield K
参数：s : Subfield L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subfield along a ring homomorphism is a subfield.
-/
def comap (s : Subfield L) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun x hx =>
      show f x⁻¹ ∈ s by
        rw [map_inv₀ f]
        exact s.inv_mem hx }

@[simp]
/-
**Subfield.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s
参数：s : Subfield L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (s : Subfield L) : (s.comap f : Set K) = f ⁻¹' s :=
  rfl

@[simp]
/-
**Subfield.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_comap {s : Subfield L} {f : K ->+* L} {x : K} : x in s.comap f ↔ f x i
n s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {s : Subfield L} {f : K →+* L} {x : K} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl
/-
**Subfield.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：comap_comap (s : Subfield M) (g : L ->+* M) (f : K ->+* L) : (s.comap g).c
omap f = s.comap (g.comp f)
参数：s : Subfield M；g : L ->+* M；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (s : Subfield M) (g : L →+* M) (f : K →+* L) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

/-! ### map -/


/-- The image of a subfield along a ring homomorphism is a subfield. -/
/-
**Subfield.map** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：map (s : Subfield K) : Subfield L
参数：s : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a subfield along a ring homomorphism is a subfield.
-/
def map (s : Subfield K) : Subfield L :=
  { s.toSubring.map f with
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x⁻¹, s.inv_mem hx, map_inv₀ f x⟩ }

@[simp, norm_cast]
/-
**Subfield.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_map : (s.map f : Set L) = f '' s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map : (s.map f : Set L) = f '' s :=
  rfl

@[simp]
/-
**Subfield.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_map {f : K ->+* L} {s : Subfield K} {y : L} : y in s.map f ↔ exists x 
in s, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_map {f : K →+* L} {s : Subfield K} {y : L} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y := by
  unfold map
  simp only [mem_mk, Subring.mem_map, mem_toSubring]

-- Higher priority to apply before `mem_map`.
@[simp 1100]
/-
**Subfield.map_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_mem_map (f : K ->+* L) {s : Subfield K} {x : K} : f x in s.map f ↔ x i
n s
参数：f : K ->+* L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_mem_map (f : K →+* L) {s : Subfield K} {x : K} : f x ∈ s.map f ↔ x ∈ s :=
  calc
    _ ↔ f x ∈ (s.map f : Set L) := Iff.rfl
    _ ↔ _ := by simp [Function.Injective.mem_set_image (f := f) f.injective]
/-
**Subfield.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_map (g : L ->+* M) (f : K ->+* L) : (s.map f).map g = s.map (g.comp f)
参数：g : L ->+* M；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) :=
  SetLike.ext' <| Set.image_image _ _ _
/-
**Subfield.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_le_iff_le_comap {f : K ->+* L} {s : Subfield K} {t : Subfield L} : s.m
ap f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : K →+* L} {s : Subfield K} {t : Subfield L} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**Subfield.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：gc_map_comap (f : K ->+* L) : GaloisConnection (map f) (comap f)
参数：f : K ->+* L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.map_le_iff_le_comap`：map_le_iff_le_comap {f : K ->+* L} {s : Su
bfield K} {t : Subfield L} : s.map f <= t ↔ s <= t.comap f
-/
theorem gc_map_comap (f : K →+* L) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

end Subfield

namespace RingHom

variable (g : L →+* M) (f : K →+* L)

/-! ### range -/


/-- The range of a ring homomorphism, as a subfield of the target. See Note [range copy pattern]. -/
/-
**RingHom.fieldRange** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：fieldRange : Subfield L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a ring homomorphism, as a subfield of the target. See Note [range c
opy pattern].
-/
def fieldRange : Subfield L :=
  ((⊤ : Subfield K).map f).copy (Set.range f) Set.image_univ.symm

@[simp, norm_cast]
/-
**RingHom.coe_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_fieldRange : (f.fieldRange : Set L) = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fieldRange : (f.fieldRange : Set L) = Set.range f :=
  rfl

@[simp]
/-
**RingHom.mem_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_fieldRange {f : K ->+* L} {y : L} : y in f.fieldRange ↔ exists x, f x 
= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fieldRange {f : K →+* L} {y : L} : y ∈ f.fieldRange ↔ ∃ x, f x = y :=
  Iff.rfl
/-
**RingHom.fieldRange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.ext`：ext {S T : Subfield K} (h : forall x, x in S ↔ x in T) : S
 = T
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
theorem fieldRange_eq_map : f.fieldRange = Subfield.map f ⊤ := by
  ext
  simp
/-
**RingHom.map_fieldRange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `Subfield.map_map`：map_map (g : L ->+* M) (f : K ->+* L) : (s.map f).map 
g = s.map (g.comp f)
-/
theorem map_fieldRange : f.fieldRange.map g = (g.comp f).fieldRange := by
  simpa only [fieldRange_eq_map] using (⊤ : Subfield K).map_map g f
/-
**RingHom.mem_fieldRange_self** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_fieldRange_self (x : K) : f x in f.fieldRange
参数：x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_apply_eq_apply`：∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' :
 α), ∃ a, f a = f a'
-/
theorem mem_fieldRange_self (x : K) : f x ∈ f.fieldRange :=
  exists_apply_eq_apply _ _
/-
**RingHom.fieldRange_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：fieldRange_eq_top_iff {f : K ->+* L} : f.fieldRange = ⊤ ↔ Function.Surject
ive f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

/-- The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.Fintype` if `L` is also a fintype. -/
/-
**RingHom.fintypeFieldRange** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
形式化陈述：fintypeFieldRange [Fintype K] [DecidableEq L] (f : K ->+* L) : Fintype f.f
ieldRange
参数：f : K ->+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of fields is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `Subtype.Fintype` if `L` is als
o a fintype.
-/
instance fintypeFieldRange [Fintype K] [DecidableEq L] (f : K →+* L) : Fintype f.fieldRange :=
  Set.fintypeRange f

end RingHom

namespace Subfield

/-! ### inf -/


/-- The inf of two subfields is their intersection. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two subfields is their intersection.
-/
instance : Min (Subfield K) :=
  ⟨fun s t =>
    { s.toSubring ⊓ t.toSubring with
      inv_mem' := fun _ hx =>
        Subring.mem_inf.mpr
          ⟨s.inv_mem (Subring.mem_inf.mp hx).1, t.inv_mem (Subring.mem_inf.mp hx).2⟩ }⟩

@[simp, norm_cast]
/-
**Subfield.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier 
inter p'.carrier
参数：p p' : Subfield K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : Subfield K) : ((p ⊓ p' : Subfield K) : Set K) = p.carrier ∩ p'.carrier :=
  rfl

@[simp]
/-
**Subfield.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_inf {p p' : Subfield K} {x : K} : x in p ⊓ p' ↔ x in p ∧ x in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : Subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Subfield K) :=
  ⟨fun S =>
    { sInf (Subfield.toSubring '' S) with
      inv_mem' := by
        rintro x hx
        apply Subring.mem_sInf.mpr
        rintro _ ⟨p, p_mem, rfl⟩
        exact p.inv_mem (Subring.mem_sInf.mp hx p.toSubring ⟨p, p_mem, rfl⟩) }⟩

@[simp, norm_cast]
/-
**Subfield.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s in
 S, ↑s
参数：S : Set (Subfield K)。
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield K) : Set K) = ⋂ s ∈ S, ↑s :=
  show ((sInf (Subfield.toSubring '' S) : Subring K) : Set K) = ⋂ s ∈ S, ↑s by simp

@[simp]
/-
**Subfield.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_sInf {S : Set (Subfield K)} {x : K} : x in sInf S ↔ forall p in S, x i
n p
参数：Subfield K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Subfield.coe_sInf`：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield
 K) : Set K) = ⋂ s in S, ↑s
-/
theorem mem_sInf {S : Set (Subfield K)} {x : K} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp, norm_cast]
/-
**Subfield.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, 
S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.coe_sInf`：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield
 K) : Set K) = ⋂ s in S, ↑s
· 使用定理 `Set.biInter_range`：biInter_range {f : ι -> α} {g : α -> Set β} : ⋂ x in 
range f, g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/-
**Subfield.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Subfield K} {x : K} : x in ⨅ i, S i ↔ foral
l i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → Subfield K} {x : K} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/-
**Subfield.sInf_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：sInf_toSubring (s : Set (Subfield K)) : (sInf s).toSubring = ⨅ t in s, Sub
field.toSubring t
参数：s : Set (Subfield K)。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sInf_toSubring (s : Set (Subfield K)) :
    (sInf s).toSubring = ⨅ t ∈ s, Subfield.toSubring t := by
  ext x
  simp [mem_sInf]
/-
**Subfield.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S)
参数：S : Set (Subfield K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsGLB.of_image`：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (h
f : forall {x y}, f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) 
(f x…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.coe_sInf`：coe_sInf (S : Set (Subfield K)) : ((sInf S : Subfield
 K) : Set K) = ⋂ s in S, ↑s
· 使用定理 `isGLB_biInf`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{s : Set β} {f : β → α}, IsGLB (f '' s) (⨅ x ∈ s, f x)
-/
theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : ∀ {s t : Subfield K}, (s : Set K) ≤ t ↔ s ≤ t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert! isGLB_biInf (s := S) (f := SetLike.coe)
  exact coe_sInf _

/-- Subfields of a ring form a complete lattice. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subfields of a ring form a complete lattice.
-/
instance : CompleteLattice (Subfield K) :=
  { completeLatticeOfInf (Subfield K) isGLB_sInf with
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }

/-! ### subfield closure of a subset -/

/-- The `Subfield` generated by a set. -/
/-
**Subfield.closure** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：closure (s : Set K) : Subfield K
参数：s : Set K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Subfield` generated by a set.
-/
def closure (s : Set K) : Subfield K := sInf {S | s ⊆ S}
/-
**Subfield.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_closure {x : K} {s : Set K} : x in closure s ↔ forall S : Subfield K, 
s subseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.mem_sInf`：mem_sInf {S : Set (Subfield K)} {x : K} : x in sInf S
 ↔ forall p in S, x in p
-/
theorem mem_closure {x : K} {s : Set K} : x ∈ closure s ↔ ∀ S : Subfield K, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The subfield generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**Subfield.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：subset_closure {s : Set K} : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.mem_closure`：mem_closure {x : K} {s : Set K} : x in closure s ↔
 forall S : Subfield K, s subseteq S -> x in S

--- 原说明 ---
The subfield generated by a set includes the set.
-/
theorem subset_closure {s : Set K} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**Subfield.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_closure_of_mem {s : Set K} {x : K} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem mem_closure_of_mem {s : Set K} {x : K} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**Subfield.subring_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：subring_closure_le (s : Set K) : Subring.closure s <= (closure s).toSubrin
g
参数：s : Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem subring_closure_le (s : Set K) : Subring.closure s ≤ (closure s).toSubring :=
  Subring.closure_le.mpr subset_closure
/-
**Subfield.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：notMem_of_notMem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem notMem_of_notMem_closure {s : Set K} {P : K} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp]
/-
**Subfield.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_le {s : Set K} {t : Subfield K} : closure s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subfield.mem_closure`：mem_closure {x : K} {s : Set K} : x in closure s ↔
 forall S : Subfield K, s subseteq S -> x in S

--- 原说明 ---
A subfield `t` includes `closure s` if and only if it includes `s`.
-/
theorem closure_le {s : Set K} {t : Subfield K} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h _ hx => mem_closure.mp hx t h⟩

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/-
**Subfield.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_mono ⦃s t : Set K⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s

--- 原说明 ---
Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`.
-/
theorem closure_mono ⦃s t : Set K⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
/-
**Subfield.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s subseteq t) (h₂ : t 
<= closure s) : closure s = t
参数：h₁ : s subseteq t；h₂ : t <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
-/
theorem closure_eq_of_le {s : Set K} {t : Subfield K} (h₁ : s ⊆ t) (h₂ : t ≤ closure s) :
    closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all
elements of the closure of `s`. -/
@[elab_as_elim]
/-
**Subfield.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_induction {s : Set K} {p : forall x in closure s, Prop} (mem : for
all x hx, p x (subset_closure hx)) (one : p 1 (one_mem _)) (add : forall x y hx 
hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (neg : forall x hx, p x hx ->
 p (-x) (neg_mem hx)) (inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx)) (mul : f
orall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (h : x in cl
osure s) : p x h
参数：mem : forall x hx, p x (subset_closure hx)；one : p 1 (one_mem _)；add : forall
 x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；neg : forall x hx, p x
 hx -> p (-x) (neg_mem hx)；inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx)；mul :
 forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；h : x in closur
e s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubfieldClass.toInvMemClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Div
isionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   InvMemClass S 
K
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `1`, and all ele
ments
of `s`, and is preserved under addition, negation, and multiplication, then `p` 
holds for all
elements of the closure of `s`.
-/
theorem closure_induction {s : Set K} {p : ∀ x ∈ closure s, Prop}
    (mem : ∀ x hx, p x (subset_closure hx))
    (one : p 1 (one_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx)) (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ closure s) : p x h :=
  letI : Subfield K :=
    { carrier := {x | ∃ hx, p x hx}
      mul_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, mul _ _ _ _ hx hy⟩
      one_mem' := ⟨_, one⟩
      add_mem' := by rintro _ _ ⟨_, hx⟩ ⟨_, hy⟩; exact ⟨_, add _ _ _ _ hx hy⟩
      zero_mem' := ⟨zero_mem _, by
        simp_rw [← @add_neg_cancel K _ 1]; exact add _ _ _ _ one (neg _ _ one)⟩
      neg_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, neg _ _ hx⟩
      inv_mem' := by rintro _ ⟨_, hx⟩; exact ⟨_, inv _ _ hx⟩ }
  ((closure_le (t := this)).2 (fun x hx ↦ ⟨_, mem x hx⟩) h).2

variable (K) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**Subfield.gi** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：(K : Type u) → [inst : DivisionRing K] → GaloisInsertion Subfield.closure 
SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure K _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

/-- Closure of a subfield `S` equals `S`. -/
@[simp]
/-
**Subfield.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_eq (s : Subfield K) : closure (s : Set K) = s
参数：s : Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a subfield `S` equals `S`.
-/
theorem closure_eq (s : Subfield K) : closure (s : Set K) = s :=
  (Subfield.gi K).l_u_eq s

@[simp]
/-
**Subfield.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_empty : closure (∅ : Set K) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_empty : closure (∅ : Set K) = ⊥ :=
  (Subfield.gi K).gc.l_bot

@[simp]
/-
**Subfield.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_univ : closure (Set.univ : Set K) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.closure_eq`：closure_eq (s : Subfield K) : closure (s : Set K) =
 s
· 使用定理 `Subfield.coe_top`：coe_top : ((⊤ : Subfield K) : Set K) = Set.univ
-/
theorem closure_univ : closure (Set.univ : Set K) = ⊤ :=
  @coe_top K _ ▸ closure_eq ⊤
/-
**Subfield.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_union (s t : Set K) : closure (s union t) = closure s ⊔ closure t
参数：s t : Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_union (s t : Set K) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subfield.gi K).gc.l_sup
/-
**Subfield.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_iUnion {ι} (s : ι -> Set K) : closure (⋃ i, s i) = ⨆ i, closure (s
 i)
参数：s : ι -> Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_iUnion {ι} (s : ι → Set K) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subfield.gi K).gc.l_iSup
/-
**Subfield.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t in s, closure t
参数：s : Set (Set K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_sUnion (s : Set (Set K)) : closure (⋃₀ s) = ⨆ t ∈ s, closure t :=
  (Subfield.gi K).gc.l_sSup
/-
**Subfield.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_sup (s t : Subfield K) (f : K ->+* L) : (s ⊔ t).map f = s.map f ⊔ t.ma
p f
参数：s t : Subfield K；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem map_sup (s t : Subfield K) (f : K →+* L) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup
/-
**Subfield.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_iSup {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield K) : (iSup s).map f
 = ⨆ i, (s i).map f
参数：f : K ->+* L；s : ι -> Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : K →+* L) (s : ι → Subfield K) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**Subfield.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_inf (s t : Subfield K) (f : K ->+* L) : (s ⊓ t).map f = s.map f ⊓ t.ma
p f
参数：s t : Subfield K；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem map_inf (s t : Subfield K) (f : K →+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f :=
  SetLike.coe_injective (Set.image_inter f.injective)
/-
**Subfield.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : K ->+* L) (s : ι -> Subfield K) : (
iInf s).map f = ⨅ i, (s i).map f
参数：f : K ->+* L；s : ι -> Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subfield K} : (↑(⨅ i, 
S i) : Set K) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : K →+* L) (s : ι → Subfield K) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**Subfield.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：comap_inf (s t : Subfield L) (f : K ->+* L) : (s ⊓ t).comap f = s.comap f 
⊓ t.comap f
参数：s t : Subfield L；f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem comap_inf (s t : Subfield L) (f : K →+* L) : (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf
/-
**Subfield.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：comap_iInf {ι : Sort*} (f : K ->+* L) (s : ι -> Subfield L) : (iInf s).com
ap f = ⨅ i, (s i).comap f
参数：f : K ->+* L；s : ι -> Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : K →+* L) (s : ι → Subfield L) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**Subfield.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_bot (f : K ->+* L) : (⊥ : Subfield K).map f = ⊥
参数：f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem map_bot (f : K →+* L) : (⊥ : Subfield K).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**Subfield.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：comap_top (f : K ->+* L) : (⊤ : Subfield L).comap f = ⊤
参数：f : K ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
-/
theorem comap_top (f : K →+* L) : (⊤ : Subfield L).comap f = ⊤ :=
  (gc_map_comap f).u_top

/-- The underlying set of a non-empty directed sSup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
/-
**Subfield.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Dir
ected (· <= ·) S) {x : K} : (x in ⨆ i, S i) ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι : Nonempty ι]
 {S : ι -> Subring R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subring R) : Set
 R) = ⋃ i, S i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.inv_mem`：∀ {K : Type u} [inst : DivisionRing K] (s : Subfield K
) {x : K}, x ∈ s → x⁻¹ ∈ s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t

--- 原说明 ---
The underlying set of a non-empty directed sSup of subfields is just a union of 
the subfields.
  Note that this fails without the directedness assumption (the union of two sub
fields is
  typically not a subfield)
-/
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S)
    {x : K} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  let s : Subfield K :=
    { __ := Subring.copy _ _ (Subring.coe_iSup_of_directed hS).symm
      inv_mem' := fun _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).inv_mem hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set K)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  exact this ▸ Set.mem_iUnion
/-
**Subfield.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> Subfield K} (hS : Dir
ected (· <= ·) S) : ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i)
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
· 使用定理 `Subfield.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempty ι
] {S : ι -> Subfield K} (hS : Directed (· <= ·) S) {x : K} : (x in ⨆ i, S i) ↔ e
xists i, x in S i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → Subfield K} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subfield K) : Set K) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_iSup_of_directed hS]
/-
**Subfield.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : Dir
ectedOn (· <= ·) S) {x : K} : x in sSup S ↔ exists s in S, x in s
参数：Subfield K；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
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
· 使用定理 `Subfield.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι : Nonempty ι
] {S : ι -> Subfield K} (hS : Directed (· <= ·) S) {x : K} : (x in ⨆ i, S i) ↔ e
xists i, x in S i
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : DirectedOn (· ≤ ·) S)
    {x : K} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]
/-
**Subfield.coe_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty) (hS : Dir
ectedOn (· <= ·) S) : (↑(sSup S) : Set K) = ⋃ s in S, ↑s
参数：Subfield K；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.mem_sSup_of_directedOn`：mem_sSup_of_directedOn {S : Set (Subfie
ld K)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S) {x : K} : x in sSup S ↔ e
xists s in S, x in s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sSup_of_directedOn {S : Set (Subfield K)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set K) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]

end Subfield

variable (L) in
/-- A field is finitely generated if it is the closure of a finite subset. -/
@[mk_iff fg_iff]
/-
**Field.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `Field`。
形式化陈述：(L : Type v) → [DivisionRing L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A field is finitely generated if it is the closure of a finite subset.
-/
protected class Field.FG : Prop where
  finitely_generated : ∃ S : Finset L, Subfield.closure (S : Set L) = ⊤

namespace RingHom

variable {s : Subfield K}

open Subfield

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
/-
**RingHom.rangeRestrictField** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：rangeRestrictField (f : K ->+* L) : K ->+* f.fieldRange
参数：f : K ->+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of a ring homomorphism to its range interpreted as a subfield.
-/
def rangeRestrictField (f : K →+* L) : K →+* f.fieldRange :=
  f.rangeSRestrict

@[simp]
/-
**RingHom.coe_rangeRestrictField** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：coe_rangeRestrictField (f : K ->+* L) (x : K) : (f.rangeRestrictField x : 
L) = f x
参数：f : K ->+* L；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rangeRestrictField (f : K →+* L) (x : K) : (f.rangeRestrictField x : L) = f x :=
  rfl
/-
**RingHom.rangeRestrictField_bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：rangeRestrictField_bijective (f : K ->+* L) : Function.Bijective (rangeRes
trictField f)
参数：f : K ->+* L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem rangeRestrictField_bijective (f : K →+* L) : Function.Bijective (rangeRestrictField f) :=
  (Equiv.ofInjective f f.injective).bijective

/--
`RingHom.rangeRestrictField` as a `RingEquiv`.
-/
@[simps! apply_coe]
/-
**RingHom.rangeRestrictFieldEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：rangeRestrictFieldEquiv (f : K ->+* L) : K ≃+* f.fieldRange
参数：f : K ->+* L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.rangeRestrictField_bijective`：rangeRestrictField_bijective (f : 
K ->+* L) : Function.Bijective (rangeRestrictField f)

--- 原说明 ---
`RingHom.rangeRestrictField` as a `RingEquiv`.
-/
noncomputable def rangeRestrictFieldEquiv (f : K →+* L) : K ≃+* f.fieldRange :=
  RingEquiv.ofBijective f.rangeRestrictField f.rangeRestrictField_bijective

@[simp]
/-
**RingHom.rangeRestrictFieldEquiv_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ri
ngHom`。
形式化陈述：rangeRestrictFieldEquiv_apply_symm_apply (f : K ->+* L) (x : f.fieldRange)
 : f (f.rangeRestrictFieldEquiv.symm x) = x
参数：f : K ->+* L；x : f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.rangeRestrictFieldEquiv_apply_coe`：∀ {K : Type u} {L : Type v} [
inst : DivisionRing K] [inst_1 : DivisionRing L] (f : K →+* L) (a : K),   ↑(f.ra
ngeRestrictFieldEquiv a) = f a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
-/
theorem rangeRestrictFieldEquiv_apply_symm_apply (f : K →+* L) (x : f.fieldRange) :
    f (f.rangeRestrictFieldEquiv.symm x) = x := by
  rw [← rangeRestrictFieldEquiv_apply_coe, RingEquiv.apply_symm_apply]

section eqLocus

variable {L : Type v} [Semiring L]

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
/-
**RingHom.eqLocusField** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：eqLocusField (f g : K ->+* L) : Subfield K where __
参数：f g : K ->+* L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R
-/
def eqLocusField (f g : K →+* L) : Subfield K where
  __ := (f : K →+* L).eqLocus g
  inv_mem' _ := eq_on_inv₀ f g
  carrier := { x | f x = g x }

@[simp]
/-
**RingHom.mem_eqLocusField** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：mem_eqLocusField {f g : K ->+* L} {x : K} : x in f.eqLocusField g ↔ f x = 
g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocusField {f g : K →+* L} {x : K} : x ∈ f.eqLocusField g ↔ f x = g x := Iff.rfl

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
/-
**RingHom.eqOn_field_closure** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eqOn_field_closure {f g : K ->+* L} {s : Set K} (h : Set.EqOn f g s) : Set
.EqOn f g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t

--- 原说明 ---
If two ring homomorphisms are equal on a set, then they are equal on its subfiel
d closure.
-/
theorem eqOn_field_closure {f g : K →+* L} {s : Set K} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocusField g from closure_le.2 h
/-
**RingHom.eq_of_eqOn_subfield_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：eq_of_eqOn_subfield_top {f g : K ->+* L} (h : Set.EqOn f g (⊤ : Subfield K
)) : f = g
参数：h : Set.EqOn f g (⊤ : Subfield K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_subfield_top {f g : K →+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g :=
  ext fun _ => h trivial
/-
**RingHom.eq_of_eqOn_of_field_closure_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`
。
形式化陈述：eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g :
 K ->+* L} (h : s.EqOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.eq_of_eqOn_subfield_top`：eq_of_eqOn_subfield_top {f g : K ->+* L
} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g
· 使用定理 `RingHom.eqOn_field_closure`：eqOn_field_closure {f g : K ->+* L} {s : Set
 K} (h : Set.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_subfield_top <| hs ▸ eqOn_field_closure h

end eqLocus

/-
**RingHom.field_closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：field_closure_preimage_le (f : K ->+* L) (s : Set L) : closure (f ⁻¹' s) <
= (closure s).comap f
参数：f : K ->+* L；s : Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subfield.mem_comap`：mem_comap {s : Subfield L} {f : K ->+* L} {x : K} : 
x in s.comap f ↔ f x in s
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem field_closure_preimage_le (f : K →+* L) (s : Set L) :
    closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
/-
**RingHom.map_field_closure** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_field_closure (f : K ->+* L) (s : Set K) : (closure s).map f = closure
 (f '' s)
参数：f : K ->+* L；s : Set K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `Subfield.gc_map_comap`：gc_map_comap (f : K ->+* L) : GaloisConnection (m
ap f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set.
-/
theorem map_field_closure (f : K →+* L) (s : Set K) : (closure s).map f = closure (f '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (Subfield.gi L).gc (Subfield.gi K).gc
    fun _ ↦ rfl

end RingHom

namespace Subfield

open RingHom

/-- The ring homomorphism associated to an inclusion of subfields. -/
/-
**Subfield.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：inclusion {S T : Subfield K} (h : S <= T) : S ->+* T
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism associated to an inclusion of subfields.
-/
def inclusion {S T : Subfield K} (h : S ≤ T) : S →+* T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/-
**Subfield.fieldRange_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s
参数：s : Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.coe_rangeS`：∀ {R : Type u} {S : Type v} [inst : NonAssocSemiring
 R] [inst_1 : NonAssocSemiring S] (f : R →+* S),   ↑f.rangeS = Set.range ⇑f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem fieldRange_subtype (s : Subfield K) : s.subtype.fieldRange = s :=
  SetLike.ext' <| (coe_rangeS _).trans Subtype.range_coe

end Subfield

namespace RingEquiv

variable {s t : Subfield K}

/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
/-
**RingEquiv.subfieldCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：subfieldCongr (h : s = t) : s ≃+* t
参数：h : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal.
-/
def subfieldCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| SetLike.ext'_iff.1 h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

end RingEquiv

namespace Subfield

variable {s : Set K}

/-
**Subfield.closure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：closure_preimage_le (f : K ->+* L) (s : Set L) : closure (f ⁻¹' s) <= (clo
sure s).comap f
参数：f : K ->+* L；s : Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subfield.closure_le`：closure_le {s : Set K} {t : Subfield K} : closure s
 <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subfield.mem_comap`：mem_comap {s : Subfield L} {f : K ->+* L} {x : K} : 
x in s.comap f ↔ f x in s
· 使用定理 `Subfield.subset_closure`：subset_closure {s : Set K} : s subseteq closure
 s
-/
theorem closure_preimage_le (f : K →+* L) (s : Set L) : closure (f ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

section Commutative

variable {K : Type u} [Field K] (s : Subfield K)

/-- Product of a multiset of elements in a subfield is in the subfield. -/
/-
**Subfield.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : Field K] (s : Subfield K) (m : Multiset K), (∀ a ∈ 
m, a ∈ s) → m.prod ∈ s
参数：s : Subfield K；m : Multiset K；∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Product of a multiset of elements in a subfield is in the subfield.
-/
protected theorem multiset_prod_mem (m : Multiset K) : (∀ a ∈ m, a ∈ s) → m.prod ∈ s :=
  multiset_prod_mem m

/-- Product of elements of a subfield indexed by a `Finset` is in the subfield. -/
/-
**Subfield.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：∀ {K : Type u} [inst : Field K] (s : Subfield K) {ι : Type u_1} {t : Finse
t ι} {f : ι → K},   (∀ c ∈ t, f c ∈ s) → ∏ i ∈ t, f i ∈ s
参数：s : Subfield K；∀ c ∈ t, f c ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `SubfieldClass.toSubgroupClass`：∀ {K : Type u} [inst : DivisionRing K] (S
 : Type u_1) [inst_1 : SetLike S K] [h : SubfieldClass S K], SubgroupClass S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
Product of elements of a subfield indexed by a `Finset` is in the subfield.
-/
protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → K} (h : ∀ c ∈ t, f c ∈ s) :
    (∏ i ∈ t, f i) ∈ s :=
  prod_mem h
/-
**Subfield.toAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：toAlgebra : Algebra s K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toAlgebra : Algebra s K :=
  inferInstance
/-
**Subfield.algebraMap_ofSubfield** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：algebraMap_ofSubfield : algebraMap s K = s.subtype
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem algebraMap_ofSubfield : algebraMap s K = s.subtype :=
  rfl

/-- The `Subfield` generated by a set in a field. -/
/-
**Subfield.commClosure** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Subfield` generated by a set in a field.
-/
private def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ x ∈ Subring.closure s, ∃ y ∈ Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩
/-
**Subfield.commClosure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem commClosure_eq_closure {s : Set K} : commClosure s = closure s :=
  le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ ↦ eq ▸ div_mem (subring_closure_le s hy) (subring_closure_le s hz))
    (closure_le.mpr fun x hx ↦ ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)
/-
**Subfield.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：mem_closure_iff {s : Set K} {x} : x in closure s ↔ exists y in Subring.clo
sure s, exists z in Subring.closure s, y / z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Field.Subfield.Basic.0.Subfield.commClosure_eq_
closure`：∀ {K : Type u} [inst : Field K] {s : Set K}, Subfield.commClosure✝ s = 
Subfield.closure s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closure_iff {s : Set K} {x} :
    x ∈ closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl

end Commutative

end Subfield

namespace Subfield

/-
**Subfield.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_comap_eq (f : K ->+* L) (s : Subfield L) : (s.comap f).map f = s ⊓ f.f
ieldRange
参数：f : K ->+* L；s : Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : K →+* L) (s : Subfield L) : (s.comap f).map f = s ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range
/-
**Subfield.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_comap_eq_self {f : K ->+* L} {s : Subfield L} (h : s <= f.fieldRange) 
: (s.comap f).map f = s
参数：h : s <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subfield.map_comap_eq`：map_comap_eq (f : K ->+* L) (s : Subfield L) : (s
.comap f).map f = s ⊓ f.fieldRange
-/
theorem map_comap_eq_self
    {f : K →+* L} {s : Subfield L} (h : s ≤ f.fieldRange) : (s.comap f).map f = s := by
  simpa only [inf_of_le_left h] using map_comap_eq f s
/-
**Subfield.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：map_comap_eq_self_of_surjective {f : K ->+* L} (hf : Function.Surjective f
) (s : Subfield L) : (s.comap f).map f = s
参数：hf : Function.Surjective f；s : Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
theorem map_comap_eq_self_of_surjective
    {f : K →+* L} (hf : Function.Surjective f) (s : Subfield L) : (s.comap f).map f = s :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)
/-
**Subfield.comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：comap_map (f : K ->+* L) (s : Subfield K) : (s.map f).comap f = s
参数：f : K ->+* L；s : Subfield K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem comap_map (f : K →+* L) (s : Subfield K) : (s.map f).comap f = s :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end Subfield

/-! ### Actions by `Subfield`s

These are just copies of the definitions about `Subsemiring` starting from
`Subsemiring.MulAction`.
-/
section Actions

namespace Subfield

variable {X Y}

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [SMul K X] (F : Subfield K) : SMul F X :=
  inferInstanceAs (SMul F.toSubsemiring X)
/-
**Subfield.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：smul_def [SMul K X] {F : Subfield K} (g : F) (m : X) : g • m = (g : K) • m
参数：g : F；m : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [SMul K X] {F : Subfield K} (g : F) (m : X) : g • m = (g : K) • m :=
  rfl
/-
**Subfield.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：smulCommClass_left [SMul K Y] [SMul X Y] [SMulCommClass K X Y] (F : Subfie
ld K) : SMulCommClass F X Y
参数：F : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_left [SMul K Y] [SMul X Y] [SMulCommClass K X Y] (F : Subfield K) :
    SMulCommClass F X Y :=
  inferInstanceAs (SMulCommClass F.toSubsemiring X Y)
/-
**Subfield.smulCommClass_right** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
形式化陈述：smulCommClass_right [SMul X Y] [SMul K Y] [SMulCommClass X K Y] (F : Subfi
eld K) : SMulCommClass X F Y
参数：F : Subfield K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass_right [SMul X Y] [SMul K Y] [SMulCommClass X K Y] (F : Subfield K) :
    SMulCommClass X F Y :=
  inferInstanceAs (SMulCommClass X F.toSubsemiring Y)

/-- Note that this provides `IsScalarTower F K K` which is needed by `smul_mul_assoc`. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides `IsScalarTower F K K` which is needed by `smul_mul_assoc
`.
-/
instance [SMul X Y] [SMul K X] [SMul K Y] [IsScalarTower K X Y] (F : Subfield K) :
    IsScalarTower F X Y :=
  inferInstanceAs (IsScalarTower F.toSubsemiring X Y)
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul K X] [FaithfulSMul K X] (F : Subfield K) : FaithfulSMul F X :=
  inferInstanceAs (FaithfulSMul F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [MulAction K X] (F : Subfield K) : MulAction F X :=
  inferInstanceAs (MulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [AddMonoid X] [DistribMulAction K X] (F : Subfield K) : DistribMulAction F X :=
  inferInstanceAs (DistribMulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [Monoid X] [MulDistribMulAction K X] (F : Subfield K) : MulDistribMulAction F X :=
  inferInstanceAs (MulDistribMulAction F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [Zero X] [SMulWithZero K X] (F : Subfield K) : SMulWithZero F X :=
  inferInstanceAs (SMulWithZero F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [Zero X] [MulActionWithZero K X] (F : Subfield K) : MulActionWithZero F X :=
  inferInstanceAs (MulActionWithZero F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [AddCommMonoid X] [Module K X] (F : Subfield K) : Module F X :=
  inferInstanceAs (Module F.toSubsemiring X)

/-- The action by a subfield is the action by the underlying field. -/
/-
**Subfield.** 是 Mathlib 中的一个实例，位于命名空间 `Subfield`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a subfield is the action by the underlying field.
-/
instance [Semiring X] [MulSemiringAction K X] (F : Subfield K) : MulSemiringAction F X :=
  inferInstanceAs (MulSemiringAction F.toSubsemiring X)

end Subfield

end Actions

