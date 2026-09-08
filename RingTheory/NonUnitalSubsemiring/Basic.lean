/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Subsemigroup.Membership
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.GroupWithZero.Center
public import Mathlib.Algebra.Ring.Center
public import Mathlib.Algebra.Ring.Centralizer
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Submonoid.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.GroupTheory.Subsemigroup.Centralizer
public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs

/-!
# Bundled non-unital subsemirings

We define the `CompleteLattice` structure, and non-unital subsemiring
`map`, `comap` and range (`srange`) of a `NonUnitalRingHom` etc.
-/

@[expose] public section


universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonUnitalNonAssocSemiring R] (M : Subsemigroup R)

namespace NonUnitalSubsemiring

@[gcongr, mono]
/-
**NonUnitalSubsemiring.toSubsemigroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubsemiring`。
形式化陈述：toSubsemigroup_strictMono : StrictMono (toSubsemigroup : NonUnitalSubsemir
ing R -> Subsemigroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubsemigroup_strictMono :
    StrictMono (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R) := fun _ _ => id

@[gcongr, mono]
/-
**NonUnitalSubsemiring.toSubsemigroup_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubsemiring R ->
 Subsemigroup R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NonUnitalSubsemiring.toSubsemigroup_strictMono`：toSubsemigroup_strictMon
o : StrictMono (toSubsemigroup : NonUnitalSubsemiring R -> Subsemigroup R)
-/
theorem toSubsemigroup_mono : Monotone (toSubsemigroup : NonUnitalSubsemiring R → Subsemigroup R) :=
  toSubsemigroup_strictMono.monotone

@[gcongr, mono]
/-
**NonUnitalSubsemiring.toAddSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubsemiring`。
形式化陈述：toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : NonUnitalSubsemir
ing R -> AddSubmonoid R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubmonoid_strictMono :
    StrictMono (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R) := fun _ _ => id

@[gcongr, mono]
/-
**NonUnitalSubsemiring.toAddSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：toAddSubmonoid_mono : Monotone (toAddSubmonoid : NonUnitalSubsemiring R ->
 AddSubmonoid R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NonUnitalSubsemiring.toAddSubmonoid_strictMono`：toAddSubmonoid_strictMon
o : StrictMono (toAddSubmonoid : NonUnitalSubsemiring R -> AddSubmonoid R)
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : NonUnitalSubsemiring R → AddSubmonoid R) :=
  toAddSubmonoid_strictMono.monotone

end NonUnitalSubsemiring

namespace NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
variable {F G : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
  [FunLike G S T] [NonUnitalRingHomClass G S T]
  (s : NonUnitalSubsemiring R)

/-- The ring equiv between the top element of `NonUnitalSubsemiring R` and `R`. -/
@[simps!]
/-
**NonUnitalSubsemiring.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：topEquiv : (⊤ : NonUnitalSubsemiring R) ≃+* R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
The ring equiv between the top element of `NonUnitalSubsemiring R` and `R`.
-/
def topEquiv : (⊤ : NonUnitalSubsemiring R) ≃+* R :=
  { Subsemigroup.topEquiv, AddSubmonoid.topEquiv with }

/-- The preimage of a non-unital subsemiring along a non-unital ring homomorphism is a
non-unital subsemiring. -/
/-
**NonUnitalSubsemiring.comap** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：comap (f : F) (s : NonUnitalSubsemiring S) : NonUnitalSubsemiring R
参数：f : F；s : NonUnitalSubsemiring S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…

--- 原说明 ---
The preimage of a non-unital subsemiring along a non-unital ring homomorphism is
 a
non-unital subsemiring.
-/
def comap (f : F) (s : NonUnitalSubsemiring S) : NonUnitalSubsemiring R :=
  { s.toSubsemigroup.comap (f : MulHom R S), s.toAddSubmonoid.comap (f : R →+ S) with
    carrier := f ⁻¹' s }

@[simp]
/-
**NonUnitalSubsemiring.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：coe_comap (s : NonUnitalSubsemiring S) (f : F) : (s.comap f : Set R) = f ⁻
¹' s
参数：s : NonUnitalSubsemiring S；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (s : NonUnitalSubsemiring S) (f : F) : (s.comap f : Set R) = f ⁻¹' s :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：mem_comap {s : NonUnitalSubsemiring S} {f : F} {x : R} : x in s.comap f ↔ 
f x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {s : NonUnitalSubsemiring S} {f : F} {x : R} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

-- this has some nasty coercions, how to deal with it?
/-
**NonUnitalSubsemiring.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：comap_comap (s : NonUnitalSubsemiring T) (g : G) (f : F) : ((s.comap g : N
onUnitalSubsemiring S).comap f : NonUnitalSubsemiring R) = s.comap ((g : S ->ₙ+*
 T).comp (f : R ->ₙ+* S))
参数：s : NonUnitalSubsemiring T；g : G；f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (s : NonUnitalSubsemiring T) (g : G) (f : F) :
    ((s.comap g : NonUnitalSubsemiring S).comap f : NonUnitalSubsemiring R) =
      s.comap ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
  rfl

/-- The image of a non-unital subsemiring along a ring homomorphism is a non-unital subsemiring. -/
/-
**NonUnitalSubsemiring.map** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：map (f : F) (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring S
参数：f : F；s : NonUnitalSubsemiring R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…

--- 原说明 ---
The image of a non-unital subsemiring along a ring homomorphism is a non-unital 
subsemiring.
-/
def map (f : F) (s : NonUnitalSubsemiring R) : NonUnitalSubsemiring S :=
  { s.toSubsemigroup.map (f : R →ₙ* S), s.toAddSubmonoid.map (f : R →+ S) with carrier := f '' s }

@[simp]
/-
**NonUnitalSubsemiring.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：coe_map (f : F) (s : NonUnitalSubsemiring R) : (s.map f : Set S) = f '' s
参数：f : F；s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (f : F) (s : NonUnitalSubsemiring R) : (s.map f : Set S) = f '' s :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：mem_map {f : F} {s : NonUnitalSubsemiring R} {y : S} : y in s.map f ↔ exis
ts x in s, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : F} {s : NonUnitalSubsemiring R} {y : S} : y ∈ s.map f ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

@[simp]
/-
**NonUnitalSubsemiring.map_id** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
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

-- unavoidable coercions?
/-
**NonUnitalSubsemiring.map_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：map_map (g : G) (f : F) : (s.map (f : R ->ₙ+* S)).map (g : S ->ₙ+* T) = s.
map ((g : S ->ₙ+* T).comp (f : R ->ₙ+* S))
参数：g : G；f : F。
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
theorem map_map (g : G) (f : F) :
    (s.map (f : R →ₙ+* S)).map (g : S →ₙ+* T) = s.map ((g : S →ₙ+* T).comp (f : R →ₙ+* S)) :=
  SetLike.coe_injective <| Set.image_image _ _ _
/-
**NonUnitalSubsemiring.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：map_le_iff_le_comap {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSub
semiring S} : s.map f <= t ↔ s <= t.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : F} {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  Set.image_subset_iff
/-
**NonUnitalSubsemiring.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemir
ing`。
形式化陈述：gc_map_comap (f : F) : @GaloisConnection (NonUnitalSubsemiring R) (NonUnit
alSubsemiring S) _ _ (map f) (comap f)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.map_le_iff_le_comap`：map_le_iff_le_comap {f : F} {s
 : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} : s.map f <= t ↔ s <= t.
comap f
-/
theorem gc_map_comap (f : F) :
    @GaloisConnection (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

/-- A non-unital subsemiring is isomorphic to its image under an injective function -/
/-
**NonUnitalSubsemiring.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：equivMapOfInjective (f : F) (hf : Function.Injective (f : R -> S)) : s ≃+*
 s.map f
参数：f : F；hf : Function.Injective (f : R -> S)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
A non-unital subsemiring is isomorphic to its image under an injective function
-/
noncomputable def equivMapOfInjective (f : F) (hf : Function.Injective (f : R → S)) :
    s ≃+* s.map f :=
  { Equiv.Set.image f s hf with
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _)
    map_add' := fun _ _ => Subtype.ext (map_add f _ _) }

@[simp]
/-
**NonUnitalSubsemiring.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalSubsemiring`。
形式化陈述：coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) 
: (equivMapOfInjective s f hf x : S) = f x
参数：f : F；hf : Function.Injective f；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem coe_equivMapOfInjective_apply (f : F) (hf : Function.Injective f) (x : s) :
    (equivMapOfInjective s f hf x : S) = f x :=
  rfl

end NonUnitalSubsemiring

namespace NonUnitalRingHom

open NonUnitalSubsemiring

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
variable {F G : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable [FunLike G S T] [NonUnitalRingHomClass G S T] (f : F) (g : G)

/-- The range of a non-unital ring homomorphism is a non-unital subsemiring.
See note [range copy pattern]. -/
/-
**NonUnitalRingHom.srange** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：srange : NonUnitalSubsemiring S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…

--- 原说明 ---
The range of a non-unital ring homomorphism is a non-unital subsemiring.
See note [range copy pattern].
-/
def srange : NonUnitalSubsemiring S :=
  ((⊤ : NonUnitalSubsemiring R).map (f : R →ₙ+* S)).copy (Set.range f) Set.image_univ.symm

@[simp]
/-
**NonUnitalRingHom.coe_srange** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：coe_srange : (srange f : Set S) = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_srange : (srange f : Set S) = Set.range f :=
  rfl

@[simp]
/-
**NonUnitalRingHom.mem_srange** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mem_srange {f : F} {y : S} : y in srange f ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_srange {f : F} {y : S} : y ∈ srange f ↔ ∃ x, f x = y :=
  Iff.rfl
/-
**NonUnitalRingHom.srange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：srange_eq_map : srange f = (⊤ : NonUnitalSubsemiring R).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.ext`：ext {S T : NonUnitalSubsemiring R} (h : forall
 x, x in S ↔ x in T) : S = T
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
theorem srange_eq_map : srange f = (⊤ : NonUnitalSubsemiring R).map f := by
  ext
  simp
/-
**NonUnitalRingHom.mem_srange_self** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：mem_srange_self (f : F) (x : R) : f x in srange f
参数：f : F；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalRingHom.mem_srange`：mem_srange {f : F} {y : S} : y in srange f 
↔ exists x, f x = y
-/
theorem mem_srange_self (f : F) (x : R) : f x ∈ srange f :=
  mem_srange.mpr ⟨x, rfl⟩
/-
**NonUnitalRingHom.map_srange** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：map_srange (g : S ->ₙ+* T) (f : R ->ₙ+* S) : map g (srange f) = srange (g.
comp f)
参数：g : S ->ₙ+* T；f : R ->ₙ+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.map.congr_simp`：∀ {R : Type u} {S : Type v} [inst :
 NonUnitalNonAssocSemiring R] [inst_1 : NonUnitalNonAssocSemiring S] {F : Type u
_1}   [inst_2 : FunLike F…
· 使用定理 `NonUnitalRingHom.srange_eq_map`：srange_eq_map : srange f = (⊤ : NonUnita
lSubsemiring R).map f
· 使用定理 `NonUnitalSubsemiring.map_map`：map_map (g : G) (f : F) : (s.map (f : R ->
ₙ+* S)).map (g : S ->ₙ+* T) = s.map ((g : S ->ₙ+* T).comp (f : R ->ₙ+* S))
-/
theorem map_srange (g : S →ₙ+* T) (f : R →ₙ+* S) : map g (srange f) = srange (g.comp f) := by
  simpa only [srange_eq_map] using! (⊤ : NonUnitalSubsemiring R).map_map g f

/-- The range of a morphism of non-unital semirings is finite if the domain is finite. -/
/-
**NonUnitalRingHom.finite_srange** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalRingHom`。
形式化陈述：finite_srange [Finite R] (f : F) : Finite (srange f : NonUnitalSubsemiring
 S)
参数：f : F。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e

--- 原说明 ---
The range of a morphism of non-unital semirings is finite if the domain is finit
e.
-/
instance finite_srange [Finite R] (f : F) : Finite (srange f : NonUnitalSubsemiring S) :=
  (Set.finite_range f).to_subtype

end NonUnitalRingHom

namespace NonUnitalSubsemiring

/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (NonUnitalSubsemiring R) :=
  ⟨fun s =>
    NonUnitalSubsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, NonUnitalSubsemiring.toSubsemigroup t)
      (by simp) (⨅ t ∈ s, NonUnitalSubsemiring.toAddSubmonoid t) (by simp)⟩

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：coe_sInf (S : Set (NonUnitalSubsemiring R)) : ((sInf S : NonUnitalSubsemir
ing R) : Set R) = ⋂ s in S, ↑s
参数：S : Set (NonUnitalSubsemiring R)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (NonUnitalSubsemiring R)) :
    ((sInf S : NonUnitalSubsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：mem_sInf {S : Set (NonUnitalSubsemiring R)} {x : R} : x in sInf S ↔ forall
 p in S, x in p
参数：NonUnitalSubsemiring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (NonUnitalSubsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} : (↑(⨅ i, S i) : Se
t R) = ⋂ i, S i
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
theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubsemiring R} :
    (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]

@[simp]
/-
**NonUnitalSubsemiring.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> NonUnitalSubsemiring R} {x : R} : x in ⨅ i,
 S i ↔ forall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubsemiring R} {x : R} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp]
/-
**NonUnitalSubsemiring.sInf_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：sInf_toSubsemigroup (s : Set (NonUnitalSubsemiring R)) : (sInf s).toSubsem
igroup = ⨅ t in s, NonUnitalSubsemiring.toSubsemigroup t
参数：s : Set (NonUnitalSubsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mk'_toSubsemigroup`：∀ {R : Type u} [inst : NonUnita
lNonAssocSemiring R] {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s)   {sa : Ad
dSubmonoid R} (ha : ↑sa = s),…
-/
theorem sInf_toSubsemigroup (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toSubsemigroup = ⨅ t ∈ s, NonUnitalSubsemiring.toSubsemigroup t :=
  mk'_toSubsemigroup _ _

@[simp]
/-
**NonUnitalSubsemiring.sInf_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：sInf_toAddSubmonoid (s : Set (NonUnitalSubsemiring R)) : (sInf s).toAddSub
monoid = ⨅ t in s, NonUnitalSubsemiring.toAddSubmonoid t
参数：s : Set (NonUnitalSubsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mk'_toAddSubmonoid`：∀ {R : Type u} [inst : NonUnita
lNonAssocSemiring R] {s : Set R} {sg : Subsemigroup R} (hg : ↑sg = s)   {sa : Ad
dSubmonoid R} (ha : ↑sa = s),…
-/
theorem sInf_toAddSubmonoid (s : Set (NonUnitalSubsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, NonUnitalSubsemiring.toAddSubmonoid t :=
  mk'_toAddSubmonoid _ _

/-- Non-unital subsemirings of a non-unital semiring form a complete lattice. -/
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-unital subsemirings of a non-unital semiring form a complete lattice.
-/
instance : CompleteLattice (NonUnitalSubsemiring R) :=
  { completeLatticeOfInf (NonUnitalSubsemiring R)
      fun _ => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun s _ hx => (mem_bot.mp hx).symm ▸ zero_mem s
    top := ⊤
    le_top := fun _ _ _ => trivial
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right
    le_inf := fun _ _ _ h₁ h₂ _ hx => ⟨h₁ hx, h₂ hx⟩ }
/-
**NonUnitalSubsemiring.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：eq_top_iff' (A : NonUnitalSubsemiring R) : A = ⊤ ↔ forall x : R, x in A
参数：A : NonUnitalSubsemiring R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `NonUnitalSubsemiring.mem_top`：mem_top (x : R) : x in (⊤ : NonUnitalSubse
miring R)
-/
theorem eq_top_iff' (A : NonUnitalSubsemiring R) : A = ⊤ ↔ ∀ x : R, x ∈ A :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩

section NonUnitalNonAssocSemiring

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
/-
**NonUnitalSubsemiring.center** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：center : NonUnitalSubsemiring R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a semiring `R` is the set of elements that commute and associate w
ith everything
in `R`
-/
def center : NonUnitalSubsemiring R :=
  { Subsemigroup.center R with
    zero_mem' := Set.zero_mem_center
    add_mem' := Set.add_mem_center }
/-
**NonUnitalSubsemiring.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemirin
g`。
形式化陈述：coe_center : ↑(center R) = Set.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : ↑(center R) = Set.center R :=
  rfl

@[simp]
/-
**NonUnitalSubsemiring.center_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubsemiring`。
形式化陈述：center_toSubsemigroup : (center R).toSubsemigroup = Subsemigroup.center R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toSubsemigroup :
    (center R).toSubsemigroup = Subsemigroup.center R :=
  rfl

/-- The center is commutative and associative. -/
/-
**NonUnitalSubsemiring.center.instNonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空
间 `NonUnitalSubsemiring.center`。
形式化陈述：(R : Type u) → [inst : NonUnitalNonAssocSemiring R] → NonUnitalCommSemirin
g ↥(NonUnitalSubsemiring.center R)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
The center is commutative and associative.
-/
instance center.instNonUnitalCommSemiring : NonUnitalCommSemiring (center R) :=
  { Subsemigroup.center.commSemigroup,
    NonUnitalSubsemiringClass.toNonUnitalNonAssocSemiring (center R) with }

/-- A point-free means of proving membership in the center, for a non-associative ring.

This can be helpful when working with types that have ext lemmas for `R →+ R`. -/
/-
**NonUnitalSubsemiring._root_.Set.mem_center_iff_addMonoidHom** 是 Mathlib 中的一个引理
，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point-free means of proving membership in the center, for a non-associative ri
ng.

This can be helpful when working with types that have ext lemmas for `R →+ R`.
-/
lemma _root_.Set.mem_center_iff_addMonoidHom (a : R) :
    a ∈ Set.center R ↔
      AddMonoidHom.mulLeft a = .mulRight a ∧
      AddMonoidHom.compr₂ .mul (.mulLeft a) = .comp .mul (.mulLeft a) ∧
      AddMonoidHom.compr₂ .mul (.mulRight a) = .compl₂ .mul (.mulRight a) := by
  rw [Set.mem_center_iff, isMulCentral_iff]
  simp [DFunLike.ext_iff, commute_iff_eq]

variable {R}

/-- The center of isomorphic (not necessarily unital or associative) semirings are isomorphic. -/
/-
**NonUnitalSubsemiring.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : NonUnitalNonAssocSemiring R] →
       [inst_1 : NonUnitalNonAssocSemiring S] →         R ≃+* S → ↥(NonUnitalSub
semiring.center R) ≃+* ↥(NonUnitalSubsemiring.center S)
参数：NonUnitalSubsemiring.center R；NonUnitalSubsemiring.center S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic (not necessarily unital or associative) semirings are i
somorphic.
-/
@[simps!] def centerCongr [NonUnitalNonAssocSemiring S] (e : R ≃+* S) : center R ≃+* center S where
  __ := Subsemigroup.centerCongr e
  map_add' _ _ := Subtype.ext <| by exact map_add e ..

/-- The center of a (not necessarily unital or associative) semiring
is isomorphic to the center of its opposite. -/
/-
**NonUnitalSubsemiring.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：{R : Type u} →   [inst : NonUnitalNonAssocSemiring R] → ↥(NonUnitalSubsemi
ring.center R) ≃+* ↥(NonUnitalSubsemiring.center Rᵐᵒᵖ)
参数：NonUnitalSubsemiring.center R；NonUnitalSubsemiring.center Rᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a (not necessarily unital or associative) semiring
is isomorphic to the center of its opposite.
-/
@[simps!] def centerToMulOpposite : center R ≃+* center Rᵐᵒᵖ where
  __ := Subsemigroup.centerToMulOpposite
  map_add' _ _ := rfl

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

set_option backward.isDefEq.respectTransparency false in
-- no instance diamond, unlike the unital version
/-
**NonUnitalSubsemiring.** 是 Mathlib 中的一个示例，位于命名空间 `NonUnitalSubsemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {R} [NonUnitalSemiring R] :
    (center.instNonUnitalCommSemiring _).toNonUnitalSemiring =
      NonUnitalSubsemiringClass.toNonUnitalSemiring (center R) := by
  with_reducible_and_instances rfl
/-
**NonUnitalSubsemiring.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：mem_center_iff {R} [NonUnitalSemiring R] {z : R} : z in center R ↔ forall 
g, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_center_iff {R} [NonUnitalSemiring R] {z : R} : z ∈ center R ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
/-
**NonUnitalSubsemiring.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：decidableMemCenter {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R] :
 DecidablePred (· in center R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mem_center_iff`：mem_center_iff {R} [NonUnitalSemiri
ng R] {z : R} : z in center R ↔ forall g, g * z = z * g
-/
instance decidableMemCenter {R} [NonUnitalSemiring R] [DecidableEq R] [Fintype R] :
    DecidablePred (· ∈ center R) := fun _ => decidable_of_iff' _ mem_center_iff

@[simp]
/-
**NonUnitalSubsemiring.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemi
ring`。
形式化陈述：center_eq_top (R) [NonUnitalCommSemiring R] : center R = ⊤
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (R) [NonUnitalCommSemiring R] : center R = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ R)

end NonUnitalSemiring

section Centralizer

/-- The centralizer of a set as non-unital subsemiring. -/
/-
**NonUnitalSubsemiring.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：centralizer {R} [NonUnitalSemiring R] (s : Set R) : NonUnitalSubsemiring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a set as non-unital subsemiring.
-/
def centralizer {R} [NonUnitalSemiring R] (s : Set R) : NonUnitalSubsemiring R :=
  { Subsemigroup.centralizer s with
    carrier := s.centralizer
    zero_mem' := Set.zero_mem_centralizer
    add_mem' := Set.add_mem_centralizer }

@[simp, norm_cast]
/-
**NonUnitalSubsemiring.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubse
miring`。
形式化陈述：coe_centralizer {R} [NonUnitalSemiring R] (s : Set R) : (centralizer s : S
et R) = s.centralizer
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s : Set R) = s.centralizer :=
  rfl
/-
**NonUnitalSubsemiring.centralizer_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalSubsemiring`。
形式化陈述：centralizer_toSubsemigroup {R} [NonUnitalSemiring R] (s : Set R) : (centra
lizer s).toSubsemigroup = Subsemigroup.centralizer s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubsemigroup {R} [NonUnitalSemiring R] (s : Set R) :
    (centralizer s).toSubsemigroup = Subsemigroup.centralizer s :=
  rfl
/-
**NonUnitalSubsemiring.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
ubsemiring`。
形式化陈述：mem_centralizer_iff {R} [NonUnitalSemiring R] {s : Set R} {z : R} : z in c
entralizer s ↔ forall g in s, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {R} [NonUnitalSemiring R] {s : Set R} {z : R} :
    z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
  Iff.rfl
/-
**NonUnitalSubsemiring.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubsemiring`。
形式化陈述：center_le_centralizer {R} [NonUnitalSemiring R] (s) : center R <= centrali
zer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer {R} [NonUnitalSemiring R] (s) : center R ≤ centralizer s :=
  s.center_subset_centralizer
/-
**NonUnitalSubsemiring.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：centralizer_le {R} [NonUnitalSemiring R] (s t : Set R) (h : s subseteq t) 
: centralizer t <= centralizer s
参数：s t : Set R；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le {R} [NonUnitalSemiring R] (s t : Set R) (h : s ⊆ t) :
    centralizer t ≤ centralizer s :=
  Set.centralizer_subset h

@[simp]
/-
**NonUnitalSubsemiring.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalSubsemiring`。
形式化陈述：centralizer_eq_top_iff_subset {R} [NonUnitalSemiring R] {s : Set R} : cent
ralizer s = ⊤ ↔ s subseteq center R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {R} [NonUnitalSemiring R] {s : Set R} :
    centralizer s = ⊤ ↔ s ⊆ center R :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[simp]
/-
**NonUnitalSubsemiring.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubs
emiring`。
形式化陈述：centralizer_univ {R} [NonUnitalSemiring R] : centralizer Set.univ = center
 R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ {R} [NonUnitalSemiring R] : centralizer Set.univ = center R :=
  SetLike.ext' (Set.centralizer_univ R)

end Centralizer

/-- The `NonUnitalSubsemiring` generated by a set. -/
/-
**NonUnitalSubsemiring.closure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：closure (s : Set R) : NonUnitalSubsemiring R
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `NonUnitalSubsemiring` generated by a set.
-/
def closure (s : Set R) : NonUnitalSubsemiring R :=
  sInf { S | s ⊆ S }
/-
**NonUnitalSubsemiring.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：mem_closure {x : R} {s : Set R} : x in closure s ↔ forall S : NonUnitalSub
semiring R, s subseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mem_sInf`：mem_sInf {S : Set (NonUnitalSubsemiring R
)} {x : R} : x in sInf S ↔ forall p in S, x in p
-/
theorem mem_closure {x : R} {s : Set R} :
    x ∈ closure s ↔ ∀ S : NonUnitalSubsemiring R, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The non-unital subsemiring generated by a set includes the set. -/
@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**NonUnitalSubsemiring.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：subset_closure {s : Set R} : s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.mem_closure`：mem_closure {x : R} {s : Set R} : x in
 closure s ↔ forall S : NonUnitalSubsemiring R, s subseteq S -> x in S

--- 原说明 ---
The non-unital subsemiring generated by a set includes the set.
-/
theorem subset_closure {s : Set R} : s ⊆ closure s := fun _ hx => mem_closure.2 fun _ hS => hS hx

@[aesop 80% (rule_sets := [SetLike])]
/-
**NonUnitalSubsemiring.mem_closure_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSu
bsemiring`。
形式化陈述：mem_closure_of_mem {s : Set R} {x : R} (hx : x in s) : x in closure s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
-/
theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ closure s := subset_closure hx
/-
**NonUnitalSubsemiring.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italSubsemiring`。
形式化陈述：notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s
参数：hP : P ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
-/
theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

/-- A non-unital subsemiring `S` includes `closure s` if and only if it includes `s`. -/
@[simp]
/-
**NonUnitalSubsemiring.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemirin
g`。
形式化陈述：closure_le {s : Set R} {t : NonUnitalSubsemiring R} : closure s <= t ↔ s s
ubseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a

--- 原说明 ---
A non-unital subsemiring `S` includes `closure s` if and only if it includes `s`
.
-/
theorem closure_le {s : Set R} {t : NonUnitalSubsemiring R} : closure s ≤ t ↔ s ⊆ t :=
  ⟨Set.Subset.trans subset_closure, fun h => sInf_le h⟩

/-- Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[gcongr]
/-
**NonUnitalSubsemiring.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemir
ing`。
形式化陈述：closure_mono ⦃s t : Set R⦄ (h : s subseteq t) : closure s <= closure t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s

--- 原说明 ---
Subsemiring closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`.
-/
theorem closure_mono ⦃s t : Set R⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Set.Subset.trans h subset_closure
/-
**NonUnitalSubsemiring.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubs
emiring`。
形式化陈述：closure_eq_of_le {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s subseteq
 t) (h₂ : t <= closure s) : closure s = t
参数：h₁ : s subseteq t；h₂ : t <= closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
-/
theorem closure_eq_of_le {s : Set R} {t : NonUnitalSubsemiring R} (h₁ : s ⊆ t)
    (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymm (closure_le.2 h₁) h₂
/-
**NonUnitalSubsemiring.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命
名空间 `NonUnitalSubsemiring`。
形式化陈述：closure_le_centralizer_centralizer {R : Type*} [NonUnitalSemiring R] (s : 
Set R) : closure s <= centralizer (centralizer s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer {R : Type*} [NonUnitalSemiring R] (s : Set R) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
semiring. -/
/-
**NonUnitalSubsemiring.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italSubsemiring`。
形式化陈述：isMulCommutative_closure {R : Type*} [NonUnitalSemiring R] {s : Set R} (hc
omm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (closure s
)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalSubsemiring.closure_le_centralizer_centralizer`：closure_le_cent
ralizer_centralizer {R : Type*} [NonUnitalSemiring R] (s : Set R) : closure s <=
 centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a non-unital commu
tative
semiring.
-/
theorem isMulCommutative_closure {R : Type*} [NonUnitalSemiring R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a non-unital commutative
semiring. -/
@[deprecated isMulCommutative_closure (since := "2026-03-11")]
/-
**NonUnitalSubsemiring.closureNonUnitalCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位
于命名空间 `NonUnitalSubsemiring`。
形式化陈述：closureNonUnitalCommSemiringOfComm {R : Type*} [NonUnitalSemiring R] {s : 
Set R} (hcomm : forall x in s, forall y in s, x * y = y * x) : NonUnitalCommSemi
ring (closure s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_closure`：isMulCommutative_closure 
{R : Type*} [NonUnitalSemiring R] {s : Set R} (hcomm : forall x in s, forall y i
n s, x * y = y * x) : IsMulCommutat…

--- 原说明 ---
If all the elements of a set `s` commute, then `closure s` is a non-unital commu
tative
semiring.
-/
abbrev closureNonUnitalCommSemiringOfComm {R : Type*} [NonUnitalSemiring R] {s : Set R}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) : NonUnitalCommSemiring (closure s) :=
  have := isMulCommutative_closure hcomm
  inferInstance
/-
**NonUnitalSubsemiring.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalSubsemiring`。
形式化陈述：instIsMulCommutative_closure {S R : Type*} [NonUnitalSemiring R] [SetLike 
S R] [MulMemClass S R] (s : S) [IsMulCommutative s] : IsMulCommutative (closure 
(s : Set R))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_closure`：isMulCommutative_closure 
{R : Type*} [NonUnitalSemiring R] {s : Set R} (hcomm : forall x in s, forall y i
n s, x * y = y * x) : IsMulCommutat…
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S R : Type*} [NonUnitalSemiring R]
    [SetLike S R] [MulMemClass S R] (s : S) [IsMulCommutative s] :
    IsMulCommutative (closure (s : Set R)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable [NonUnitalNonAssocSemiring S]
/-
**NonUnitalSubsemiring.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemi
ring`。
形式化陈述：mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S} : x in K.
map (f : R ->ₙ+* S) ↔ f.symm x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_map_equiv {f : R ≃+* S} {K : NonUnitalSubsemiring R} {x : S} :
    x ∈ K.map (f : R →ₙ+* S) ↔ f.symm x ∈ K := by
  convert! @Set.mem_image_equiv _ _ (↑K) f.toEquiv x
/-
**NonUnitalSubsemiring.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talSubsemiring`。
形式化陈述：map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubsemiring R) : K.map
 (f : R ->ₙ+* S) = K.comap f.symm
参数：f : R ≃+* S；K : NonUnitalSubsemiring R。
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
theorem map_equiv_eq_comap_symm (f : R ≃+* S) (K : NonUnitalSubsemiring R) :
    K.map (f : R →ₙ+* S) = K.comap f.symm :=
  SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)
/-
**NonUnitalSubsemiring.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talSubsemiring`。
形式化陈述：comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubsemiring S) : K.com
ap (f : R ->ₙ+* S) = K.map f.symm
参数：f : R ≃+* S；K : NonUnitalSubsemiring S。
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
· 使用定理 `NonUnitalSubsemiring.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f
 : R ≃+* S) (K : NonUnitalSubsemiring R) : K.map (f : R ->ₙ+* S) = K.comap f.sym
m
-/
theorem comap_equiv_eq_map_symm (f : R ≃+* S) (K : NonUnitalSubsemiring S) :
    K.comap (f : R →ₙ+* S) = K.map f.symm :=
  (map_equiv_eq_comap_symm f.symm K).symm

end NonUnitalSubsemiring

namespace Subsemigroup

/-- The additive closure of a non-unital subsemigroup is a non-unital subsemiring. -/
/-
**Subsemigroup.nonUnitalSubsemiringClosure** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigro
up`。
形式化陈述：nonUnitalSubsemiringClosure (M : Subsemigroup R) : NonUnitalSubsemiring R
参数：M : Subsemigroup R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive closure of a non-unital subsemigroup is a non-unital subsemiring.
-/
def nonUnitalSubsemiringClosure (M : Subsemigroup R) : NonUnitalSubsemiring R :=
  { AddSubmonoid.closure (M : Set R) with mul_mem' := MulMemClass.mul_mem_add_closure }
/-
**Subsemigroup.nonUnitalSubsemiringClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subsem
igroup`。
形式化陈述：nonUnitalSubsemiringClosure_coe : (M.nonUnitalSubsemiringClosure : Set R) 
= AddSubmonoid.closure (M : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonUnitalSubsemiringClosure_coe :
    (M.nonUnitalSubsemiringClosure : Set R) = AddSubmonoid.closure (M : Set R) :=
  rfl
/-
**Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命
名空间 `Subsemigroup`。
形式化陈述：nonUnitalSubsemiringClosure_toAddSubmonoid : M.nonUnitalSubsemiringClosure
.toAddSubmonoid = AddSubmonoid.closure (M : Set R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonUnitalSubsemiringClosure_toAddSubmonoid :
    M.nonUnitalSubsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) :=
  rfl

/-- The `NonUnitalSubsemiring` generated by a multiplicative subsemigroup coincides with the
`NonUnitalSubsemiring.closure` of the subsemigroup itself . -/
/-
**Subsemigroup.nonUnitalSubsemiringClosure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 
`Subsemigroup`。
形式化陈述：nonUnitalSubsemiringClosure_eq_closure : M.nonUnitalSubsemiringClosure = N
onUnitalSubsemiring.closure (M : Set R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.ext`：ext {S T : NonUnitalSubsemiring R} (h : forall
 x, x in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S
· 使用定理 `NonUnitalSubsemiring.mem_closure`：mem_closure {x : R} {s : Set R} : x in
 closure s ↔ forall S : NonUnitalSubsemiring R, s subseteq S -> x in S

--- 原说明 ---
The `NonUnitalSubsemiring` generated by a multiplicative subsemigroup coincides 
with the
`NonUnitalSubsemiring.closure` of the subsemigroup itself .
-/
theorem nonUnitalSubsemiringClosure_eq_closure :
    M.nonUnitalSubsemiringClosure = NonUnitalSubsemiring.closure (M : Set R) := by
  ext
  refine ⟨fun hx => ?_,
    fun hx => (NonUnitalSubsemiring.mem_closure.mp hx) M.nonUnitalSubsemiringClosure fun s sM => ?_⟩
  <;> rintro - ⟨H1, rfl⟩
  <;> rintro - ⟨H2, rfl⟩
  · exact AddSubmonoid.mem_closure.mp hx H1.toAddSubmonoid H2
  · exact H2 sM

end Subsemigroup

namespace NonUnitalSubsemiring

@[simp]
/-
**NonUnitalSubsemiring.closure_subsemigroup_closure** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubsemiring`。
形式化陈述：closure_subsemigroup_closure (s : Set R) : closure ↑(Subsemigroup.closure 
s) = closure s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subsemigroup.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall 
S : Subsemigroup M, s subseteq S -> x in S
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `NonUnitalSubsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s sub
seteq t) : closure s <= closure t
· 使用定理 `Subsemigroup.subset_closure`：subset_closure : s subseteq closure s
-/
theorem closure_subsemigroup_closure (s : Set R) : closure ↑(Subsemigroup.closure s) = closure s :=
  le_antisymm
    (closure_le.mpr fun _ hy =>
      (Subsemigroup.mem_closure.mp hy) (closure s).toSubsemigroup subset_closure)
    (closure_mono Subsemigroup.subset_closure)

/-- The elements of the non-unital subsemiring closure of `M` are exactly the elements of the
additive closure of a multiplicative subsemigroup `M`. -/
/-
**NonUnitalSubsemiring.coe_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：coe_closure_eq (s : Set R) : (closure s : Set R) = AddSubmonoid.closure (S
ubsemigroup.closure s : Set R)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsemigroup.nonUnitalSubsemiringClosure_eq_closure`：nonUnitalSubsemirin
gClosure_eq_closure : M.nonUnitalSubsemiringClosure = NonUnitalSubsemiring.closu
re (M : Set R)
· 使用定理 `NonUnitalSubsemiring.closure_subsemigroup_closure`：closure_subsemigroup_
closure (s : Set R) : closure ↑(Subsemigroup.closure s) = closure s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The elements of the non-unital subsemiring closure of `M` are exactly the elemen
ts of the
additive closure of a multiplicative subsemigroup `M`.
-/
theorem coe_closure_eq (s : Set R) :
    (closure s : Set R) = AddSubmonoid.closure (Subsemigroup.closure s : Set R) := by
  simp [← Subsemigroup.nonUnitalSubsemiringClosure_toAddSubmonoid,
    Subsemigroup.nonUnitalSubsemiringClosure_eq_closure]
/-
**NonUnitalSubsemiring.mem_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubse
miring`。
形式化陈述：mem_closure_iff {s : Set R} {x} : x in closure s ↔ x in AddSubmonoid.closu
re (Subsemigroup.closure s : Set R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `NonUnitalSubsemiring.coe_closure_eq`：coe_closure_eq (s : Set R) : (closu
re s : Set R) = AddSubmonoid.closure (Subsemigroup.closure s : Set R)
-/
theorem mem_closure_iff {s : Set R} {x} :
    x ∈ closure s ↔ x ∈ AddSubmonoid.closure (Subsemigroup.closure s : Set R) :=
  Set.ext_iff.mp (coe_closure_eq s) x

@[simp]
/-
**NonUnitalSubsemiring.closure_addSubmonoid_closure** 是 Mathlib 中的一个定理，位于命名空间 `N
onUnitalSubsemiring`。
形式化陈述：closure_addSubmonoid_closure {s : Set R} : closure ↑(AddSubmonoid.closure 
s) = closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.ext`：ext {S T : NonUnitalSubsemiring R} (h : forall
 x, x in S ↔ x in T) : S = T
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddSubmonoid.mem_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : 
Set M} {x : M},   x ∈ AddSubmonoid.closure s ↔ ∀ (S : AddSubmonoid M), s ⊆ ↑S → 
x ∈ S
· 使用定理 `NonUnitalSubsemiring.mem_closure_iff`：mem_closure_iff {s : Set R} {x} : 
x in closure s ↔ x in AddSubmonoid.closure (Subsemigroup.closure s : Set R)
· 使用定理 `Subsemigroup.mem_closure`：mem_closure {x : M} : x in closure s ↔ forall 
S : Subsemigroup M, s subseteq S -> x in S
· 使用定理 `NonUnitalSubsemiring.closure_mono`：closure_mono ⦃s t : Set R⦄ (h : s sub
seteq t) : closure s <= closure t
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
  refine (Subsemigroup.mem_closure.mp hy) H.toSubsemigroup fun z hz => ?_
  exact (AddSubmonoid.mem_closure.mp hz) H.toAddSubmonoid fun w hw => J hw

/-- An induction principle for closure membership. If `p` holds for `0`, `1`, and all elements
of `s`, and is preserved under addition and multiplication, then `p` holds for all elements
of the closure of `s`. -/
@[elab_as_elim]
/-
**NonUnitalSubsemiring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
semiring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (mul : f
orall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in c
losure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；m
ul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in c
losure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
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
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership. If `p` holds for `0`, `1`, and al
l elements
of `s`, and is preserved under addition and multiplication, then `p` holds for a
ll elements
of the closure of `s`.
-/
theorem closure_induction {s : Set R} {p : (x : R) → x ∈ closure s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_closure hx)) (zero : p 0 (zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let K : NonUnitalSubsemiring R :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩ }
  closure_le (t := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

/-- An induction principle for closure membership for predicates with two arguments. -/
@[elab_as_elim]
/-
**NonUnitalSubsemiring.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
semiring`。
形式化陈述：closure_induction {s : Set R} {p : (x : R) -> x in closure s -> Prop} (mem
 : forall (x) (hx : x in s), p x (subset_closure hx)) (zero : p 0 (zero_mem _)) 
(add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)) (mul : f
orall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) {x} (hx : x in c
losure s) : p x hx
参数：x : R；mem : forall (x) (hx : x in s), p x (subset_closure hx)；zero : p 0 (zer
o_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy)；m
ul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；hx : x in c
losure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
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
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
An induction principle for closure membership for predicates with two arguments.
-/
theorem closure_induction₂ {s : Set R} {p : (x y : R) → x ∈ closure s → y ∈ closure s → Prop}
    (mem_mem : ∀ (x) (hx : x ∈ s) (y) (hy : y ∈ s), p x y (subset_closure hx) (subset_closure hy))
    (zero_left : ∀ x hx, p 0 x (zero_mem _) hx) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : R} (hx : x ∈ closure s) (hy : y ∈ closure s) :
    p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem_mem _ h _ hz
    | zero => exact zero_left _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | zero => exact zero_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

variable (R) in
/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**NonUnitalSubsemiring.gi** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：(R : Type u) → [inst : NonUnitalNonAssocSemiring R] → GaloisInsertion NonU
nitalSubsemiring.closure SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure R _) (↑) where
  choice s _ := closure s
  gc _ _ := closure_le
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- Closure of a non-unital subsemiring `S` equals `S`. -/
@[simp]
/-
**NonUnitalSubsemiring.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemirin
g`。
形式化陈述：closure_eq (s : NonUnitalSubsemiring R) : closure (s : Set R) = s
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a non-unital subsemiring `S` equals `S`.
-/
theorem closure_eq (s : NonUnitalSubsemiring R) : closure (s : Set R) = s :=
  (NonUnitalSubsemiring.gi R).l_u_eq s

@[simp]
/-
**NonUnitalSubsemiring.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemi
ring`。
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
  (NonUnitalSubsemiring.gi R).gc.l_bot

@[simp]
/-
**NonUnitalSubsemiring.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemir
ing`。
形式化陈述：closure_univ : closure (Set.univ : Set R) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.closure_eq`：closure_eq (s : NonUnitalSubsemiring R)
 : closure (s : Set R) = s
· 使用定理 `NonUnitalSubsemiring.coe_top`：coe_top : ((⊤ : NonUnitalSubsemiring R) : 
Set R) = Set.univ
-/
theorem closure_univ : closure (Set.univ : Set R) = ⊤ :=
  @coe_top R _ ▸ closure_eq ⊤
/-
**NonUnitalSubsemiring.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemi
ring`。
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
  (NonUnitalSubsemiring.gi R).gc.l_sup
/-
**NonUnitalSubsemiring.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
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
  (NonUnitalSubsemiring.gi R).gc.l_iSup
/-
**NonUnitalSubsemiring.closure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
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
  (NonUnitalSubsemiring.gi R).gc.l_sSup
/-
**NonUnitalSubsemiring.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：map_sup (s t : NonUnitalSubsemiring R) (f : F) : (map f (s ⊔ t) : NonUnita
lSubsemiring S) = map f s ⊔ map f t
参数：s t : NonUnitalSubsemiring R；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem map_sup (s t : NonUnitalSubsemiring R) (f : F) :
    (map f (s ⊔ t) : NonUnitalSubsemiring S) = map f s ⊔ map f t :=
  @GaloisConnection.l_sup _ _ s t _ _ _ _ (gc_map_comap f)
/-
**NonUnitalSubsemiring.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：map_iSup {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring R) : (map f (i
Sup s) : NonUnitalSubsemiring S) = ⨆ i, map f (s i)
参数：f : F；s : ι -> NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : F) (s : ι → NonUnitalSubsemiring R) :
    (map f (iSup s) : NonUnitalSubsemiring S) = ⨆ i, map f (s i) :=
  @GaloisConnection.l_iSup _ _ _ _ _ _ _ (gc_map_comap f) s
/-
**NonUnitalSubsemiring.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：map_inf (s t : NonUnitalSubsemiring R) (f : F) (hf : Function.Injective f)
 : (map f (s ⊓ t) : NonUnitalSubsemiring S) = map f s ⊓ map f t
参数：s t : NonUnitalSubsemiring R；f : F；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (s t : NonUnitalSubsemiring R) (f : F) (hf : Function.Injective f) :
    (map f (s ⊓ t) : NonUnitalSubsemiring S) = map f s ⊓ map f t :=
  SetLike.coe_injective (Set.image_inter hf)
/-
**NonUnitalSubsemiring.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f) (s :
 ι -> NonUnitalSubsemiring R) : (map f (iInf s) : NonUnitalSubsemiring S) = ⨅ i,
 map f (s i)
参数：f : F；hf : Function.Injective f；s : ι -> NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> NonUnitalS
ubsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : F) (hf : Function.Injective f)
    (s : ι → NonUnitalSubsemiring R) :
    (map f (iInf s) : NonUnitalSubsemiring S) = ⨅ i, map f (s i) := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)
/-
**NonUnitalSubsemiring.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：comap_inf (s t : NonUnitalSubsemiring S) (f : F) : (comap f (s ⊓ t) : NonU
nitalSubsemiring R) = comap f s ⊓ comap f t
参数：s t : NonUnitalSubsemiring S；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem comap_inf (s t : NonUnitalSubsemiring S) (f : F) :
    (comap f (s ⊓ t) : NonUnitalSubsemiring R) = comap f s ⊓ comap f t :=
  @GaloisConnection.u_inf _ _ s t _ _ _ _ (gc_map_comap f)
/-
**NonUnitalSubsemiring.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemirin
g`。
形式化陈述：comap_iInf {ι : Sort*} (f : F) (s : ι -> NonUnitalSubsemiring S) : (comap 
f (iInf s) : NonUnitalSubsemiring R) = ⨅ i, comap f (s i)
参数：f : F；s : ι -> NonUnitalSubsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : F) (s : ι → NonUnitalSubsemiring S) :
    (comap f (iInf s) : NonUnitalSubsemiring R) = ⨅ i, comap f (s i) :=
  @GaloisConnection.u_iInf _ _ _ _ _ _ _ (gc_map_comap f) s

@[simp]
/-
**NonUnitalSubsemiring.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：map_bot (f : F) : map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubse
miring S)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem map_bot (f : F) : map f (⊥ : NonUnitalSubsemiring R) = (⊥ : NonUnitalSubsemiring S) :=
  (gc_map_comap f).l_bot

@[simp]
/-
**NonUnitalSubsemiring.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：comap_top (f : F) : comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalS
ubsemiring R)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
-/
theorem comap_top (f : F) : comap f (⊤ : NonUnitalSubsemiring S) = (⊤ : NonUnitalSubsemiring R) :=
  (gc_map_comap f).u_top

/-- Given `NonUnitalSubsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is
`s × t` as a non-unital subsemiring of `R × S`. -/
/-
**NonUnitalSubsemiring.prod** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring`。
形式化陈述：prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : NonUnital
Subsemiring (R × S)
参数：s : NonUnitalSubsemiring R；t : NonUnitalSubsemiring S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `NonUnitalSubsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.pr
od t` is
`s × t` as a non-unital subsemiring of `R × S`.
-/
def prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : NonUnitalSubsemiring (R × S) :=
  { s.toSubsemigroup.prod t.toSubsemigroup, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := (s : Set R) ×ˢ (t : Set S) }

@[norm_cast]
/-
**NonUnitalSubsemiring.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：coe_prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : (s.pr
od t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S)
参数：s : NonUnitalSubsemiring R；t : NonUnitalSubsemiring S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) :=
  rfl
/-
**NonUnitalSubsemiring.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：mem_prod {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R 
× S} : p in s.prod t ↔ p.1 in s ∧ p.2 in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : NonUnitalSubsemiring R} {t : NonUnitalSubsemiring S} {p : R × S} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[gcongr, mono]
/-
**NonUnitalSubsemiring.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUni
talSubsemiring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁ <= s₂.prod t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring R⦄ (hs : s₁ ≤ s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄
    (ht : t₁ ≤ t₂) : s₁.prod t₁ ≤ s₂.prod t₂ :=
  Set.prod_mono hs ht
/-
**NonUnitalSubsemiring.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubse
miring`。
形式化陈述：prod_mono_right (s : NonUnitalSubsemiring R) : Monotone fun t : NonUnitalS
ubsemiring S => s.prod t
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.prod_mono`：prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring 
R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁
 <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_right (s : NonUnitalSubsemiring R) :
    Monotone fun t : NonUnitalSubsemiring S => s.prod t :=
  prod_mono (le_refl s)
/-
**NonUnitalSubsemiring.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：prod_mono_left (t : NonUnitalSubsemiring S) : Monotone fun s : NonUnitalSu
bsemiring R => s.prod t
参数：t : NonUnitalSubsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.prod_mono`：prod_mono ⦃s₁ s₂ : NonUnitalSubsemiring 
R⦄ (hs : s₁ <= s₂) ⦃t₁ t₂ : NonUnitalSubsemiring S⦄ (ht : t₁ <= t₂) : s₁.prod t₁
 <= s₂.prod t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_left (t : NonUnitalSubsemiring S) :
    Monotone fun s : NonUnitalSubsemiring R => s.prod t := fun _ _ hs => prod_mono hs (le_refl t)
/-
**NonUnitalSubsemiring.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：prod_top (s : NonUnitalSubsemiring R) : s.prod (⊤ : NonUnitalSubsemiring S
) = s.comap (NonUnitalRingHom.fst R S)
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.ext`：ext {S T : NonUnitalSubsemiring R} (h : forall
 x, x in S ↔ x in T) : S = T
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
theorem prod_top (s : NonUnitalSubsemiring R) :
    s.prod (⊤ : NonUnitalSubsemiring S) = s.comap (NonUnitalRingHom.fst R S) :=
  ext fun x => by simp [mem_prod]
/-
**NonUnitalSubsemiring.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring`
。
形式化陈述：top_prod (s : NonUnitalSubsemiring S) : (⊤ : NonUnitalSubsemiring R).prod 
s = s.comap (NonUnitalRingHom.snd R S)
参数：s : NonUnitalSubsemiring S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.ext`：ext {S T : NonUnitalSubsemiring R} (h : forall
 x, x in S ↔ x in T) : S = T
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
theorem top_prod (s : NonUnitalSubsemiring S) :
    (⊤ : NonUnitalSubsemiring R).prod s = s.comap (NonUnitalRingHom.snd R S) :=
  ext fun x => by simp [mem_prod]

@[simp]
/-
**NonUnitalSubsemiring.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemir
ing`。
形式化陈述：top_prod_top : (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring
 S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubsemiring.top_prod`：top_prod (s : NonUnitalSubsemiring S) : (
⊤ : NonUnitalSubsemiring R).prod s = s.comap (NonUnitalRingHom.snd R S)
· 使用定理 `NonUnitalSubsemiring.comap_top`：comap_top (f : F) : comap f (⊤ : NonUnit
alSubsemiring S) = (⊤ : NonUnitalSubsemiring R)
-/
theorem top_prod_top : (⊤ : NonUnitalSubsemiring R).prod (⊤ : NonUnitalSubsemiring S) = ⊤ :=
  (top_prod _).trans <| comap_top _
/-
**NonUnitalSubsemiring.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalNonAssocSemiring R] [inst_1 :
 NonUnitalNonAssocSemiring S],   NonUnitalSubsemiring.center (R × S) = (NonUnita
lSubsemiring.center R).prod (NonUnitalSubsemiring.center S)
参数：R × S；NonUnitalSubsemiring.center R；NonUnitalSubsemiring.center S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center (R × S) = prod (center R) (center S) :=
  SetLike.coe_injective Set.center_prod

/-- Product of non-unital subsemirings is isomorphic to their product as semigroups. -/
/-
**NonUnitalSubsemiring.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：prodEquiv (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : s.pr
od t ≃+* s × t
参数：s : NonUnitalSubsemiring R；t : NonUnitalSubsemiring S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
Product of non-unital subsemirings is isomorphic to their product as semigroups.
-/
def prodEquiv (s : NonUnitalSubsemiring R) (t : NonUnitalSubsemiring S) : s.prod t ≃+* s × t :=
  { Equiv.Set.prod (s : Set R) (t : Set S) with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }
/-
**NonUnitalSubsemiring.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subsemiring`。
形式化陈述：mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring 
R} (hS : Directed (· <= ·) S) {x : R} : (x in ⨆ i, S i) ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.mk'`：mk'_toSubsemigroup {s : Set R} {sg : Subsemigr
oup R} (hg : ↑sg = s) {sa : AddSubmonoid R} (ha : ↑sa = s) : (NonUnitalSubsemiri
ng.mk' s sg hg…
· 使用定理 `Subsemigroup.coe_iSup_of_directed`：coe_iSup_of_directed {S : ι -> Subsem
igroup M} (hS : Directed (· <= ·) S) : ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃
 i, S i
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
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubsemiring R}
    (hS : Directed (· ≤ ·) S) {x : R} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  let U : NonUnitalSubsemiring R :=
    NonUnitalSubsemiring.mk' (⋃ i, (S i : Set R))
      (⨆ i, (S i).toSubsemigroup) (Subsemigroup.coe_iSup_of_directed hS)
      (⨆ i, (S i).toAddSubmonoid) (AddSubmonoid.coe_iSup_of_directed hS)
  suffices ⨆ i, S i ≤ U by simpa [U] using @this x
  exact iSup_le fun i x hx => Set.mem_iUnion.2 ⟨i, hx⟩
/-
**NonUnitalSubsemiring.coe_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subsemiring`。
形式化陈述：coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι -> NonUnitalSubsemiring 
R} (hS : Directed (· <= ·) S) : ((⨆ i, S i : NonUnitalSubsemiring R) : Set R) = 
⋃ i, S i
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
· 使用定理 `NonUnitalSubsemiring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) {x : 
R} : (x in ⨆ i, S i) ↔ exists i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_iSup_of_directed {ι} [hι : Nonempty ι] {S : ι → NonUnitalSubsemiring R}
    (hS : Directed (· ≤ ·) S) : ((⨆ i, S i : NonUnitalSubsemiring R) : Set R) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]
/-
**NonUnitalSubsemiring.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubsemiring`。
形式化陈述：mem_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempt
y) (hS : DirectedOn (· <= ·) S) {x : R} : x in sSup S ↔ exists s in S, x in s
参数：NonUnitalSubsemiring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
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
· 使用定理 `NonUnitalSubsemiring.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) {x : 
R} : (x in ⨆ i, S i) ↔ exists i…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : R} : x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]
/-
**NonUnitalSubsemiring.coe_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubsemiring`。
形式化陈述：coe_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempt
y) (hS : DirectedOn (· <= ·) S) : (↑(sSup S) : Set R) = ⋃ s in S, ↑s
参数：NonUnitalSubsemiring R；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.mem_sSup_of_directedOn`：mem_sSup_of_directedOn {S :
 Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty) (hS : DirectedOn (· <= ·) S) {
x : R} : x in sSup S ↔ exists s i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sSup_of_directedOn {S : Set (NonUnitalSubsemiring R)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set R) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_sSup_of_directedOn Sne hS]
/-
**NonUnitalSubsemiring.isMulCommutative_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lSubsemiring`。
形式化陈述：isMulCommutative_iSup {ι : Sort*} [Nonempty ι] {S : ι -> NonUnitalSubsemir
ing R} [hS : forall i, IsMulCommutative (S i)] (dir : Directed (· <= ·) S) : IsM
ulCommutative (⨆ i, S i : NonUnitalSubsemiring R)
参数：S i；dir : Directed (· <= ·) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [hι 
: Nonempty ι] {S : ι -> NonUnitalSubsemiring R} (hS : Directed (· <= ·) S) : ((⨆
 i, S i : NonUnitalSubsemiring …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
theorem isMulCommutative_iSup {ι : Sort*} [Nonempty ι]
    {S : ι → NonUnitalSubsemiring R} [hS : ∀ i, IsMulCommutative (S i)]
    (dir : Directed (· ≤ ·) S) : IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring R) := by
  refine .of_setLike_mul_comm ?_
  simp_rw [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index]
  intro a i ha b j hb
  obtain ⟨k, hik, hjk⟩ := dir i j
  exact setLike_mul_comm (hik ha) (hjk hb)
/-
**NonUnitalSubsemiring.instIsMulCommutative_iSup** 是 Mathlib 中的一个实例，位于命名空间 `NonU
nitalSubsemiring`。
形式化陈述：instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι] [IsDirecte
dOrder ι] {S : ι ->o NonUnitalSubsemiring R} [hS : forall i, IsMulCommutative (S
 i)] : IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring R)
参数：S i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalSubsemiring.isMulCommutative_iSup`：isMulCommutative_iSup {ι : S
ort*} [Nonempty ι] {S : ι -> NonUnitalSubsemiring R} [hS : forall i, IsMulCommut
ative (S i)] (dir : Directed (· …
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
instance instIsMulCommutative_iSup {ι : Type*} [Nonempty ι] [Preorder ι]
    [IsDirectedOrder ι] {S : ι →o NonUnitalSubsemiring R} [hS : ∀ i, IsMulCommutative (S i)] :
    IsMulCommutative (⨆ i, S i : NonUnitalSubsemiring R) :=
  NonUnitalSubsemiring.isMulCommutative_iSup S.monotone.directed_le

end NonUnitalSubsemiring

namespace NonUnitalRingHom

variable {F : Type*} [FunLike F R S]

/-
**NonUnitalRingHom.eq_of_eqOn_stop** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：eq_of_eqOn_stop {f g : F} (h : Set.EqOn (f : R -> S) (g : R -> S) (⊤ : Non
UnitalSubsemiring R)) : f = g
参数：h : Set.EqOn (f : R -> S) (g : R -> S) (⊤ : NonUnitalSubsemiring R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_stop {f g : F}
    (h : Set.EqOn (f : R → S) (g : R → S) (⊤ : NonUnitalSubsemiring R)) : f = g :=
  DFunLike.ext _ _ fun _ => h trivial

variable [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring T]
  [NonUnitalRingHomClass F R S]
  {S' : Type*} [SetLike S' S] [NonUnitalSubsemiringClass S' S]
  {s : NonUnitalSubsemiring R}

open NonUnitalSubsemiringClass NonUnitalSubsemiring

/-- Restriction of a non-unital ring homomorphism to its range interpreted as a
non-unital subsemiring.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**NonUnitalRingHom.srangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalRingHom`。
形式化陈述：srangeRestrict (f : F) : R ->ₙ+* (srange f : NonUnitalSubsemiring S)
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalRingHom.mem_srange_self`：mem_srange_self (f : F) (x : R) : f x 
in srange f

--- 原说明 ---
Restriction of a non-unital ring homomorphism to its range interpreted as a
non-unital subsemiring.

This is the bundled version of `Set.rangeFactorization`.
-/
def srangeRestrict (f : F) : R →ₙ+* (srange f : NonUnitalSubsemiring S) :=
  codRestrict f (srange f) (mem_srange_self f)

@[simp]
/-
**NonUnitalRingHom.coe_srangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHo
m`。
形式化陈述：coe_srangeRestrict (f : F) (x : R) : (srangeRestrict f x : S) = f x
参数：f : F；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem coe_srangeRestrict (f : F) (x : R) : (srangeRestrict f x : S) = f x :=
  rfl
/-
**NonUnitalRingHom.srangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnita
lRingHom`。
形式化陈述：srangeRestrict_surjective (f : F) : Function.Surjective (srangeRestrict f 
: R -> (srange f : NonUnitalSubsemiring S))
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NonUnitalRingHom.mem_srange`：mem_srange {f : F} {y : S} : y in srange f 
↔ exists x, f x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem srangeRestrict_surjective (f : F) :
    Function.Surjective (srangeRestrict f : R → (srange f : NonUnitalSubsemiring S)) :=
  fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := mem_srange.mp hy
  ⟨x, Subtype.ext hx⟩
/-
**NonUnitalRingHom.srange_eq_top_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italRingHom`。
形式化陈述：srange_eq_top_iff_surjective {f : F} : srange f = (⊤ : NonUnitalSubsemirin
g S) ↔ Function.Surjective (f : R -> S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalRingHom.coe_srange`：coe_srange : (srange f : Set S) = Set.range
 f
· 使用定理 `NonUnitalSubsemiring.coe_top`：coe_top : ((⊤ : NonUnitalSubsemiring R) : 
Set R) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem srange_eq_top_iff_surjective {f : F} :
    srange f = (⊤ : NonUnitalSubsemiring S) ↔ Function.Surjective (f : R → S) :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_srange, coe_top]) Set.range_eq_univ

/-- The range of a surjective non-unital ring homomorphism is the whole of the codomain. -/
@[simp]
/-
**NonUnitalRingHom.srange_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talRingHom`。
形式化陈述：srange_eq_top_of_surjective (f : F) (hf : Function.Surjective (f : R -> S)
) : srange f = (⊤ : NonUnitalSubsemiring S)
参数：f : F；hf : Function.Surjective (f : R -> S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalRingHom.srange_eq_top_iff_surjective`：srange_eq_top_iff_surject
ive {f : F} : srange f = (⊤ : NonUnitalSubsemiring S) ↔ Function.Surjective (f :
 R -> S)

--- 原说明 ---
The range of a surjective non-unital ring homomorphism is the whole of the codom
ain.
-/
theorem srange_eq_top_of_surjective (f : F) (hf : Function.Surjective (f : R → S)) :
    srange f = (⊤ : NonUnitalSubsemiring S) :=
  srange_eq_top_iff_surjective.2 hf

/-- If two non-unital ring homomorphisms are equal on a set, then they are equal on its
non-unital subsemiring closure. -/
/-
**NonUnitalRingHom.eqOn_sclosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：eqOn_sclosure {f g : F} {s : Set R} (h : Set.EqOn (f : R -> S) (g : R -> S
) s) : Set.EqOn f g (closure s)
参数：h : Set.EqOn (f : R -> S) (g : R -> S) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t

--- 原说明 ---
If two non-unital ring homomorphisms are equal on a set, then they are equal on 
its
non-unital subsemiring closure.
-/
theorem eqOn_sclosure {f g : F} {s : Set R} (h : Set.EqOn (f : R → S) (g : R → S) s) :
    Set.EqOn f g (closure s) :=
  show closure s ≤ eqSlocus f g from closure_le.2 h
/-
**NonUnitalRingHom.eq_of_eqOn_sdense** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom
`。
形式化陈述：eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : F} (h : s.EqOn (
f : R -> S) (g : R -> S)) : f = g
参数：hs : closure s = ⊤；h : s.EqOn (f : R -> S) (g : R -> S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.eq_of_eqOn_stop`：eq_of_eqOn_stop {f g : F} (h : Set.EqO
n (f : R -> S) (g : R -> S) (⊤ : NonUnitalSubsemiring R)) : f = g
· 使用定理 `NonUnitalRingHom.eqOn_sclosure`：eqOn_sclosure {f g : F} {s : Set R} (h :
 Set.EqOn (f : R -> S) (g : R -> S) s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_sdense {s : Set R} (hs : closure s = ⊤) {f g : F}
    (h : s.EqOn (f : R → S) (g : R → S)) : f = g :=
  eq_of_eqOn_stop <| hs ▸ eqOn_sclosure h
/-
**NonUnitalRingHom.sclosure_preimage_le** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRing
Hom`。
形式化陈述：sclosure_preimage_le (f : F) (s : Set S) : closure ((f : R -> S) ⁻¹' s) <=
 (closure s).comap f
参数：f : F；s : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NonUnitalSubsemiring.closure_le`：closure_le {s : Set R} {t : NonUnitalSu
bsemiring R} : closure s <= t ↔ s subseteq t
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `NonUnitalSubsemiring.mem_comap`：mem_comap {s : NonUnitalSubsemiring S} {
f : F} {x : R} : x in s.comap f ↔ f x in s
· 使用定理 `NonUnitalSubsemiring.subset_closure`：subset_closure {s : Set R} : s subs
eteq closure s
-/
theorem sclosure_preimage_le (f : F) (s : Set S) :
    closure ((f : R → S) ⁻¹' s) ≤ (closure s).comap f :=
  closure_le.2 fun _ hx => SetLike.mem_coe.2 <| mem_comap.2 <| subset_closure hx

/-- The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set. -/
/-
**NonUnitalRingHom.map_sclosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalRingHom`。
形式化陈述：map_sclosure (f : F) (s : Set R) : (closure s).map f = closure ((f : R -> 
S) '' s)
参数：f : F；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_comm_of_u_comm`：l_comm_of_u_comm {X : Type*} [Preorde
r X] {Y : Type*} [Preorder Y] {Z : Type*} [Preorder Z] {W : Type*} [PartialOrder
 W] {lYX : X -> Y} {uXY…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `NonUnitalSubsemiring.gc_map_comap`：gc_map_comap (f : F) : @GaloisConnect
ion (NonUnitalSubsemiring R) (NonUnitalSubsemiring S) _ _ (map f) (comap f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The image under a ring homomorphism of the subsemiring generated by a set equals
the subsemiring generated by the image of the set.
-/
theorem map_sclosure (f : F) (s : Set R) : (closure s).map f = closure ((f : R → S) '' s) :=
  Set.image_preimage.l_comm_of_u_comm (gc_map_comap f) (NonUnitalSubsemiring.gi S).gc
    (NonUnitalSubsemiring.gi R).gc fun _ ↦ rfl

end NonUnitalRingHom

namespace NonUnitalSubsemiring

open NonUnitalRingHom NonUnitalSubsemiringClass

@[simp]
/-
**NonUnitalSubsemiring.srange_subtype** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsem
iring`。
形式化陈述：srange_subtype (s : NonUnitalSubsemiring R) : NonUnitalRingHom.srange (sub
type s) = s
参数：s : NonUnitalSubsemiring R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalRingHom.coe_srange`：coe_srange : (srange f : Set S) = Set.range
 f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem srange_subtype (s : NonUnitalSubsemiring R) : NonUnitalRingHom.srange (subtype s) = s :=
  SetLike.coe_injective <| (coe_srange _).trans Subtype.range_coe

variable [NonUnitalNonAssocSemiring S]

@[simp]
/-
**NonUnitalSubsemiring.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：range_fst : NonUnitalRingHom.srange (fst R S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.srange_eq_top_of_surjective`：srange_eq_top_of_surjectiv
e (f : F) (hf : Function.Surjective (f : R -> S)) : srange f = (⊤ : NonUnitalSub
semiring S)
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem range_fst : NonUnitalRingHom.srange (fst R S) = ⊤ :=
  NonUnitalRingHom.srange_eq_top_of_surjective (fst R S) Prod.fst_surjective

@[simp]
/-
**NonUnitalSubsemiring.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubsemiring
`。
形式化陈述：range_snd : NonUnitalRingHom.srange (snd R S) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.srange_eq_top_of_surjective`：srange_eq_top_of_surjectiv
e (f : F) (hf : Function.Surjective (f : R -> S)) : srange f = (⊤ : NonUnitalSub
semiring S)
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem range_snd : NonUnitalRingHom.srange (snd R S) = ⊤ :=
  NonUnitalRingHom.srange_eq_top_of_surjective (snd R S) <| Prod.snd_surjective

end NonUnitalSubsemiring

namespace RingEquiv

open NonUnitalRingHom NonUnitalSubsemiringClass

variable {s t : NonUnitalSubsemiring R}
variable [NonUnitalNonAssocSemiring S] {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]

/-- Makes the identity isomorphism from a proof two non-unital subsemirings of a multiplicative
monoid are equal. -/
/-
**RingEquiv.nonUnitalSubsemiringCongr** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：nonUnitalSubsemiringCongr (h : s = t) : s ≃+* t
参数：h : s = t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
Makes the identity isomorphism from a proof two non-unital subsemirings of a mul
tiplicative
monoid are equal.
-/
def nonUnitalSubsemiringCongr (h : s = t) : s ≃+* t :=
  { Equiv.setCongr <| congr_arg _ h with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Restrict a non-unital ring homomorphism with a left inverse to a ring isomorphism to its
`NonUnitalRingHom.srange`. -/
/-
**RingEquiv.sofLeftInverse'** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：sofLeftInverse' {g : S -> R} {f : F} (h : Function.LeftInverse g f) : R ≃+
* srange f
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
Restrict a non-unital ring homomorphism with a left inverse to a ring isomorphis
m to its
`NonUnitalRingHom.srange`.
-/
def sofLeftInverse' {g : S → R} {f : F} (h : Function.LeftInverse g f) : R ≃+* srange f :=
  { srangeRestrict f with
    toFun := srangeRestrict f
    invFun := fun x => g (subtype (srange f) x)
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := NonUnitalRingHom.mem_srange.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**RingEquiv.sofLeftInverse'_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalNonAssocSemiring R] [inst_1 :
 NonUnitalNonAssocSemiring S] {F : Type u_1}   [inst_2 : FunLike F R S] [inst_3 
: NonUnitalRingHomClass F R S] {g : S → R} {f : F} (h : Function.LeftInverse g ⇑
f)   (x : R), ↑((RingEquiv.sofLeftInverse' h) x) = f x
参数：h : Function.LeftInverse g ⇑f；x : R；(RingEquiv.sofLeftInverse' h) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem sofLeftInverse'_apply {g : S → R} {f : F} (h : Function.LeftInverse g f) (x : R) :
    ↑(sofLeftInverse' h x) = f x :=
  rfl

@[simp]
/-
**RingEquiv.sofLeftInverse'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : NonUnitalNonAssocSemiring R] [inst_1 :
 NonUnitalNonAssocSemiring S] {F : Type u_1}   [inst_2 : FunLike F R S] [inst_3 
: NonUnitalRingHomClass F R S] {g : S → R} {f : F} (h : Function.LeftInverse g ⇑
f)   (x : ↥(NonUnitalRingHom.srange f)), (RingEquiv.sofLeftInverse' h).symm x = 
g ↑x
参数：h : Function.LeftInverse g ⇑f；x : ↥(NonUnitalRingHom.srange f)；RingEquiv.sofL
eftInverse' h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R
-/
theorem sofLeftInverse'_symm_apply {g : S → R} {f : F} (h : Function.LeftInverse g f)
    (x : srange f) : (sofLeftInverse' h).symm x = g x :=
  rfl

/-- Given an equivalence `e : R ≃+* S` of non-unital semirings and a non-unital subsemiring
`s` of `R`, `nonUnitalSubsemiringMap e s` is the induced equivalence between `s` and
`s.map e` -/
@[simps!]
/-
**RingEquiv.nonUnitalSubsemiringMap** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：nonUnitalSubsemiringMap (e : R ≃+* S) (s : NonUnitalSubsemiring R) : s ≃+*
 NonUnitalSubsemiring.map e.toNonUnitalRingHom s
参数：e : R ≃+* S；s : NonUnitalSubsemiring R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalSubsemiring.instNonUnitalSubsemiringClass`：∀ {R : Type u} [inst
 : NonUnitalNonAssocSemiring R], NonUnitalSubsemiringClass (NonUnitalSubsemiring
 R) R

--- 原说明 ---
Given an equivalence `e : R ≃+* S` of non-unital semirings and a non-unital subs
emiring
`s` of `R`, `nonUnitalSubsemiringMap e s` is the induced equivalence between `s`
 and
`s.map e`
-/
def nonUnitalSubsemiringMap (e : R ≃+* S) (s : NonUnitalSubsemiring R) :
    s ≃+* NonUnitalSubsemiring.map e.toNonUnitalRingHom s :=
  { e.toAddEquiv.addSubmonoidMap s.toAddSubmonoid,
    e.toMulEquiv.subsemigroupMap s.toSubsemigroup with }

end RingEquiv

