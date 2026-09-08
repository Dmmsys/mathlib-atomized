/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Closure
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Encoding

/-!
# First-Order Substructures

This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions

- A `FirstOrder.Language.Substructure` is defined so that `L.Substructure M` is the type of all
    substructures of the `L`-structure `M`.
- `FirstOrder.Language.Substructure.closure` is defined so that if `s : Set M`, `closure L s` is
    the least substructure of `M` containing `s`.
- `FirstOrder.Language.Substructure.comap` is defined so that `s.comap f` is the preimage of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Substructure.map` is defined so that `s.map f` is the image of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.range` is defined so that `f.range` is the range of the
    homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.domRestrict` and `FirstOrder.Language.Hom.codRestrict` restrict
    the domain and codomain respectively of first-order homomorphisms to substructures.
- `FirstOrder.Language.Embedding.domRestrict` and `FirstOrder.Language.Embedding.codRestrict`
    restrict the domain and codomain respectively of first-order embeddings to substructures.
- `FirstOrder.Language.Substructure.inclusion` is the inclusion embedding between substructures.
- `FirstOrder.Language.Substructure.PartialEquiv` is defined so that `PartialEquiv L M N` is
  the type of equivalences between substructures of `M` and `N`.

## Main Results

- `L.Substructure M` forms a `CompleteLattice`.
-/

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure

section ClosedUnder

open Set

variable {n : ℕ} (f : L.Functions n) (s : Set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
/-
**FirstOrder.Language.ClosedUnder** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
`。
形式化陈述：ClosedUnder : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indicates that a set in a given structure is a closed under a function symbol.
-/
def ClosedUnder : Prop :=
  ∀ x : Fin n → M, (∀ i : Fin n, x i ∈ s) → funMap f x ∈ s

variable (L)

@[simp]
/-
**FirstOrder.Language.closedUnder_univ** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：closedUnder_univ : ClosedUnder f (univ : Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem closedUnder_univ : ClosedUnder f (univ : Set M) := fun _ _ => mem_univ _

variable {L f s} {t : Set M}

namespace ClosedUnder

/-
**FirstOrder.Language.ClosedUnder.inter** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.ClosedUnder`。
形式化陈述：inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s int
er t)
参数：hs : ClosedUnder f s；ht : ClosedUnder f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
-/
theorem inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ∩ t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))
/-
**FirstOrder.Language.ClosedUnder.inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.ClosedUnder`。
形式化陈述：inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ⊓ t)
参数：hs : ClosedUnder f s；ht : ClosedUnder f t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.ClosedUnder.inter`：inter (hs : ClosedUnder f s) (ht 
: ClosedUnder f t) : ClosedUnder f (s inter t)
-/
theorem inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ⊓ t) :=
  hs.inter ht

variable {S : Set (Set M)}
/-
**FirstOrder.Language.ClosedUnder.sInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.ClosedUnder`。
形式化陈述：sInf (hS : forall s, s in S -> ClosedUnder f s) : ClosedUnder f (sInf S)
参数：hS : forall s, s in S -> ClosedUnder f s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf (hS : ∀ s, s ∈ S → ClosedUnder f s) : ClosedUnder f (sInf S) := fun x h s hs =>
  hS s hs x fun i => h i s hs

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
/-
**FirstOrder.Language.Substructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：(L : FirstOrder.Language) → (M : Type w) → [L.Structure M] → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A substructure of a structure `M` is a set closed under application of function 
symbols.
-/
structure Substructure where
  /-- The underlying set of this substructure -/
  carrier : Set M
  fun_mem : ∀ {n}, ∀ f : L.Functions n, ClosedUnder f carrier

variable {L} {M}

namespace Substructure

attribute [coe] Substructure.carrier

/-
**FirstOrder.Language.Substructure.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：instSetLike : SetLike (L.Substructure M) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (L.Substructure M) M :=
  ⟨Substructure.carrier, fun p q h => by cases p; cases q; congr⟩
/-
**FirstOrder.Language.Substructure.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (L.Substructure M) := .ofSetLike (L.Substructure M) M

/-- See Note [custom simps projection] -/
/-
**FirstOrder.Language.Substructure.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.Substructure.Simps`。
形式化陈述：{L : FirstOrder.Language} → {M : Type w} → [inst : L.Structure M] → L.Subs
tructure M → Set M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.coe (S : L.Substructure M) : Set M :=
  S

initialize_simps_projections Substructure (carrier → coe, as_prefix coe)

@[simp]
/-
**FirstOrder.Language.Substructure.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：mem_carrier {s : L.Substructure M} {x : M} : x in s.carrier ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {s : L.Substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
/-
**FirstOrder.Language.Substructure.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Substructure`。
形式化陈述：ext {S T : L.Substructure M} (h : forall x, x in S ↔ x in T) : S = T
参数：h : forall x, x in S ↔ x in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two substructures are equal if they have the same elements.
-/
theorem ext {S T : L.Substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
/-
**FirstOrder.Language.Substructure.copy** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Substructure`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} → [inst : L.Structure M] → (S :
 L.Substructure M) → (s : Set M) → s = ↑S → L.Substructure M
参数：S : L.Substructure M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy a substructure replacing `carrier` with a set that is equal to it.
-/
protected def copy (S : L.Substructure M) (s : Set M) (hs : s = S) : L.Substructure M where
  carrier := s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f

end Substructure

variable {S : L.Substructure M}

/-
**FirstOrder.Language.Term.realize_mem** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Term`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {S : L.Sub
structure M} {α : Type u_3} (t : L.Term α)   (xs : α → M), (∀ (a : α), xs a ∈ S)
 → FirstOrder.Language.Term.realize xs t ∈ S
参数：t : L.Term α；xs : α → M；∀ (a : α), xs a ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.fun_mem`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] (self : L.Substructure M) {n : ℕ} (f : L.Funct
ions n),   FirstOrder.Language…
-/
theorem Term.realize_mem {α : Type*} (t : L.Term α) (xs : α → M) (h : ∀ a, xs a ∈ S) :
    t.realize xs ∈ S := by
  induction t with
  | var a => exact h a
  | func f ts ih => exact Substructure.fun_mem _ _ _ ih

namespace Substructure

@[simp]
/-
**FirstOrder.Language.Substructure.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s
参数：hs : s = S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
/-
**FirstOrder.Language.Substructure.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S
参数：hs : s = S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**FirstOrder.Language.Substructure.constants_mem** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：constants_mem (c : L.Constants) : (c : M) in S
参数：c : L.Constants。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Substructure.mem_carrier`：mem_carrier {s : L.Substru
cture M} {x : M} : x in s.carrier ↔ x in s
· 使用定理 `FirstOrder.Language.Substructure.fun_mem`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] (self : L.Substructure M) {n : ℕ} (f : L.Funct
ions n),   FirstOrder.Language…
-/
theorem constants_mem (c : L.Constants) : (c : M) ∈ S :=
  mem_carrier.2 (S.fun_mem c _ finZeroElim)

/-- The substructure `M` of the structure `M`. -/
/-
**FirstOrder.Language.Substructure.instTop** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：instTop : Top (L.Substructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The substructure `M` of the structure `M`.
-/
instance instTop : Top (L.Substructure M) :=
  ⟨{  carrier := Set.univ
      fun_mem := fun {_} _ _ _ => Set.mem_univ _ }⟩
/-
**FirstOrder.Language.Substructure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：instInhabited : Inhabited (L.Substructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
/-
**FirstOrder.Language.Substructure.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：mem_top (x : M) : x in (⊤ : L.Substructure M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : M) : x ∈ (⊤ : L.Substructure M) :=
  Set.mem_univ x

@[simp]
/-
**FirstOrder.Language.Substructure.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：coe_top : ((⊤ : L.Substructure M) : Set M) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : L.Substructure M) : Set M) = Set.univ :=
  rfl

/-- The inf of two substructures is their intersection. -/
/-
**FirstOrder.Language.Substructure.instInf** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：instInf : Min (L.Substructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inf of two substructures is their intersection.
-/
instance instInf : Min (L.Substructure M) :=
  ⟨fun S₁ S₂ =>
    { carrier := (S₁ : Set M) ∩ (S₂ : Set M)
      fun_mem := fun {_} f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
/-
**FirstOrder.Language.Substructure.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：coe_inf (p p' : L.Substructure M) : ((p ⊓ p' : L.Substructure M) : Set M) 
= (p : Set M) inter (p' : Set M)
参数：p p' : L.Substructure M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (p p' : L.Substructure M) :
    ((p ⊓ p' : L.Substructure M) : Set M) = (p : Set M) ∩ (p' : Set M) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Substructure.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：mem_inf {p p' : L.Substructure M} {x : M} : x in p ⊓ p' ↔ x in p ∧ x in p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p p' : L.Substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
/-
**FirstOrder.Language.Substructure.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：instInfSet : InfSet (L.Substructure M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfSet : InfSet (L.Substructure M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, (t : Set M)
      fun_mem := fun {n} f =>
        ClosedUnder.sInf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t ∈ s
            · simpa [h] using! t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]
/-
**FirstOrder.Language.Substructure.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：coe_sInf (S : Set (L.Substructure M)) : ((sInf S : L.Substructure M) : Set
 M) = ⋂ s in S, (s : Set M)
参数：S : Set (L.Substructure M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (L.Substructure M)) :
    ((sInf S : L.Substructure M) : Set M) = ⋂ s ∈ S, (s : Set M) :=
  rfl
/-
**FirstOrder.Language.Substructure.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：mem_sInf {S : Set (L.Substructure M)} {x : M} : x in sInf S ↔ forall p in 
S, x in p
参数：L.Substructure M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (L.Substructure M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
/-
**FirstOrder.Language.Substructure.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> L.Substructure M} {x : M} : x in ⨅ i, S i ↔
 forall i, x in S i
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
theorem mem_iInf {ι : Sort*} {S : ι → L.Substructure M} {x : M} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp, norm_cast]
/-
**FirstOrder.Language.Substructure.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> L.Substructure M} : ((⨅ i, S i : L.Substruc
ture M) : Set M) = ⋂ i, (S i : Set M)
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
theorem coe_iInf {ι : Sort*} {S : ι → L.Substructure M} :
    ((⨅ i, S i : L.Substructure M) : Set M) = ⋂ i, (S i : Set M) := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/-- Substructures of a structure form a complete lattice. -/
/-
**FirstOrder.Language.Substructure.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间
 `FirstOrder.Language.Substructure`。
形式化陈述：instCompleteLattice : CompleteLattice (L.Substructure M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.mem_top`：mem_top (x : M) : x in (⊤ : L.
Substructure M)

--- 原说明 ---
Substructures of a structure form a complete lattice.
-/
instance instCompleteLattice : CompleteLattice (L.Substructure M) :=
  { completeLatticeOfInf (L.Substructure M) fun _ =>
      IsGLB.of_image
        (fun {S T : L.Substructure M} => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· ≤ ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

variable (L)

/-- The `L.Substructure` generated by a set. -/
/-
**FirstOrder.Language.Substructure.closure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：closure : LowerAdjoint ((↑) : L.Substructure M -> Set M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `L.Substructure` generated by a set.
-/
def closure : LowerAdjoint ((↑) : L.Substructure M → Set M) :=
  ⟨fun s => sInf { S | s ⊆ S }, fun _ _ =>
    ⟨Set.Subset.trans fun _x hx => mem_sInf.2 fun _S hS => hS hx, fun h => sInf_le h⟩⟩

variable {L} {s : Set M}
/-
**FirstOrder.Language.Substructure.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：mem_closure {x : M} : x in closure L s ↔ forall S : L.Substructure M, s su
bseteq S -> x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.mem_sInf`：mem_sInf {S : Set (L.Substruc
ture M)} {x : M} : x in sInf S ↔ forall p in S, x in p
-/
theorem mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.Substructure M, s ⊆ S → x ∈ S :=
  mem_sInf

/-- The substructure generated by a set includes the set. -/
@[simp]
/-
**FirstOrder.Language.Substructure.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：subset_closure : s subseteq closure L s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.le_closure`：le_closure (x : α) : x <= u (l x)

--- 原说明 ---
The substructure generated by a set includes the set.
-/
theorem subset_closure : s ⊆ closure L s :=
  (closure L).le_closure s
/-
**FirstOrder.Language.Substructure.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：notMem_of_notMem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s
参数：hP : P ∉ closure L s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
-/
theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h =>
  hP (subset_closure h)

@[simp]
/-
**FirstOrder.Language.Substructure.closed** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：closed (S : L.Substructure M) : (S : Set M) in (closure L).closed
参数：S : L.Substructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LowerAdjoint.eq_of_le`：eq_of_le {s : Set β} {S : α} (h₁ : s subseteq S) 
(h₂ : S <= l s) : l s = S
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Substructure.mem_closure`：mem_closure {x : M} : x in
 closure L s ↔ forall S : L.Substructure M, s subseteq S -> x in S
-/
theorem closed (S : L.Substructure M) : (S : Set M) ∈ (closure L).closed :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun _x xS => mem_closure.2 fun _T hT => hT xS)

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
/-
**FirstOrder.Language.Substructure.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：closure_le : closure L s <= S ↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.closure_le_closed_iff_le`：closure_le_closed_iff_le (x : α) 
{y : α} (hy : y in l.closed) : u (l x) <= y ↔ x <= y
· 使用定理 `FirstOrder.Language.Substructure.closed`：closed (S : L.Substructure M) :
 (S : Set M) in (closure L).closed

--- 原说明 ---
A substructure `S` includes `closure L s` if and only if it includes `s`.
-/
theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
  (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
@[gcongr]
/-
**FirstOrder.Language.Substructure.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : closure L s <= closure L t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.monotone`：monotone : Monotone (u ∘ l)

--- 原说明 ---
Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`.
-/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
  (closure L).monotone h
/-
**FirstOrder.Language.Substructure.closure_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Substructure`。
形式化陈述：closure_eq_of_le (h₁ : s subseteq S) (h₂ : S <= closure L s) : closure L s
 = S
参数：h₁ : s subseteq S；h₂ : S <= closure L s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.eq_of_le`：eq_of_le {s : Set β} {S : α} (h₁ : s subseteq S) 
(h₂ : S <= l s) : l s = S
-/
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂
/-
**FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：coe_closure_eq_range_term_realize : (closure L s : Set M) = range (@Term.r
ealize L _ _ _ ((↑) : s -> M))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `FirstOrder.Language.Substructure.closure_eq_of_le`：closure_eq_of_le (h₁ 
: s subseteq S) (h₂ : S <= closure L s) : closure L s = S
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `FirstOrder.Language.Term.realize_mem`：∀ {L : FirstOrder.Language} {M : T
ype w} [inst : L.Structure M] {S : L.Substructure M} {α : Type u_3} (t : L.Term 
α)   (xs : α → M), (∀ (a :…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_closure_eq_range_term_realize :
    (closure L s : Set M) = range (@Term.realize L _ _ _ ((↑) : s → M)) := by
  let S : L.Substructure M := ⟨range (Term.realize (L := L) ((↑) : s → M)), fun {n} f x hx => by
    simp only [mem_range] at *
    refine ⟨func f fun i => Classical.choose (hx i), ?_⟩
    simp only [Term.realize, fun i => Classical.choose_spec (hx i)]⟩
  change _ = (S : Set M)
  rw [← SetLike.ext'_iff]
  refine closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_sInf fun S' hS' => ?_)
  rintro _ ⟨t, rfl⟩
  exact t.realize_mem _ fun i => hS' i.2
/-
**FirstOrder.Language.Substructure.small_closure** 是 Mathlib 中的一个实例，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：small_closure [Small.{u} s] : Small.{u} (closure L s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize`：coe_
closure_eq_range_term_realize : (closure L s : Set M) = range (@Term.realize L _
 _ _ ((↑) : s -> M))
-/
instance small_closure [Small.{u} s] : Small.{u} (closure L s) := by
  rw [← SetLike.coe_sort_coe, Substructure.coe_closure_eq_range_term_realize]
  exact small_range _
/-
**FirstOrder.Language.Substructure.mem_closure_iff_exists_term** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：mem_closure_iff_exists_term {x : M} : x in closure L s ↔ exists t : L.Term
 s, t.realize ((↑) : s -> M) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize`：coe_
closure_eq_range_term_realize : (closure L s : Set M) = range (@Term.realize L _
 _ _ ((↑) : s -> M))
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closure_iff_exists_term {x : M} :
    x ∈ closure L s ↔ ∃ t : L.Term s, t.realize ((↑) : s → M) = x := by
  rw [← SetLike.mem_coe, coe_closure_eq_range_term_realize, mem_range]
/-
**FirstOrder.Language.Substructure.lift_card_closure_le_card_term** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：lift_card_closure_le_card_term : Cardinal.lift.{max u w} #(closure L s) <=
 #(L.Term s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `FirstOrder.Language.Substructure.coe_closure_eq_range_term_realize`：coe_
closure_eq_range_term_realize : (closure L s : Set M) = range (@Term.realize L _
 _ _ ((↑) : s -> M))
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
-/
theorem lift_card_closure_le_card_term : Cardinal.lift.{max u w} #(closure L s) ≤ #(L.Term s) := by
  rw [← SetLike.coe_sort_coe, coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w, max u w} #(L.Term s)]
  exact Cardinal.mk_range_le_lift
/-
**FirstOrder.Language.Substructure.lift_card_closure_le** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Substructure`。
形式化陈述：lift_card_closure_le : Cardinal.lift.{u, w} #(closure L s) <= max ℵ₀ (Card
inal.lift.{u, w} #s + Cardinal.lift.{w, u} #(Σ i, L.Functions i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `FirstOrder.Language.Substructure.lift_card_closure_le_card_term`：lift_ca
rd_closure_le_card_term : Cardinal.lift.{max u w} #(closure L s) <= #(L.Term s)
· 使用定理 `FirstOrder.Language.Term.card_le`：card_le : #(L.Term α) <= max ℵ₀ #(α op
lus (Σ i, L.Functions i))
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lift_card_closure_le :
    Cardinal.lift.{u, w} #(closure L s) ≤
      max ℵ₀ (Cardinal.lift.{u, w} #s + Cardinal.lift.{w, u} #(Σ i, L.Functions i)) := by
  rw [← lift_umax]
  refine lift_card_closure_le_card_term.trans (Term.card_le.trans ?_)
  rw [mk_sum, lift_umax.{w, u}]
/-
**FirstOrder.Language.Substructure.mem_closed_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：mem_closed_iff (s : Set M) : s in (closure L).closed ↔ forall {n}, forall 
f : L.Functions n, ClosedUnder f s
参数：s : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.fun_mem`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] (self : L.Substructure M) {n : ℕ} (f : L.Funct
ions n),   FirstOrder.Language…
· 使用定理 `FirstOrder.Language.Substructure.closure_eq_of_le`：closure_eq_of_le (h₁ 
: s subseteq S) (h₂ : S <= closure L s) : closure L s = S
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mem_closed_iff (s : Set M) :
    s ∈ (closure L).closed ↔ ∀ {n}, ∀ f : L.Functions n, ClosedUnder f s := by
  refine ⟨fun h n f => ?_, fun h => ?_⟩
  · rw [← h]
    exact Substructure.fun_mem _ _
  · have h' : closure L s = ⟨s, h⟩ := closure_eq_of_le (refl _) subset_closure
    exact congr_arg _ h'

variable (L)
/-
**FirstOrder.Language.Substructure.mem_closed_of_isRelational** 是 Mathlib 中的一个引理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：mem_closed_of_isRelational [L.IsRelational] (s : Set M) : s in (closure L)
.closed
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `FirstOrder.Language.Substructure.mem_closed_iff`：mem_closed_iff (s : Set
 M) : s in (closure L).closed ↔ forall {n}, forall f : L.Functions n, ClosedUnde
r f s
-/
lemma mem_closed_of_isRelational [L.IsRelational] (s : Set M) : s ∈ (closure L).closed :=
  (mem_closed_iff s).2 isEmptyElim

@[simp]
/-
**FirstOrder.Language.Substructure.closure_eq_of_isRelational** 是 Mathlib 中的一个引理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：closure_eq_of_isRelational [L.IsRelational] (s : Set M) : closure L s = s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.closure_eq_self_of_mem_closed`：closure_eq_self_of_mem_close
d {x : α} (h : x in l.closed) : u (l x) = x
· 使用引理 `FirstOrder.Language.Substructure.mem_closed_of_isRelational`：mem_closed_
of_isRelational [L.IsRelational] (s : Set M) : s in (closure L).closed
-/
lemma closure_eq_of_isRelational [L.IsRelational] (s : Set M) : closure L s = s :=
  LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L s)

@[simp]
/-
**FirstOrder.Language.Substructure.mem_closure_iff_of_isRelational** 是 Mathlib 中
的一个引理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：mem_closure_iff_of_isRelational [L.IsRelational] (s : Set M) (m : M) : m i
n closure L s ↔ m in s
参数：s : Set M；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `FirstOrder.Language.Substructure.closure_eq_of_isRelational`：closure_eq_
of_isRelational [L.IsRelational] (s : Set M) : closure L s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_closure_iff_of_isRelational [L.IsRelational] (s : Set M) (m : M) :
    m ∈ closure L s ↔ m ∈ s := by
  rw [← SetLike.mem_coe, closure_eq_of_isRelational]
/-
**FirstOrder.Language.Substructure._root_.Set.Countable.substructure_closure** 是
 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Countable.substructure_closure
    [Countable (Σ l, L.Functions l)] (h : s.Countable) : Countable.{w + 1} (closure L s) := by
  have : Countable s := h.to_subtype
  rw [← mk_le_aleph0_iff, ← lift_le_aleph0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph0

variable {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
/-
**FirstOrder.Language.Substructure.closure_induction** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Substructure`。
形式化陈述：closure_induction {p : M -> Prop} {x} (h : x in closure L s) (Hs : forall 
x in s, p x) (Hfun : forall {n : Nat} (f : L.Functions n), ClosedUnder f (Set.of
Pred p)) : p x
参数：h : x in closure L s；Hs : forall x in s, p x；Hfun : forall {n : Nat} (f : L.F
unctions n), ClosedUnder f (Set.ofPred p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S

--- 原说明 ---
An induction principle for closure membership. If `p` holds for all elements of 
`s`, and
is preserved under function symbols, then `p` holds for all elements of the clos
ure of `s`.
-/
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure L s) (Hs : ∀ x ∈ s, p x)
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (Set.ofPred p)) : p x :=
  (@closure_le L M _ ⟨Set.ofPred p, fun {_} => Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `Substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_elim]
/-
**FirstOrder.Language.Substructure.dense_induction** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Substructure`。
形式化陈述：dense_induction {p : M -> Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
 (Hs : forall x in s, p x) (Hfun : forall {n : Nat} (f : L.Functions n), ClosedU
nder f (Set.ofPred p)) : p x
参数：x : M；hs : closure L s = ⊤；Hs : forall x in s, p x；Hfun : forall {n : Nat} (f
 : L.Functions n), ClosedUnder f (Set.ofPred p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.closure_induction`：closure_induction {p
 : M -> Prop} {x} (h : x in closure L s) (Hs : forall x in s, p x) (Hfun : foral
l {n : Nat} (f : L.Functions n), ClosedU…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `s` is a dense set in a structure `M`, `Substructure.closure L s = ⊤`, then i
n order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x
 ∈ s`, and verify
that `p` is preserved under function symbols.
-/
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
    (Hs : ∀ x ∈ s, p x) (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f (Set.ofPred p)) :
    p x := by
  have : ∀ x ∈ closure L s, p x := fun x hx => closure_induction hx Hs fun {n} => Hfun
  simpa [hs] using this x

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
/-
**FirstOrder.Language.Substructure.gi** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Substructure`。
形式化陈述：(L : FirstOrder.Language) →   (M : Type w) → [inst : L.Structure M] → Galo
isInsertion (FirstOrder.Language.Substructure.closure L).toFun SetLike.coe
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`closure` forms a Galois insertion with the coercion to set.
-/
protected def gi : GaloisInsertion (@closure L M _) (↑) where
  choice s _ := closure L s
  gc := (closure L).gc
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
/-
**FirstOrder.Language.Substructure.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：closure_eq : closure L (S : Set M) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b

--- 原说明 ---
Closure of a substructure `S` equals `S`.
-/
theorem closure_eq : closure L (S : Set M) = S :=
  (Substructure.gi L M).l_u_eq S

@[simp]
/-
**FirstOrder.Language.Substructure.closure_empty** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：closure_empty : closure L (∅ : Set M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (Substructure.gi L M).gc.l_bot

@[simp]
/-
**FirstOrder.Language.Substructure.closure_univ** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：closure_univ : closure L (univ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
· 使用定理 `FirstOrder.Language.Substructure.coe_top`：coe_top : ((⊤ : L.Substructure
 M) : Set M) = Set.univ
-/
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤
/-
**FirstOrder.Language.Substructure.closure_union** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：closure_union (s t : Set M) : closure L (s union t) = closure L s ⊔ closur
e L t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_union (s t : Set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
  (Substructure.gi L M).gc.l_sup
/-
**FirstOrder.Language.Substructure.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：closure_iUnion {ι} (s : ι -> Set M) : closure L (⋃ i, s i) = ⨆ i, closure 
L (s i)
参数：s : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem closure_iUnion {ι} (s : ι → Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (Substructure.gi L M).gc.l_iSup
/-
**FirstOrder.Language.Substructure.closure_insert** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：closure_insert (s : Set M) (m : M) : closure L (insert m s) = closure L {m
} ⊔ closure L s
参数：s : Set M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.closure_union`：closure_union (s t : Set
 M) : closure L (s union t) = closure L s ⊔ closure L t
-/
theorem closure_insert (s : Set M) (m : M) : closure L (insert m s) = closure L {m} ⊔ closure L s :=
  closure_union {m} s
/-
**FirstOrder.Language.Substructure.small_bot** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language.Substructure`。
形式化陈述：small_bot : Small.{u} (⊥ : L.Substructure M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.closure_empty`：closure_empty : closure 
L (∅ : Set M) = ⊥
· 使用定理 `small_subsingleton`：∀ (α : Type v) [Subsingleton α], Small.{w, v} α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
instance small_bot : Small.{u} (⊥ : L.Substructure M) := by
  rw [← closure_empty]
  have : Small.{u} (∅ : Set M) := small_subsingleton _
  exact Substructure.small_closure
/-
**FirstOrder.Language.Substructure.iSup_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Substructure`。
形式化陈述：iSup_eq_closure {ι : Sort*} (S : ι -> L.Substructure M) : ⨆ i, S i = closu
re L (⋃ i, (S i : Set M))
参数：S : ι -> L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.closure_iUnion`：closure_iUnion {ι} (s :
 ι -> Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_eq_closure {ι : Sort*} (S : ι → L.Substructure M) :
    ⨆ i, S i = closure L (⋃ i, (S i : Set M)) := by simp_rw [closure_iUnion, closure_eq]

-- This proof uses the fact that `Substructure.closure` is finitary.
/-
**FirstOrder.Language.Substructure.mem_iSup_of_directed** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Substructure`。
形式化陈述：mem_iSup_of_directed {ι : Type*} [hι : Nonempty ι] {S : ι -> L.Substructur
e M} (hS : Directed (· <= ·) S) {x : M} : x in ⨆ i, S i ↔ exists i, x in S i
参数：hS : Directed (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.closure_induction`：closure_induction {p
 : M -> Prop} {x} (h : x in closure L s) (Hs : forall x in s, p x) (Hfun : foral
l {n : Nat} (f : L.Functions n), ClosedU…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Directed.finite_le`：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finit
e κ] {f : ι -> α} (hf : Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g
 i)) (f …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FirstOrder.Language.Substructure.fun_mem`：∀ {L : FirstOrder.Language} {M
 : Type w} [inst : L.Structure M] (self : L.Substructure M) {n : ℕ} (f : L.Funct
ions n),   FirstOrder.Language…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Substructure.closure_iUnion`：closure_iUnion {ι} (s :
 ι -> Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem mem_iSup_of_directed {ι : Type*} [hι : Nonempty ι] {S : ι → L.Substructure M}
    (hS : Directed (· ≤ ·) S) {x : M} :
    x ∈ ⨆ i, S i ↔ ∃ i, x ∈ S i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup S i hi⟩
  suffices x ∈ closure L (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx ↦ closure_induction hx (fun _ ↦ mem_iUnion.1) (fun f v hC ↦ ?_)
  simp_rw [Set.mem_ofPred] at *
  have ⟨i, hi⟩ := hS.finite_le (fun i ↦ Classical.choose (hC i))
  refine ⟨i, (S i).fun_mem f v (fun j ↦ hi j (Classical.choose_spec (hC j)))⟩

-- This proof uses the fact that `Substructure.closure` is finitary.
/-
**FirstOrder.Language.Substructure.mem_sSup_of_directedOn** 是 Mathlib 中的一个定理，位于命
名空间 `FirstOrder.Language.Substructure`。
形式化陈述：mem_sSup_of_directedOn {S : Set (L.Substructure M)} (Sne : S.Nonempty) (hS
 : DirectedOn (· <= ·) S) {x : M} : x in sSup S ↔ exists s in S, x in s
参数：L.Substructure M；Sne : S.Nonempty；hS : DirectedOn (· <= ·) S。
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
· 使用定理 `FirstOrder.Language.Substructure.mem_iSup_of_directed`：mem_iSup_of_direc
ted {ι : Type*} [hι : Nonempty ι] {S : ι -> L.Substructure M} (hS : Directed (· 
<= ·) S) {x : M} : x in ⨆ i, S i ↔ exists i…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup_of_directedOn {S : Set (L.Substructure M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} :
    x ∈ sSup S ↔ ∃ s ∈ S, x ∈ s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

variable (L) (M)
/-
**FirstOrder.Language.Substructure.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.Substructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty L.Constants] : IsEmpty (⊥ : L.Substructure M) := by
  refine (isEmpty_subtype _).2 (fun x => ?_)
  have h : (∅ : Set M) ∈ (closure L).closed := by
    rw [mem_closed_iff]
    intro n f
    cases n
    · exact isEmptyElim f
    · intro x hx
      simp only [mem_empty_iff_false, forall_const] at hx
  rw [← closure_empty, ← SetLike.mem_coe, h]
  exact Set.notMem_empty _

variable {L} {M}

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
/-
**FirstOrder.Language.Substructure.comap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.Substructure`。
形式化陈述：comap (φ : M ->[L] N) (S : L.Substructure N) : L.Substructure M where carr
ier
参数：φ : M ->[L] N；S : L.Substructure N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a substructure along a homomorphism is a substructure.
-/
def comap (φ : M →[L] N) (S : L.Substructure N) : L.Substructure M where
  carrier := φ ⁻¹' S
  fun_mem {n} f x hx := by
    rw [mem_preimage, φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
/-
**FirstOrder.Language.Substructure.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Substructure`。
形式化陈述：mem_comap {S : L.Substructure N} {f : M ->[L] N} {x : M} : x in S.comap f 
↔ f x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {S : L.Substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
/-
**FirstOrder.Language.Substructure.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：comap_comap (S : L.Substructure P) (g : N ->[L] P) (f : M ->[L] N) : (S.co
map g).comap f = S.comap (g.comp f)
参数：S : L.Substructure P；g : N ->[L] P；f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (S : L.Substructure P) (g : N →[L] P) (f : M →[L] N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Substructure.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S
参数：S : L.Substructure P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.ext`：ext {S T : L.Substructure M} (h : 
forall x, x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S :=
  ext (by simp)

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
/-
**FirstOrder.Language.Substructure.map** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lan
guage.Substructure`。
形式化陈述：map (φ : M ->[L] N) (S : L.Substructure M) : L.Substructure N where carrie
r
参数：φ : M ->[L] N；S : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a substructure along a homomorphism is a substructure.
-/
def map (φ : M →[L] N) (S : L.Substructure M) : L.Substructure N where
  carrier := φ '' S
  fun_mem {n} f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1, by
        simp only [Hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩

@[simp]
/-
**FirstOrder.Language.Substructure.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：mem_map {f : M ->[L] N} {S : L.Substructure M} {y : N} : y in S.map f ↔ ex
ists x in S, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : M →[L] N} {S : L.Substructure M} {y : N} :
    y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  Iff.rfl
/-
**FirstOrder.Language.Substructure.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：mem_map_of_mem (f : M ->[L] N) {S : L.Substructure M} {x : M} (hx : x in S
) : f x in S.map f
参数：f : M ->[L] N；hx : x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem (f : M →[L] N) {S : L.Substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx
/-
**FirstOrder.Language.Substructure.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Substructure`。
形式化陈述：apply_coe_mem_map (f : M ->[L] N) (S : L.Substructure M) (x : S) : f x in 
S.map f
参数：f : M ->[L] N；S : L.Substructure M；x : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.mem_map_of_mem`：mem_map_of_mem (f : M -
>[L] N) {S : L.Substructure M} {x : M} (hx : x in S) : f x in S.map f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem apply_coe_mem_map (f : M →[L] N) (S : L.Substructure M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop
/-
**FirstOrder.Language.Substructure.map_map** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：map_map (g : N ->[L] P) (f : M ->[L] N) : (S.map f).map g = S.map (g.comp 
f)
参数：g : N ->[L] P；f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _
/-
**FirstOrder.Language.Substructure.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure`。
形式化陈述：map_le_iff_le_comap {f : M ->[L] N} {S : L.Substructure M} {T : L.Substruc
ture N} : S.map f <= T ↔ S <= T.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : M →[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff
/-
**FirstOrder.Language.Substructure.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：gc_map_comap (f : M ->[L] N) : GaloisConnection (map f) (comap f)
参数：f : M ->[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.map_le_iff_le_comap`：map_le_iff_le_coma
p {f : M ->[L] N} {S : L.Substructure M} {T : L.Substructure N} : S.map f <= T ↔
 S <= T.comap f
-/
theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap
/-
**FirstOrder.Language.Substructure.map_le_of_le_comap** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Substructure`。
形式化陈述：map_le_of_le_comap {T : L.Substructure N} {f : M ->[L] N} : S <= T.comap f
 -> S.map f <= T
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_le_of_le_comap {T : L.Substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le
/-
**FirstOrder.Language.Substructure.le_comap_of_map_le** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Substructure`。
形式化陈述：le_comap_of_map_le {T : L.Substructure N} {f : M ->[L] N} : S.map f <= T -
> S <= T.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ {a : α}
 {b : β}, l…
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem le_comap_of_map_le {T : L.Substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u
/-
**FirstOrder.Language.Substructure.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：le_comap_map {f : M ->[L] N} : S <= (S.map f).comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _
/-
**FirstOrder.Language.Substructure.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：map_comap_le {S : L.Substructure N} {f : M ->[L] N} : (S.comap f).map f <=
 S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_comap_le {S : L.Substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _
/-
**FirstOrder.Language.Substructure.monotone_map** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：monotone_map {f : M ->[L] N} : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l
/-
**FirstOrder.Language.Substructure.monotone_comap** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：monotone_comap {f : M ->[L] N} : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
/-
**FirstOrder.Language.Substructure.map_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：map_comap_map {f : M ->[L] N} : ((S.map f).comap f).map f = S.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
/-
**FirstOrder.Language.Substructure.comap_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Substructure`。
形式化陈述：comap_map_comap {S : L.Substructure N} {f : M ->[L] N} : ((S.comap f).map 
f).comap f = S.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem comap_map_comap {S : L.Substructure N} {f : M →[L] N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _
/-
**FirstOrder.Language.Substructure.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：map_sup (S T : L.Substructure M) (f : M ->[L] N) : (S ⊔ T).map f = S.map f
 ⊔ T.map f
参数：S T : L.Substructure M；f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_sup (S T : L.Substructure M) (f : M →[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup
/-
**FirstOrder.Language.Substructure.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：map_iSup {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure M) : (⨆ i, s
 i).map f = ⨆ i, (s i).map f
参数：f : M ->[L] N；s : ι -> L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_iSup {ι : Sort*} (f : M →[L] N) (s : ι → L.Substructure M) :
    (⨆ i, s i).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup
/-
**FirstOrder.Language.Substructure.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Substructure`。
形式化陈述：comap_inf (S T : L.Substructure N) (f : M ->[L] N) : (S ⊓ T).comap f = S.c
omap f ⊓ T.comap f
参数：S T : L.Substructure N；f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem comap_inf (S T : L.Substructure N) (f : M →[L] N) :
    (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf
/-
**FirstOrder.Language.Substructure.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：comap_iInf {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure N) : (⨅ i,
 s i).comap f = ⨅ i, (s i).comap f
参数：f : M ->[L] N；s : ι -> L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem comap_iInf {ι : Sort*} (f : M →[L] N) (s : ι → L.Substructure N) :
    (⨅ i, s i).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/-
**FirstOrder.Language.Substructure.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：map_bot (f : M ->[L] N) : (⊥ : L.Substructure M).map f = ⊥
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem map_bot (f : M →[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**FirstOrder.Language.Substructure.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Substructure`。
形式化陈述：comap_top (f : M ->[L] N) : (⊤ : L.Substructure N).comap f = ⊤
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)
-/
theorem comap_top (f : M →[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
/-
**FirstOrder.Language.Substructure.map_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：map_id (S : L.Substructure M) : S.map (Hom.id L M) = S
参数：S : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S :=
  SetLike.coe_injective <| Set.image_id _
/-
**FirstOrder.Language.Substructure.map_closure** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：map_closure (f : M ->[L] N) (s : Set M) : (closure L s).map f = closure L 
(f '' s)
参数：f : M ->[L] N；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.closure_eq_of_le`：closure_eq_of_le (h₁ 
: s subseteq S) (h₂ : S <= closure L s) : closure L s = S
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Substructure.map_le_iff_le_comap`：map_le_iff_le_coma
p {f : M ->[L] N} {S : L.Substructure M} {T : L.Substructure N} : S.map f <= T ↔
 S <= T.comap f
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S
-/
theorem map_closure (f : M →[L] N) (s : Set M) : (closure L s).map f = closure L (f '' s) :=
  Eq.symm <|
    closure_eq_of_le (Set.image_mono subset_closure) <|
      map_le_iff_le_comap.2 <| closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]
/-
**FirstOrder.Language.Substructure.closure_image** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：closure_image (f : M ->[L] N) : closure L (f '' s) = map f (closure L s)
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.map_closure`：map_closure (f : M ->[L] N
) (s : Set M) : (closure L s).map f = closure L (f '' s)
-/
theorem closure_image (f : M →[L] N) : closure L (f '' s) = map f (closure L s) :=
  (map_closure f s).symm

section GaloisCoinsertion

variable {ι : Type*} {f : M →[L] N}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
/-
**FirstOrder.Language.Substructure.gciMapComap** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap
 f)
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.
-/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf
/-
**FirstOrder.Language.Substructure.comap_map_eq_of_injective** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S
参数：S : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _
/-
**FirstOrder.Language.Substructure.comap_surjective_of_injective** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_surjective_of_injective : Function.Surjective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
/-
**FirstOrder.Language.Substructure.map_injective_of_injective** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_injective_of_injective : Function.Injective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
/-
**FirstOrder.Language.Substructure.comap_inf_map_of_injective** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f ⊓ T.map f).
comap f = S ⊓ T
参数：S T : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _
/-
**FirstOrder.Language.Substructure.comap_iInf_map_of_injective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_iInf_map_of_injective (S : ι -> L.Substructure M) : (⨅ i, (S i).map 
f).comap f = ⨅ i, S i
参数：S : ι -> L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iInf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iInf_map_of_injective (S : ι → L.Substructure M) :
    (⨅ i, (S i).map f).comap f = ⨅ i, S i :=
  (gciMapComap hf).u_iInf_l _
/-
**FirstOrder.Language.Substructure.comap_sup_map_of_injective** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f ⊔ T.map f).
comap f = S ⊔ T
参数：S T : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _
/-
**FirstOrder.Language.Substructure.comap_iSup_map_of_injective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_iSup_map_of_injective (S : ι -> L.Substructure M) : (⨆ i, (S i).map 
f).comap f = ⨆ i, S i
参数：S : ι -> L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iSup_map_of_injective (S : ι → L.Substructure M) :
    (⨆ i, (S i).map f).comap f = ⨆ i, S i :=
  (gciMapComap hf).u_iSup_l _
/-
**FirstOrder.Language.Substructure.map_le_map_iff_of_injective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f <= T.map f 
↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
theorem map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff
/-
**FirstOrder.Language.Substructure.map_strictMono_of_injective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_strictMono_of_injective : StrictMono (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M →[L] N} (hf : Function.Surjective f)
include hf

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
/-
**FirstOrder.Language.Substructure.giMapComap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：giMapComap : GaloisInsertion (map f) (comap f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.gc_map_comap`：gc_map_comap (f : M ->[L]
 N) : GaloisConnection (map f) (comap f)

--- 原说明 ---
`map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩
/-
**FirstOrder.Language.Substructure.map_comap_eq_of_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S
参数：S : L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _
/-
**FirstOrder.Language.Substructure.map_surjective_of_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_surjective_of_surjective : Function.Surjective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
/-
**FirstOrder.Language.Substructure.comap_injective_of_surjective** 是 Mathlib 中的一
个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_injective_of_surjective : Function.Injective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
/-
**FirstOrder.Language.Substructure.map_inf_comap_of_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_inf_comap_of_surjective (S T : L.Substructure N) : (S.comap f ⊓ T.coma
p f).map f = S ⊓ T
参数：S T : L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem map_inf_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _
/-
**FirstOrder.Language.Substructure.map_iInf_comap_of_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_iInf_comap_of_surjective (S : ι -> L.Substructure N) : (⨅ i, (S i).com
ap f).map f = ⨅ i, S i
参数：S : ι -> L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem map_iInf_comap_of_surjective (S : ι → L.Substructure N) :
    (⨅ i, (S i).comap f).map f = ⨅ i, S i :=
  (giMapComap hf).l_iInf_u _
/-
**FirstOrder.Language.Substructure.map_sup_comap_of_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_sup_comap_of_surjective (S T : L.Substructure N) : (S.comap f ⊔ T.coma
p f).map f = S ⊔ T
参数：S T : L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem map_sup_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _
/-
**FirstOrder.Language.Substructure.map_iSup_comap_of_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：map_iSup_comap_of_surjective (S : ι -> L.Substructure N) : (⨆ i, (S i).com
ap f).map f = ⨆ i, S i
参数：S : ι -> L.Substructure N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem map_iSup_comap_of_surjective (S : ι → L.Substructure N) :
    (⨆ i, (S i).comap f).map f = ⨆ i, S i :=
  (giMapComap hf).l_iSup_u _
/-
**FirstOrder.Language.Substructure.comap_le_comap_iff_of_surjective** 是 Mathlib 
中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f <= T
.comap f ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
-/
theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff
/-
**FirstOrder.Language.Substructure.comap_strictMono_of_surjective** 是 Mathlib 中的
一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：comap_strictMono_of_surjective : StrictMono (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.strictMono_u`：strictMono_u [Preorder α] [Preorder β] (gi
 : GaloisInsertion l u) : StrictMono u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

/-
**FirstOrder.Language.Substructure.inducedStructure** 是 Mathlib 中的一个实例，位于命名空间 `F
irstOrder.Language.Substructure`。
形式化陈述：inducedStructure {S : L.Substructure M} : L.Structure S where funMap {_} f
 x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inducedStructure {S : L.Substructure M} : L.Structure S where
  funMap {_} f x := ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap {_} r x := RelMap r fun i => (x i : M)

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
/-
**FirstOrder.Language.Substructure.subtype** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Substructure`。
形式化陈述：subtype (S : L.Substructure M) : S ↪[L] M where toFun
参数：S : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural embedding of an `L.Substructure` of `M` into `M`.
-/
def subtype (S : L.Substructure M) : S ↪[L] M where
  toFun := (↑)
  inj' := Subtype.coe_injective

@[simp]
/-
**FirstOrder.Language.Substructure.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：subtype_apply {S : L.Substructure M} {x : S} : subtype S x = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply {S : L.Substructure M} {x : S} : subtype S x = x :=
  rfl
/-
**FirstOrder.Language.Substructure.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Substructure`。
形式化陈述：subtype_injective (S : L.Substructure M) : Function.Injective (subtype S)
参数：S : L.Substructure M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective (S : L.Substructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
/-
**FirstOrder.Language.Substructure.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Substructure`。
形式化陈述：coe_subtype : ⇑S.subtype = ((↑) : S -> M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : ⇑S.subtype = ((↑) : S → M) :=
  rfl

/-- The equivalence between the maximal substructure of a structure and the structure itself. -/
/-
**FirstOrder.Language.Substructure.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Substructure`。
形式化陈述：topEquiv : (⊤ : L.Substructure M) ≃[L] M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.mem_top`：mem_top (x : M) : x in (⊤ : L.
Substructure M)

--- 原说明 ---
The equivalence between the maximal substructure of a structure and the structur
e itself.
-/
def topEquiv : (⊤ : L.Substructure M) ≃[L] M where
  toFun := subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp

@[simp]
/-
**FirstOrder.Language.Substructure.coe_topEquiv** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure`。
形式化陈述：coe_topEquiv : ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = ((↑) : (⊤ : L
.Substructure M) -> M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_topEquiv :
    ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = ((↑) : (⊤ : L.Substructure M) → M) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Substructure.realize_boundedFormula_top** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：realize_boundedFormula_top {α : Type*} {n : Nat} {φ : L.BoundedFormula α n
} {v : α -> (⊤ : L.Substructure M)} {xs : Fin n -> (⊤ : L.Substructure M)} : φ.R
ealize v xs ↔ φ.Realize (((↑) : _ -> M) ∘ v) ((↑) ∘ xs)
参数：⊤ : L.Substructure M；⊤ : L.Substructure M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_boundedFormula`：realize_bound
edFormula (φ : L.BoundedFormula α n) {v : α -> M} {xs : Fin n -> M} : φ.Realize 
(g ∘ v) (g ∘ xs) ↔ φ.Realize v xs
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_boundedFormula_top {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    {v : α → (⊤ : L.Substructure M)} {xs : Fin n → (⊤ : L.Substructure M)} :
    φ.Realize v xs ↔ φ.Realize (((↑) : _ → M) ∘ v) ((↑) ∘ xs) := by
  rw [← StrongHomClass.realize_boundedFormula Substructure.topEquiv φ]
  simp

@[simp]
/-
**FirstOrder.Language.Substructure.realize_formula_top** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure`。
形式化陈述：realize_formula_top {α : Type*} {φ : L.Formula α} {v : α -> (⊤ : L.Substru
cture M)} : φ.Realize v ↔ φ.Realize (((↑) : (⊤ : L.Substructure M) -> M) ∘ v)
参数：⊤ : L.Substructure M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.StrongHomClass.realize_formula`：realize_formula (φ :
 L.Formula α) {v : α -> M} : φ.Realize (g ∘ v) ↔ φ.Realize v
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_formula_top {α : Type*} {φ : L.Formula α} {v : α → (⊤ : L.Substructure M)} :
    φ.Realize v ↔ φ.Realize (((↑) : (⊤ : L.Substructure M) → M) ∘ v) := by
  rw [← StrongHomClass.realize_formula Substructure.topEquiv φ]
  simp

/-- A dependent version of `Substructure.closure_induction`. -/
@[elab_as_elim]
/-
**FirstOrder.Language.Substructure.closure_induction'** 是 Mathlib 中的一个定理，位于命名空间 
`FirstOrder.Language.Substructure`。
形式化陈述：closure_induction' (s : Set M) {p : forall x, x in closure L s -> Prop} (H
s : forall (x) (h : x in s), p x (subset_closure h)) (Hfun : forall {n : Nat} (f
 : L.Functions n), ClosedUnder f { x | exists hx, p x hx }) {x} (hx : x in closu
re L s) : p x hx
参数：s : Set M；Hs : forall (x) (h : x in s), p x (subset_closure h)；Hfun : forall 
{n : Nat} (f : L.Functions n), ClosedUnder f { x | exists hx, p x hx }；hx : x in
 closure L s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `FirstOrder.Language.Substructure.closure_induction`：closure_induction {p
 : M -> Prop} {x} (h : x in closure L s) (Hs : forall x in s, p x) (Hfun : foral
l {n : Nat} (f : L.Functions n), ClosedU…

--- 原说明 ---
A dependent version of `Substructure.closure_induction`.
-/
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure L s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h))
    (Hfun : ∀ {n : ℕ} (f : L.Functions n), ClosedUnder f { x | ∃ hx, p x hx }) {x}
    (hx : x ∈ closure L s) : p x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

end Substructure

open Substructure

namespace LHom

variable {L' : Language} [L'.Structure M]

set_option backward.isDefEq.respectTransparency false in
/-- Reduces the language of a substructure along a language hom. -/
/-
**FirstOrder.Language.LHom.substructureReduct** 是 Mathlib 中的一个定义，位于命名空间 `FirstOr
der.Language.LHom`。
形式化陈述：substructureReduct (φ : L ->ᴸ L') [φ.IsExpansionOn M] : L'.Substructure M 
↪o L.Substructure M where toFun S
参数：φ : L ->ᴸ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reduces the language of a substructure along a language hom.
-/
def substructureReduct (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    L'.Substructure M ↪o L.Substructure M where
  toFun S :=
    { carrier := S
      fun_mem := fun {n} f x hx => by
        have h := S.fun_mem (φ.onFunction f) x hx
        simp only [LHom.map_onFunction, Substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq, Substructure.mk.injEq] at h
    exact h
  map_rel_iff' {_ _} := Iff.rfl

variable (φ : L →ᴸ L') [φ.IsExpansionOn M]

@[simp]
/-
**FirstOrder.Language.LHom.mem_substructureReduct** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.LHom`。
形式化陈述：mem_substructureReduct {x : M} {S : L'.Substructure M} : x in φ.substructu
reReduct S ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_substructureReduct {x : M} {S : L'.Substructure M} :
    x ∈ φ.substructureReduct S ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.LHom.coe_substructureReduct** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.LHom`。
形式化陈述：coe_substructureReduct {S : L'.Substructure M} : (φ.substructureReduct S :
 Set M) = ↑S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_substructureReduct {S : L'.Substructure M} : (φ.substructureReduct S : Set M) = ↑S :=
  rfl

end LHom

namespace Substructure

/-- Turns any substructure containing a constant set `A` into a `L[[A]]`-substructure. -/
/-
**FirstOrder.Language.Substructure.withConstants** 是 Mathlib 中的一个定义，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：withConstants (S : L.Substructure M) {A : Set M} (h : A subseteq S) : L[[A
]].Substructure M where carrier
参数：S : L.Substructure M；h : A subseteq S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns any substructure containing a constant set `A` into a `L[[A]]`-substructur
e.
-/
def withConstants (S : L.Substructure M) {A : Set M} (h : A ⊆ S) : L[[A]].Substructure M where
  carrier := S
  fun_mem {n} f := by
    obtain f | f := f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f

variable {A : Set M} {s : Set M} (h : A ⊆ S)

@[simp]
/-
**FirstOrder.Language.Substructure.mem_withConstants** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Substructure`。
形式化陈述：mem_withConstants {x : M} : x in S.withConstants h ↔ x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_withConstants {x : M} : x ∈ S.withConstants h ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.Substructure.coe_withConstants** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Substructure`。
形式化陈述：coe_withConstants : (S.withConstants h : Set M) = ↑S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_withConstants : (S.withConstants h : Set M) = ↑S :=
  rfl

@[simp]
/-
**FirstOrder.Language.Substructure.reduct_withConstants** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Substructure`。
形式化陈述：reduct_withConstants : (L.lhomWithConstants A).substructureReduct (S.withC
onstants h) = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.ext`：ext {S T : L.Substructure M} (h : 
forall x, x in S ↔ x in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reduct_withConstants :
    (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S := by
  ext
  simp
/-
**FirstOrder.Language.Substructure.subset_closure_withConstants** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：subset_closure_withConstants : A subseteq closure L[[A]] s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.constants_mem`：constants_mem (c : L.Con
stants) : (c : M) in S
-/
theorem subset_closure_withConstants : A ⊆ closure L[[A]] s := by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'
/-
**FirstOrder.Language.Substructure.closure_withConstants_eq** 是 Mathlib 中的一个定理，位
于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：closure_withConstants_eq : closure L[[A]] s = (closure L (A union s)).with
Constants ((A.subset_union_left).trans subset_closure)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.closure_eq_of_le`：closure_eq_of_le (h₁ 
: s subseteq S) (h₂ : S <= closure L s) : closure L s = S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.Substructure.reduct_withConstants`：reduct_withConsta
nts : (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `FirstOrder.Language.Substructure.subset_closure_withConstants`：subset_cl
osure_withConstants : A subseteq closure L[[A]] s
-/
theorem closure_withConstants_eq :
    closure L[[A]] s =
      (closure L (A ∪ s)).withConstants ((A.subset_union_left).trans subset_closure) := by
  refine closure_eq_of_le ((A.subset_union_right).trans subset_closure) ?_
  rw [← (L.lhomWithConstants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_withConstants, closure_le, LHom.coe_substructureReduct,
    Set.union_subset_iff, and_true]
  exact subset_closure_withConstants

end Substructure

namespace Hom

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps!]
/-
**FirstOrder.Language.Hom.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Hom`。
形式化陈述：domRestrict (f : M ->[L] N) (p : L.Substructure M) : p ->[L] N
参数：f : M ->[L] N；p : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → 
N`.
-/
def domRestrict (f : M →[L] N) (p : L.Substructure M) : p →[L] N :=
  f.comp p.subtype.toHom

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps]
/-
**FirstOrder.Language.Hom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Hom`。
形式化陈述：codRestrict (p : L.Substructure N) (f : M ->[L] N) (h : forall c, f c in p
) : M ->[L] p where toFun c
参数：p : L.Substructure N；f : M ->[L] N；h : forall c, f c in p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.map_rel`：map_rel (φ : M ->[L] N) {n : Nat} (r : 
L.Relations n) (x : Fin n -> M) : RelMap r x -> RelMap r (φ ∘ x)

--- 原说明 ---
A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be 
restricted to a
hom `M → p`.
-/
def codRestrict (p : L.Substructure N) (f : M →[L] N) (h : ∀ c, f c ∈ p) : M →[L] p where
  toFun c := ⟨f c, h c⟩
  map_fun' {n} f x := by aesop
  map_rel' {_} R x h := f.map_rel R x h

@[simp]
/-
**FirstOrder.Language.Hom.comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Hom`。
形式化陈述：comp_codRestrict (f : M ->[L] N) (g : N ->[L] P) (p : L.Substructure P) (h
 : forall b, g b in p) : ((codRestrict p g h).comp f : M ->[L] p) = codRestrict 
p (g.comp f) fun _ => h _
参数：f : M ->[L] N；g : N ->[L] P；p : L.Substructure P；h : forall b, g b in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.ext`：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = 
g x) : f = g
-/
theorem comp_codRestrict (f : M →[L] N) (g : N →[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
/-
**FirstOrder.Language.Hom.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Hom`。
形式化陈述：subtype_comp_codRestrict (f : M ->[L] N) (p : L.Substructure N) (h : foral
l b, f b in p) : p.subtype.toHom.comp (codRestrict p f h) = f
参数：f : M ->[L] N；p : L.Substructure N；h : forall b, f b in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.ext`：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = 
g x) : f = g
-/
theorem subtype_comp_codRestrict (f : M →[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.subtype.toHom.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

@[simp]
/-
**FirstOrder.Language.Hom.domRestrict_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Hom`。
形式化陈述：domRestrict_comp_codRestrict (g : N ->[L] P) (f : M ->[L] N) (p : L.Substr
ucture N) (h : forall b, f b in p) : (g.domRestrict p).comp (f.codRestrict p h) 
= g.comp f
参数：g : N ->[L] P；f : M ->[L] N；p : L.Substructure N；h : forall b, f b in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_comp_codRestrict (g : N →[L] P) (f : M →[L] N) (p : L.Substructure N)
    (h : ∀ b, f b ∈ p) :
    (g.domRestrict p).comp (f.codRestrict p h) = g.comp f :=
  rfl

/-- The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern]. -/
/-
**FirstOrder.Language.Hom.range** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.H
om`。
形式化陈述：range (f : M ->[L] N) : L.Substructure N
参数：f : M ->[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern].
-/
def range (f : M →[L] N) : L.Substructure N :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
/-
**FirstOrder.Language.Hom.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Hom`。
形式化陈述：range_coe (f : M ->[L] N) : (range f : Set N) = Set.range f
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_coe (f : M →[L] N) : (range f : Set N) = Set.range f :=
  rfl

@[simp]
/-
**FirstOrder.Language.Hom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Hom`。
形式化陈述：mem_range {f : M ->[L] N} {x} : x in range f ↔ exists y, f y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range {f : M →[L] N} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
/-
**FirstOrder.Language.Hom.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Hom`。
形式化陈述：range_eq_map (f : M ->[L] N) : f.range = map f ⊤
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.ext`：ext {S T : L.Substructure M} (h : 
forall x, x in S ↔ x in T) : S = T
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
theorem range_eq_map (f : M →[L] N) : f.range = map f ⊤ := by
  ext
  simp
/-
**FirstOrder.Language.Hom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Hom`。
形式化陈述：mem_range_self (f : M ->[L] N) (x : M) : f x in f.range
参数：f : M ->[L] N；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_self (f : M →[L] N) (x : M) : f x ∈ f.range :=
  ⟨x, rfl⟩

@[simp]
/-
**FirstOrder.Language.Hom.range_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.Hom`。
形式化陈述：range_id : range (id L M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id : range (id L M) = ⊤ :=
  SetLike.coe_injective Set.range_id
/-
**FirstOrder.Language.Hom.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Hom`。
形式化陈述：range_comp (f : M ->[L] N) (g : N ->[L] P) : range (g.comp f : M ->[L] P) 
= map g (range f)
参数：f : M ->[L] N；g : N ->[L] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_comp (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)
/-
**FirstOrder.Language.Hom.range_comp_le_range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Hom`。
形式化陈述：range_comp_le_range (f : M ->[L] N) (g : N ->[L] P) : range (g.comp f : M 
->[L] P) <= range g
参数：f : M ->[L] N；g : N ->[L] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
/-
**FirstOrder.Language.Hom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Hom`。
形式化陈述：range_eq_top {f : M ->[L] N} : range f = ⊤ ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `FirstOrder.Language.Hom.range_coe`：range_coe (f : M ->[L] N) : (range f 
: Set N) = Set.range f
· 使用定理 `FirstOrder.Language.Substructure.coe_top`：coe_top : ((⊤ : L.Substructure
 M) : Set M) = Set.univ
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq_top {f : M →[L] N} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, range_coe, coe_top, Set.range_eq_univ]
/-
**FirstOrder.Language.Hom.range_le_iff_comap** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Hom`。
形式化陈述：range_le_iff_comap {f : M ->[L] N} {p : L.Substructure N} : range f <= p ↔
 comap f p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `FirstOrder.Language.Substructure.map_le_iff_le_comap`：map_le_iff_le_coma
p {f : M ->[L] N} {S : L.Substructure M} {T : L.Substructure N} : S.map f <= T ↔
 S <= T.comap f
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_le_iff_comap {f : M →[L] N} {p : L.Substructure N} : range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
/-
**FirstOrder.Language.Hom.map_le_range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Hom`。
形式化陈述：map_le_range {f : M ->[L] N} {p : L.Substructure M} : map f p <= range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem map_le_range {f : M →[L] N} {p : L.Substructure M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

/-- The substructure of elements `x : M` such that `f x = g x` -/
/-
**FirstOrder.Language.Hom.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.Hom`。
形式化陈述：eqLocus (f g : M ->[L] N) : Substructure L M where carrier
参数：f g : M ->[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The substructure of elements `x : M` such that `f x = g x`
-/
def eqLocus (f g : M →[L] N) : Substructure L M where
  carrier := { x : M | f x = g x }
  fun_mem {n} fn x hx := by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]

@[simp]
/-
**FirstOrder.Language.Hom.mem_eqLocus** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Hom`。
形式化陈述：mem_eqLocus {f g : M ->[L] N} {x : M} : x in f.eqLocus g ↔ f x = g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_eqLocus {f g : M →[L] N} {x : M} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

/-- If two `L.Hom`s are equal on a set, then they are equal on its substructure closure. -/
/-
**FirstOrder.Language.Hom.eqOn_closure** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Hom`。
形式化陈述：eqOn_closure {f g : M ->[L] N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn
 f g (closure L s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S

--- 原说明 ---
If two `L.Hom`s are equal on a set, then they are equal on its substructure clos
ure.
-/
theorem eqOn_closure {f g : M →[L] N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure L s) :=
  show closure L s ≤ f.eqLocus g from closure_le.2 h
/-
**FirstOrder.Language.Hom.eq_of_eqOn_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Hom`。
形式化陈述：eq_of_eqOn_top {f g : M ->[L] N} (h : Set.EqOn f g (⊤ : Substructure L M))
 : f = g
参数：h : Set.EqOn f g (⊤ : Substructure L M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.ext`：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = 
g x) : f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_top {f g : M →[L] N} (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g :=
  ext fun _ => h trivial

variable {s : Set M}
/-
**FirstOrder.Language.Hom.eq_of_eqOn_dense** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Hom`。
形式化陈述：eq_of_eqOn_dense (hs : closure L s = ⊤) {f g : M ->[L] N} (h : s.EqOn f g)
 : f = g
参数：hs : closure L s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.eq_of_eqOn_top`：eq_of_eqOn_top {f g : M ->[L] N}
 (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g
· 使用定理 `FirstOrder.Language.Hom.eqOn_closure`：eqOn_closure {f g : M ->[L] N} {s 
: Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure L s)
-/
theorem eq_of_eqOn_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

end Hom

namespace Embedding

/-- The restriction of a first-order embedding to a substructure `s ⊆ M` gives an embedding `s → N`.
-/
/-
**FirstOrder.Language.Embedding.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Embedding`。
形式化陈述：domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N
参数：f : M ↪[L] N；p : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a first-order embedding to a substructure `s ⊆ M` gives an em
bedding `s → N`.
-/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.subtype

@[simp]
/-
**FirstOrder.Language.Embedding.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Embedding`。
形式化陈述：domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRes
trict p x = f x
参数：f : M ↪[L] N；p : L.Substructure M；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRestrict p x = f x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted
to an embedding `M → p`. -/
/-
**FirstOrder.Language.Embedding.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Embedding`。
形式化陈述：codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : forall c, f c in p)
 : M ↪[L] p where toFun
参数：p : L.Substructure N；f : M ↪[L] N；h : forall c, f c in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` c
an be restricted
to an embedding `M → p`.
-/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : ∀ c, f c ∈ p) : M ↪[L] p where
  toFun := f.toHom.codRestrict p h
  inj' _ _ ab := f.injective (Subtype.mk_eq_mk.1 ab)
  map_fun' {_} F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' {n} r x := by
    rw [← p.subtype.map_rel]
    change RelMap r (Hom.comp p.subtype.toHom (f.toHom.codRestrict p h) ∘ x) ↔ _
    rw [Hom.subtype_comp_codRestrict, ← f.map_rel]
    rfl

@[simp]
/-
**FirstOrder.Language.Embedding.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Embedding`。
形式化陈述：codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) : (cod
Restrict p f h x : N) = f x
参数：p : L.Substructure N；f : M ↪[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    (codRestrict p f h x : N) = f x :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.codRestrict_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Embedding`。
形式化陈述：codRestrict_apply' (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) : cod
Restrict p f h x = ⟨f x, h x⟩
参数：p : L.Substructure N；f : M ↪[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply' (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    codRestrict p f h x = ⟨f x, h x⟩ :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Embedding`。
形式化陈述：comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h :
 forall b, g b in p) : ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (
g.comp f) fun _ => h _
参数：f : M ↪[L] N；g : N ↪[L] P；p : L.Substructure P；h : forall b, g b in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
/-
**FirstOrder.Language.Embedding.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名
空间 `FirstOrder.Language.Embedding`。
形式化陈述：subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N) (h : forall
 b, f b in p) : p.subtype.comp (codRestrict p f h) = f
参数：f : M ↪[L] N；p : L.Substructure N；h : forall b, f b in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

/-- The equivalence between a substructure `s` and its image `s.map f.toHom`, where `f` is an
  embedding. -/
/-
**FirstOrder.Language.Embedding.substructureEquivMap** 是 Mathlib 中的一个定义，位于命名空间 `
FirstOrder.Language.Embedding`。
形式化陈述：substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) : s ≃[L] s.map 
f.toHom where toFun
参数：f : M ↪[L] N；s : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between a substructure `s` and its image `s.map f.toHom`, where 
`f` is an
  embedding.
-/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    s ≃[L] s.map f.toHom where
  toFun := codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
/-
**FirstOrder.Language.Embedding.substructureEquivMap_apply** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.Embedding`。
形式化陈述：substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
 (f.substructureEquivMap p x : N) = f x
参数：f : M ↪[L] N；p : L.Substructure M；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
    (f.substructureEquivMap p x : N) = f x :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.subtype_substructureEquivMap** 是 Mathlib 中的一个定理，
位于命名空间 `FirstOrder.Language.Embedding`。
形式化陈述：subtype_substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) : (subt
ype _).comp (f.substructureEquivMap s).toEmbedding = f.comp (subtype _)
参数：f : M ↪[L] N；s : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem subtype_substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    (subtype _).comp (f.substructureEquivMap s).toEmbedding = f.comp (subtype _) := by
  ext; rfl

/-- The equivalence between the domain and the range of an embedding `f`. -/
/-
**FirstOrder.Language.Embedding.equivRange** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：{L : FirstOrder.Language} →   {M : Type w} →     {N : Type u_1} →       [i
nst : L.Structure M] → [inst_1 : L.Structure N] → (f : L.Embedding M N) → L.Equi
v M ↥f.toHom.range
参数：f : L.Embedding M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the domain and the range of an embedding `f`.
-/
@[simps toEquiv_apply] noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range where
  toFun := codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
/-
**FirstOrder.Language.Embedding.equivRange_apply** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Embedding`。
形式化陈述：equivRange_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x
参数：f : M ↪[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivRange_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.subtype_equivRange** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Embedding`。
形式化陈述：subtype_equivRange (f : M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedd
ing = f
参数：f : M ↪[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
-/
theorem subtype_equivRange (f : M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedding = f := by
  ext; rfl

end Embedding

namespace Equiv

/-
**FirstOrder.Language.Equiv.toHom_range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Equiv`。
形式化陈述：toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.ext`：ext {S T : L.Substructure M} (h : 
forall x, x in S ↔ x in T) : S = T
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
-/
theorem toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤ := by
  ext n
  simp only [Hom.mem_range, coe_toHom, Substructure.mem_top, iff_true]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

end Equiv

namespace Substructure

/-- The embedding associated to an inclusion of substructures. -/
/-
**FirstOrder.Language.Substructure.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.Substructure`。
形式化陈述：inclusion {S T : L.Substructure M} (h : S <= T) : S ↪[L] T
参数：h : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding associated to an inclusion of substructures.
-/
def inclusion {S T : L.Substructure M} (h : S ≤ T) : S ↪[L] T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/-
**FirstOrder.Language.Substructure.inclusion_self** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Substructure`。
形式化陈述：inclusion_self (S : L.Substructure M) : inclusion (le_refl S) = Embedding.
refl L S
参数：S : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem inclusion_self (S : L.Substructure M) : inclusion (le_refl S) = Embedding.refl L S := rfl

@[simp]
/-
**FirstOrder.Language.Substructure.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：coe_inclusion {S T : L.Substructure M} (h : S <= T) : (inclusion h : S -> 
T) = Set.inclusion h
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    (inclusion h : S → T) = Set.inclusion h :=
  rfl
/-
**FirstOrder.Language.Substructure.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：range_subtype (S : L.Substructure M) : S.subtype.toHom.range = S
参数：S : L.Substructure M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.ext`：ext {S T : L.Substructure M} (h : 
forall x, x in S ↔ x in T) : S = T
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem range_subtype (S : L.Substructure M) : S.subtype.toHom.range = S := by
  ext x
  simp only [Hom.mem_range, Embedding.coe_toHom, coe_subtype]
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]
/-
**FirstOrder.Language.Substructure.subtype_comp_inclusion** 是 Mathlib 中的一个引理，位于命
名空间 `FirstOrder.Language.Substructure`。
形式化陈述：subtype_comp_inclusion {S T : L.Substructure M} (h : S <= T) : T.subtype.c
omp (inclusion h) = S.subtype
参数：h : S <= T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_comp_inclusion {S T : L.Substructure M} (h : S ≤ T) :
    T.subtype.comp (inclusion h) = S.subtype := rfl

end Substructure

end Language

end FirstOrder

