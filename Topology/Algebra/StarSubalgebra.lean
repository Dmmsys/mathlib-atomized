/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Star

/-!
# Topological star (sub)algebras

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `ContinuousSMul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/

@[expose] public section

open Topology
namespace StarSubalgebra

section TopologicalStarAlgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

/-
**StarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalSemiring A] (s : StarSubalgebra R A) : IsTopologicalSemiring s :=
  s.toSubalgebra.topologicalSemiring
/-
**StarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSemitopologicalSemiring A] (s : StarSubalgebra R A) : IsSemitopologicalSemiring s :=
  s.toSubalgebra.semitopologicalSemiring

/-- The `StarSubalgebra.inclusion` of a star subalgebra is an embedding. -/
/-
**StarSubalgebra.isEmbedding_inclusion** 是 Mathlib 中的一个引理，位于命名空间 `StarSubalgebra
`。
形式化陈述：isEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) : IsEmbe
dding (inclusion h) where eq_induced
参数：h : S₁ <= S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id

--- 原说明 ---
The `StarSubalgebra.inclusion` of a star subalgebra is an embedding.
-/
lemma isEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    IsEmbedding (inclusion h) where
  eq_induced := Eq.symm induced_compose
  injective := Subtype.map_injective h Function.injective_id

/-- The `StarSubalgebra.inclusion` of a closed star subalgebra is a `IsClosedEmbedding`. -/
/-
**StarSubalgebra.isClosedEmbedding_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `StarSuba
lgebra`。
形式化陈述：isClosedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ <= S₂) (h
S₁ : IsClosed (S₁ : Set A)) : IsClosedEmbedding (inclusion h)
参数：h : S₁ <= S₂；hS₁ : IsClosed (S₁ : Set A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_induced_iff`：isClosed_induced_iff [t : TopologicalSpace β] {s :
 Set α} {f : α -> β} : IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t 
= s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.range_subtype_map`：range_subtype_map {p : α -> Prop} {q : β -> Prop}
 (f : α -> β) (h : forall x, p x -> q (f x)) : range (Subtype.map f h) = (↑) ⁻¹'
 f '' { x |…

--- 原说明 ---
The `StarSubalgebra.inclusion` of a closed star subalgebra is a `IsClosedEmbeddi
ng`.
-/
theorem isClosedEmbedding_inclusion {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂)
    (hS₁ : IsClosed (S₁ : Set A)) : IsClosedEmbedding (inclusion h) :=
  { IsEmbedding.inclusion h with
    isClosed_range := isClosed_induced_iff.2
      ⟨S₁, hS₁, by
          convert! (Set.range_subtype_map id _).symm
          · rw [Set.image_id]; rfl
          · intro _ h'
            apply h h' ⟩ }

variable [IsSemitopologicalSemiring A] [ContinuousStar A]
variable [TopologicalSpace B] [Semiring B] [Algebra R B] [StarRing B]

/-- The closure of a star subalgebra in a topological star algebra as a star subalgebra. -/
/-
**StarSubalgebra.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 `StarSubalgebra`。
形式化陈述：topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A
参数：s : StarSubalgebra R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.algebraMap_mem'`：∀ {R : Type u} {A : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (self : Subalgebra R A)   (
r : R), (algebra…

--- 原说明 ---
The closure of a star subalgebra in a topological star algebra as a star subalge
bra.
-/
def topologicalClosure (s : StarSubalgebra R A) : StarSubalgebra R A :=
  {
    s.toSubalgebra.topologicalClosure with
    carrier := closure (s : Set A)
    star_mem' := fun ha =>
      map_mem_closure continuous_star ha fun x => (star_mem : x ∈ s → star x ∈ s) }
/-
**StarSubalgebra.topologicalClosure_toSubalgebra_comm** 是 Mathlib 中的一个定理，位于命名空间 
`StarSubalgebra`。
形式化陈述：topologicalClosure_toSubalgebra_comm (s : StarSubalgebra R A) : s.topologi
calClosure.toSubalgebra = s.toSubalgebra.topologicalClosure
参数：s : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem topologicalClosure_toSubalgebra_comm (s : StarSubalgebra R A) :
    s.topologicalClosure.toSubalgebra = s.toSubalgebra.topologicalClosure :=
  SetLike.coe_injective rfl

@[simp]
/-
**StarSubalgebra.topologicalClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebr
a`。
形式化陈述：topologicalClosure_coe (s : StarSubalgebra R A) : (s.topologicalClosure : 
Set A) = closure (s : Set A)
参数：s : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem topologicalClosure_coe (s : StarSubalgebra R A) :
    (s.topologicalClosure : Set A) = closure (s : Set A) :=
  rfl
/-
**StarSubalgebra.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebra
`。
形式化陈述：le_topologicalClosure (s : StarSubalgebra R A) : s <= s.topologicalClosure
参数：s : StarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem le_topologicalClosure (s : StarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
/-
**StarSubalgebra.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `StarSuba
lgebra`。
形式化陈述：isClosed_topologicalClosure (s : StarSubalgebra R A) : IsClosed (s.topolog
icalClosure : Set A)
参数：s : StarSubalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_topologicalClosure (s : StarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) :=
  isClosed_closure
/-
**StarSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A]
    {S : StarSubalgebra R A} : CompleteSpace S.topologicalClosure :=
  isClosed_closure.completeSpace_coe
/-
**StarSubalgebra.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 `StarSubal
gebra`。
形式化陈述：topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s <= t) (ht : I
sClosed (t : Set A)) : s.topologicalClosure <= t
参数：h : s <= t；ht : IsClosed (t : Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem topologicalClosure_minimal {s t : StarSubalgebra R A} (h : s ≤ t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**StarSubalgebra.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgeb
ra`。
形式化陈述：topologicalClosure_mono : Monotone (topologicalClosure : _ -> StarSubalgeb
ra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.topologicalClosure_minimal`：topologicalClosure_minimal {s
 t : StarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topologica
lClosure <= t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s : StarSub
algebra R A) : s <= s.topologicalClosure
· 使用定理 `StarSubalgebra.isClosed_topologicalClosure`：isClosed_topologicalClosure 
(s : StarSubalgebra R A) : IsClosed (s.topologicalClosure : Set A)
-/
theorem topologicalClosure_mono : Monotone (topologicalClosure : _ → StarSubalgebra R A) :=
  fun _ S₂ h =>
  topologicalClosure_minimal (h.trans <| le_topologicalClosure S₂) (isClosed_topologicalClosure S₂)
/-
**StarSubalgebra.topologicalClosure_map_le** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalg
ebra`。
形式化陈述：topologicalClosure_map_le [StarModule R B] [IsSemitopologicalSemiring B] [
ContinuousStar B] (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : IsClosedMap φ
) : (map φ s).topologicalClosure <= map φ s.topologicalClosure
参数：s : StarSubalgebra R A；φ : A ->⋆ₐ[R] B；hφ : IsClosedMap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.closure_image_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → ∀ (s : Set X), clos…
-/
theorem topologicalClosure_map_le [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _
/-
**StarSubalgebra.map_topologicalClosure_le** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalg
ebra`。
形式化陈述：map_topologicalClosure_le [StarModule R B] [IsSemitopologicalSemiring B] [
ContinuousStar B] (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : Continuous φ)
 : map φ s.topologicalClosure <= (map φ s).topologicalClosure
参数：s : StarSubalgebra R A；φ : A ->⋆ₐ[R] B；hφ : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
-/
theorem map_topologicalClosure_le [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ
/-
**StarSubalgebra.topologicalClosure_map** 是 Mathlib 中的一个定理，位于命名空间 `StarSubalgebr
a`。
形式化陈述：topologicalClosure_map [StarModule R B] [IsSemitopologicalSemiring B] [Con
tinuousStar B] (s : StarSubalgebra R A) (φ : A ->⋆ₐ[R] B) (hφ : IsClosedMap φ) (
hφ' : Continuous φ) : (map φ s).topologicalClosure = map φ s.topologicalClosure
参数：s : StarSubalgebra R A；φ : A ->⋆ₐ[R] B；hφ : IsClosedMap φ；hφ' : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `IsClosedMap.closure_image_eq_of_continuous`：IsClosedMap.closure_image_eq
_of_continuous (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) : 
closure (f '' s) = f '' closure …
-/
theorem topologicalClosure_map [StarModule R B] [IsSemitopologicalSemiring B] [ContinuousStar B]
    (s : StarSubalgebra R A) (φ : A →⋆ₐ[R] B) (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq_of_continuous hφ' _

variable (R) in
open StarAlgebra in
/-
**StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer** 是 Mathli
b 中的一个引理，位于命名空间 `StarSubalgebra`。
形式化陈述：topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set 
A) : (adjoin R s).topologicalClosure <= centralizer R (centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.topologicalClosure_minimal`：topologicalClosure_minimal {s
 t : StarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topologica
lClosure <= t
· 使用引理 `StarAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralizer_cen
tralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用引理 `Set.isClosed_centralizer`：Set.isClosed_centralizer {M : Type*} (s : Set 
M) [Mul M] [TopologicalSpace M] [SeparatelyContinuousMul M] [T2Space M] : IsClos
ed (centralize…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)
/-
**StarSubalgebra._root_.Subalgebra.topologicalClosure_star_comm** 是 Mathlib 中的一个
定理，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.topologicalClosure_star_comm (s : Subalgebra R A) :
    (star s).topologicalClosure = star s.topologicalClosure := by
  suffices ∀ t : Subalgebra R A, (star t).topologicalClosure ≤ star t.topologicalClosure from
    le_antisymm (this s) (by simpa only [star_star] using Subalgebra.star_mono (this (star s)))
  exact fun t => (star t).topologicalClosure_minimal (Subalgebra.star_mono subset_closure)
    (isClosed_closure.preimage continuous_star)

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
/-
**StarSubalgebra.commSemiringTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sta
rSubalgebra`。
形式化陈述：commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A) (hs : 
forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure
参数：s : StarSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a star subalgebra of a topological star algebra is commutative, then so is it
s topological
closure. See note [reducible non-instances].
-/
abbrev commSemiringTopologicalClosure [T2Space A] (s : StarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  fast_instance% s.toSubalgebra.commSemiringTopologicalClosure hs

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
/-
**StarSubalgebra.commRingTopologicalClosure** 是 Mathlib 中的一个缩写定义，位于命名空间 `StarSub
algebra`。
形式化陈述：commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpa
ce A] [Ring A] [Algebra R A] [StarRing A] [StarModule R A] [IsSemitopologicalRin
g A] [ContinuousStar A] [T2Space A] (s : StarSubalgebra R A) (hs : forall x y : 
s, x * y = y * x) : CommRing s.topologicalClosure
参数：s : StarSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a star subalgebra of a topological star algebra is commutative, then so is it
s topological
closure. See note [reducible non-instances].
-/
abbrev commRingTopologicalClosure {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A]
    [Algebra R A] [StarRing A] [StarModule R A] [IsSemitopologicalRing A] [ContinuousStar A]
    [T2Space A] (s : StarSubalgebra R A) (hs : ∀ x y : s, x * y = y * x) :
    CommRing s.topologicalClosure :=
  fast_instance% s.toSubalgebra.commRingTopologicalClosure hs

set_option backward.isDefEq.respectTransparency false in
/-- Continuous `StarAlgHom`s from the topological closure of a `StarSubalgebra` whose
compositions with the `StarSubalgebra.inclusion` map agree are, in fact, equal. -/
/-
**StarSubalgebra._root_.StarAlgHom.ext_topologicalClosure** 是 Mathlib 中的一个定理，位于命
名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous `StarAlgHom`s from the topological closure of a `StarSubalgebra` whos
e
compositions with the `StarSubalgebra.inclusion` map agree are, in fact, equal.
-/
theorem _root_.StarAlgHom.ext_topologicalClosure [T2Space B] {S : StarSubalgebra R A}
    {φ ψ : S.topologicalClosure →⋆ₐ[R] B} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h :
      φ.comp (inclusion (le_topologicalClosure S)) = ψ.comp (inclusion (le_topologicalClosure S))) :
    φ = ψ := by
  rw [DFunLike.ext'_iff]
  have : DenseRange (Set.inclusion (le_topologicalClosure S)) := by simp [-SetLike.coe_sort_coe]
  refine Continuous.ext_on this hφ hψ ?_
  rintro _ ⟨x, rfl⟩
  simpa only using! DFunLike.congr_fun h x
/-
**StarSubalgebra._root_.StarAlgHomClass.ext_topologicalClosure** 是 Mathlib 中的一个定
理，位于命名空间 `StarSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StarAlgHomClass.ext_topologicalClosure [T2Space B] {F : Type*}
    {S : StarSubalgebra R A} [FunLike F S.topologicalClosure B]
    [AlgHomClass F R S.topologicalClosure B] [StarHomClass F S.topologicalClosure B] {φ ψ : F}
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : ∀ x : S,
        φ (inclusion (le_topologicalClosure S) x) = ψ ((inclusion (le_topologicalClosure S)) x)) :
    φ = ψ := by
  have : (φ : S.topologicalClosure →⋆ₐ[R] B) = (ψ : S.topologicalClosure →⋆ₐ[R] B) := by
    refine StarAlgHom.ext_topologicalClosure (R := R) (A := A) (B := B) hφ hψ (StarAlgHom.ext ?_)
    simpa only [StarAlgHom.coe_comp, StarAlgHom.coe_coe] using! h
  rw [DFunLike.ext'_iff, ← StarAlgHom.coe_coe]
  apply congrArg _ this

end TopologicalStarAlgebra

end StarSubalgebra

section Elemental

namespace StarAlgebra

open StarSubalgebra

variable (R : Type*) {A B : Type*} [CommSemiring R] [StarRing R]
variable [TopologicalSpace A] [Semiring A] [StarRing A] [IsSemitopologicalSemiring A]
variable [ContinuousStar A] [Algebra R A] [StarModule R A]
variable [TopologicalSpace B] [Semiring B] [StarRing B] [Algebra R B]

/-- The topological closure of the star subalgebra generated by a single element. -/
/-
**StarAlgebra.elemental** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgebra`。
形式化陈述：elemental (x : A) : StarSubalgebra R A
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological closure of the star subalgebra generated by a single element.
-/
def elemental (x : A) : StarSubalgebra R A :=
  (adjoin R ({x} : Set A)).topologicalClosure

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**StarAlgebra.elemental.self_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.elementa
l`。
形式化陈述：self_mem (x : A) : x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s : StarSub
algebra R A) : s <= s.topologicalClosure
· 使用定理 `StarAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A)
 : x in adjoin R ({x} : Set A)
-/
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ (self_mem_adjoin_singleton R x)

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**StarAlgebra.elemental.star_self_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.ele
mental`。
形式化陈述：star_self_mem (x : A) : star x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarMemClass.star_mem`：∀ {S : Type u_1} {R : Type u_2} {inst : Star R} {
inst_1 : SetLike S R} [self : StarMemClass S R] {s : S} {r : R},   r ∈ s → star 
r ∈ s
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
-/
theorem star_self_mem (x : A) : star x ∈ elemental R x :=
  star_mem <| self_mem R x

/-- The `elemental` star subalgebra generated by a normal element is commutative. -/
/-
**StarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `elemental` star subalgebra generated by a normal element is commutative.
-/
instance [T2Space A] {x : A} [IsStarNormal x] : CommSemiring (elemental R x) :=
  fast_instance% StarSubalgebra.commSemiringTopologicalClosure _ mul_comm

/-- The `elemental` generated by a normal element is commutative. -/
/-
**StarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `elemental` generated by a normal element is commutative.
-/
instance {R A} [CommRing R] [StarRing R] [TopologicalSpace A] [Ring A] [Algebra R A] [StarRing A]
    [StarModule R A] [IsSemitopologicalRing A] [ContinuousStar A] [T2Space A] {x : A}
    [IsStarNormal x] : CommRing (elemental R x) :=
  fast_instance% StarSubalgebra.commRingTopologicalClosure _ mul_comm
/-
**StarAlgebra.elemental.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.elementa
l`。
形式化陈述：isClosed (x : A) : IsClosed (elemental R x : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_closure
/-
**StarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Algebra R A] [StarModule R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

variable {R} in
/-
**StarAlgebra.elemental.le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.element
al`。
形式化陈述：le_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A} (hx
 : x in S) : elemental R x <= S
参数：hS : IsClosed (S : Set A)；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarSubalgebra.topologicalClosure_minimal`：topologicalClosure_minimal {s
 t : StarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topologica
lClosure <= t
· 使用定理 `StarAlgebra.adjoin_le`：adjoin_le {S : StarSubalgebra R A} {s : Set A} (h
s : s subseteq S) : adjoin R s <= S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem le_of_mem {S : StarSubalgebra R A} (hS : IsClosed (S : Set A)) {x : A}
    (hx : x ∈ S) : elemental R x ≤ S :=
  topologicalClosure_minimal (adjoin_le <| Set.singleton_subset_iff.2 hx) hS

variable {R} in
/-
**StarAlgebra.elemental.le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.elemen
tal`。
形式化陈述：le_iff_mem {x : A} {s : StarSubalgebra R A} (hs : IsClosed (s : Set A)) : 
elemental R x <= s ↔ x in s
参数：hs : IsClosed (s : Set A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
· 使用定理 `StarAlgebra.elemental.le_of_mem`：le_of_mem {S : StarSubalgebra R A} (hS 
: IsClosed (S : Set A)) {x : A} (hx : x in S) : elemental R x <= S
-/
theorem le_iff_mem {x : A} {s : StarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩

/-- The coercion from an elemental algebra to the full algebra as a `IsClosedEmbedding`. -/
/-
**StarAlgebra.elemental.isClosedEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `StarAlg
ebra.elemental`。
形式化陈述：isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x -> 
A) where eq_induced
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `StarAlgebra.elemental.isClosed`：isClosed (x : A) : IsClosed (elemental R
 x : Set A)

--- 原说明 ---
The coercion from an elemental algebra to the full algebra as a `IsClosedEmbeddi
ng`.
-/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
/-
**StarAlgebra.elemental.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `St
arAlgebra.elemental`。
形式化陈述：le_centralizer_centralizer [T2Space A] (x : A) : elemental R x <= centrali
zer R (centralizer R {x})
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer`：top
ologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A) : (adj
oin R s).topologicalClosure <= centralizer R (centralizer…
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

@[elab_as_elim]
/-
**StarAlgebra.elemental.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgebra.elem
ental`。
形式化陈述：induction_on {x y : A} (hy : y in elemental R x) {P : (u : A) -> u in elem
ental R x -> Prop} (self : P x (self_mem R x)) (star_self : P (star x) (star_sel
f_mem R x)) (algebraMap : forall r, P (algebraMap R A r) (algebraMap_mem _ r)) (
add : forall u hu v hv, P u hu -> P v hv -> P (u + v) (add_mem hu hv)) (mul : fo
rall u hu v hv, P u hu -> P v hv -> P (u * v) (mul_mem hu hv)) (closure : forall
 s : Set A, (hs : s subseteq elemental R x) -> (forall u, (hu : u in s) -> P u (
hs hu)) -> forall v, (hv :
参数：hy : y in elemental R x；u : A；self : P x (self_mem R x)；star_self : P (star x
) (star_self_mem R x)；algebraMap : forall r, P (algebraMap R A r) (algebraMap_me
m _ r)；add : forall u hu v hv, P u hu -> P v hv -> P (u + v) (add_mem hu hv)；mul
 : forall u hu v hv, P u hu -> P v hv -> P (u * v) (mul_mem hu hv)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
· 使用定理 `StarAlgebra.elemental.star_self_mem`：star_self_mem (x : A) : star x in e
lemental R x
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
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
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `StarAlgebra.elemental.isClosed`：isClosed (x : A) : IsClosed (elemental R
 x : Set A)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `StarAlgebra.adjoin_toSubalgebra`：adjoin_toSubalgebra (s : Set A) : (adjo
in R s).toSubalgebra = Algebra.adjoin R (s union star s)
· 使用定理 `StarSubalgebra.mem_toSubalgebra`：mem_toSubalgebra {S : StarSubalgebra R 
A} {x} : x in S.toSubalgebra ↔ x in S
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
-/
theorem induction_on {x y : A}
    (hy : y ∈ elemental R x) {P : (u : A) → u ∈ elemental R x → Prop}
    (self : P x (self_mem R x)) (star_self : P (star x) (star_self_mem R x))
    (algebraMap : ∀ r, P (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ u hu v hv, P u hu → P v hv → P (u + v) (add_mem hu hv))
    (mul : ∀ u hu v hv, P u hu → P v hv → P (u * v) (mul_mem hu hv))
    (closure : ∀ s : Set A, (hs : s ⊆ elemental R x) → (∀ u, (hu : u ∈ s) →
      P u (hs hu)) → ∀ v, (hv : v ∈ closure s) → P v (closure_minimal hs (isClosed R x) hv)) :
    P y hy := by
  apply closure (adjoin R {x} : Set A) subset_closure (fun y hy ↦ ?_) y hy
  rw [SetLike.mem_coe, ← mem_toSubalgebra, adjoin_toSubalgebra] at hy
  induction hy using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ((rfl : u = x) | (hu : star u = x)) := by simpa using hu
    · exact self
    · simp_rw [← hu, star_star] at star_self
      exact star_self
  | algebraMap r => exact algebraMap r
  | add u v hu_mem hv_mem hu hv =>
    exact add u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)
  | mul u v hu_mem hv_mem hu hv =>
    exact mul u (subset_closure hu_mem) v (subset_closure hv_mem) (hu hu_mem) (hv hv_mem)

set_option backward.isDefEq.respectTransparency false in
/-
**StarAlgebra.elemental.starAlgHomClass_ext** 是 Mathlib 中的一个定理，位于命名空间 `StarAlgeb
ra.elemental`。
形式化陈述：starAlgHomClass_ext [T2Space B] {F : Type*} {a : A} [FunLike F (elemental 
R a) B] [AlgHomClass F R _ B] [StarHomClass F _ B] {φ ψ : F} (hφ : Continuous φ)
 (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ
参数：elemental R a；hφ : Continuous φ；hψ : Continuous ψ；h : φ ⟨a, self_mem R a⟩ = ψ
 ⟨a, self_mem R a⟩。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
· 使用定理 `StarAlgHomClass.ext_topologicalClosure`：∀ {R : Type u_1} {A : Type u_2} 
{B : Type u_3} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : Topolog
icalSpace A] [inst_3 : Semir…
· 使用定理 `StarAlgebra.adjoin_induction_subtype`：adjoin_induction_subtype {s : Set 
A} {p : adjoin R s -> Prop} (a : adjoin R s) (mem : forall (x) (h : x in s), p ⟨
x, subset_adjoin R s h⟩) (…
· 使用定理 `StarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s : StarSub
algebra R A) : s <= s.topologicalClosure
· 使用定理 `StarAlgebra.subset_adjoin`：subset_adjoin (s : Set A) : s subseteq adjoin
 R s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
-/
theorem starAlgHomClass_ext [T2Space B] {F : Type*} {a : A}
    [FunLike F (elemental R a) B] [AlgHomClass F R _ B] [StarHomClass F _ B]
    {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) : φ = ψ := by
  refine StarAlgHomClass.ext_topologicalClosure hφ hψ fun x => ?_
  refine adjoin_induction_subtype x ?_ ?_ ?_ ?_ ?_
  exacts [fun y hy => by simpa only [Set.mem_singleton_iff.mp hy] using! h, fun r => by
    simp only [AlgHomClass.commutes], fun x y hx hy => by simp only [map_add, hx, hy],
    fun x y hx hy => by simp only [map_mul, hx, hy], fun x hx => by simp only [map_star, hx]]

end elemental

end StarAlgebra

end Elemental

