/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Non-unital topological (sub)algebras

A non-unital topological algebra over a topological semiring `R` is a topological (non-unital)
semiring with a compatible continuous scalar multiplication by elements of `R`. We reuse
typeclass `ContinuousSMul` to express the latter condition.

## Results

Any non-unital subalgebra of a non-unital topological algebra is itself a non-unital
topological algebra, and its closure is again a non-unital subalgebra.

-/

@[expose] public section

namespace NonUnitalSubalgebra

section Semiring

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A]
variable [NonUnitalSemiring A] [Module R A]
variable [ContinuousConstSMul R A]

/-
**NonUnitalSubalgebra.instIsTopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：instIsTopologicalSemiring [IsTopologicalSemiring A] (s : NonUnitalSubalgeb
ra R A) : IsTopologicalSemiring s
参数：s : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTopologicalSemiring [IsTopologicalSemiring A] (s : NonUnitalSubalgebra R A) :
    IsTopologicalSemiring s :=
  s.toNonUnitalSubsemiring.instIsTopologicalSemiring
/-
**NonUnitalSubalgebra.instIsSemitopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalSubalgebra`。
形式化陈述：instIsSemitopologicalSemiring [IsSemitopologicalSemiring A] (s : NonUnital
Subalgebra R A) : IsSemitopologicalSemiring s
参数：s : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSemitopologicalSemiring [IsSemitopologicalSemiring A] (s : NonUnitalSubalgebra R A) :
    IsSemitopologicalSemiring s :=
  s.toNonUnitalSubsemiring.instIsSemitopologicalSemiring

variable [IsSemitopologicalSemiring A]

/-- The (topological) closure of a non-unital subalgebra of a non-unital topological algebra is
itself a non-unital subalgebra. -/
/-
**NonUnitalSubalgebra.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSub
algebra`。
形式化陈述：topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A
参数：s : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological) closure of a non-unital subalgebra of a non-unital topological
 algebra is
itself a non-unital subalgebra.
-/
def topologicalClosure (s : NonUnitalSubalgebra R A) : NonUnitalSubalgebra R A :=
  { s.toNonUnitalSubsemiring.topologicalClosure, s.toSubmodule.topologicalClosure with
    carrier := _root_.closure (s : Set A) }
/-
**NonUnitalSubalgebra.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subalgebra`。
形式化陈述：le_topologicalClosure (s : NonUnitalSubalgebra R A) : s <= s.topologicalCl
osure
参数：s : NonUnitalSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem le_topologicalClosure (s : NonUnitalSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
/-
**NonUnitalSubalgebra.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalSubalgebra`。
形式化陈述：isClosed_topologicalClosure (s : NonUnitalSubalgebra R A) : IsClosed (s.to
pologicalClosure : Set A)
参数：s : NonUnitalSubalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_topologicalClosure (s : NonUnitalSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure
/-
**NonUnitalSubalgebra.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 `NonU
nitalSubalgebra`。
形式化陈述：topologicalClosure_minimal {s t : NonUnitalSubalgebra R A} (h : s <= t) (h
t : IsClosed (t : Set A)) : s.topologicalClosure <= t
参数：h : s <= t；ht : IsClosed (t : Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem topologicalClosure_minimal {s t : NonUnitalSubalgebra R A}
    (h : s ≤ t) (ht : IsClosed (t : Set A)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**NonUnitalSubalgebra.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `NonUnit
alSubalgebra`。
形式化陈述：topologicalClosure_mono {s t : NonUnitalSubalgebra R A} (h : s <= t) : s.t
opologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem topologicalClosure_mono {s t : NonUnitalSubalgebra R A} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

/-- If a non-unital subalgebra of a non-unital topological algebra is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
/-
**NonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure** 是 Mathlib 中的一个缩写
定义，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalSubalgeb
ra R A) (hs : forall x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologic
alClosure
参数：s : NonUnitalSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital subalgebra of a non-unital topological algebra is commutative, t
hen so is its
topological closure.

See note [reducible non-instances].
-/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  fast_instance% s.toNonUnitalSubsemiring.nonUnitalCommSemiringTopologicalClosure hs

variable [TopologicalSpace B] [NonUnitalSemiring B] [Module R B] [IsTopologicalSemiring B]
    [ContinuousConstSMul R B] (s : NonUnitalSubalgebra R A) {φ : A →ₙₐ[R] B}
/-
**NonUnitalSubalgebra.map_topologicalClosure_le** 是 Mathlib 中的一个引理，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：map_topologicalClosure_le (hφ : Continuous φ) : map φ s.topologicalClosure
 <= (map φ s).topologicalClosure
参数：hφ : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ
/-
**NonUnitalSubalgebra.topologicalClosure_map_le** 是 Mathlib 中的一个引理，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：topologicalClosure_map_le (hφ : IsClosedMap φ) : (map φ s).topologicalClos
ure <= map φ s.topologicalClosure
参数：hφ : IsClosedMap φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.closure_image_subset`：∀ {X : Type u_1} {Y : Type u_2} {f : X
 → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f
 → ∀ (s : Set X), clos…
-/
lemma topologicalClosure_map_le (hφ : IsClosedMap φ) :
    (map φ s).topologicalClosure ≤ map φ s.topologicalClosure :=
  hφ.closure_image_subset _
/-
**NonUnitalSubalgebra.topologicalClosure_map** 是 Mathlib 中的一个引理，位于命名空间 `NonUnita
lSubalgebra`。
形式化陈述：topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) : (map φ 
s).topologicalClosure = map φ s.topologicalClosure
参数：hφ : IsClosedMap φ；hφ' : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `IsClosedMap.closure_image_eq_of_continuous`：IsClosedMap.closure_image_eq
_of_continuous (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) : 
closure (f '' s) = f '' closure …
-/
lemma topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq_of_continuous hφ' _

variable (R) in
open NonUnitalAlgebra in
/-
**NonUnitalSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer** 是 M
athlib 中的一个引理，位于命名空间 `NonUnitalSubalgebra`。
形式化陈述：topologicalClosure_adjoin_le_centralizer_centralizer [IsScalarTower R A A]
 [SMulCommClass R A A] [T2Space A] (s : Set A) : (adjoin R s).topologicalClosure
 <= centralizer R (centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.topologicalClosure_minimal`：topologicalClosure_minim
al {s t : NonUnitalSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.
topologicalClosure <= t
· 使用引理 `NonUnitalAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralize
r_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用引理 `Set.isClosed_centralizer`：Set.isClosed_centralizer {M : Type*} (s : Set 
M) [Mul M] [TopologicalSpace M] [SeparatelyContinuousMul M] [T2Space M] : IsClos
ed (centralize…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma topologicalClosure_adjoin_le_centralizer_centralizer
    [IsScalarTower R A A] [SMulCommClass R A A] [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A]
variable [ContinuousConstSMul R A]

/-
**NonUnitalSubalgebra.instIsTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUnital
Subalgebra`。
形式化陈述：instIsTopologicalRing [IsTopologicalRing A] (s : NonUnitalSubalgebra R A) 
: IsTopologicalRing s
参数：s : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTopologicalRing [IsTopologicalRing A] (s : NonUnitalSubalgebra R A) :
    IsTopologicalRing s :=
  s.toNonUnitalSubring.instIsTopologicalRing
/-
**NonUnitalSubalgebra.instIsSemitopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italSubalgebra`。
形式化陈述：instIsSemitopologicalRing [IsSemitopologicalRing A] (s : NonUnitalSubalgeb
ra R A) : IsSemitopologicalRing s
参数：s : NonUnitalSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSemitopologicalRing [IsSemitopologicalRing A] (s : NonUnitalSubalgebra R A) :
    IsSemitopologicalRing s :=
  s.toNonUnitalSubring.instIsSemitopologicalRing

variable [IsSemitopologicalRing A]

/-- If a non-unital subalgebra of a non-unital topological algebra is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/
/-
**NonUnitalSubalgebra.nonUnitalCommRingTopologicalClosure** 是 Mathlib 中的一个缩写定义，位
于命名空间 `NonUnitalSubalgebra`。
形式化陈述：nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R
 A) (hs : forall x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosur
e
参数：s : NonUnitalSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital subalgebra of a non-unital topological algebra is commutative, t
hen so is its
topological closure.

See note [reducible non-instances].
-/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalSubalgebra

namespace NonUnitalAlgebra

open NonUnitalSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [TopologicalSpace A] [IsSemitopologicalSemiring A] [ContinuousConstSMul R A]

/-- The topological closure of the non-unital subalgebra generated by a single element. -/
/-
**NonUnitalAlgebra.elemental** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalAlgebra`。
形式化陈述：elemental (x : A) : NonUnitalSubalgebra R A
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological closure of the non-unital subalgebra generated by a single eleme
nt.
-/
def elemental (x : A) : NonUnitalSubalgebra R A :=
  adjoin R {x} |>.topologicalClosure

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**NonUnitalAlgebra.elemental.self_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgebr
a.elemental`。
形式化陈述：self_mem (x : A) : x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.le_topologicalClosure`：le_topologicalClosure (s : No
nUnitalSubalgebra R A) : s <= s.topologicalClosure
· 使用定理 `NonUnitalAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x
 : A) : x in adjoin R ({x} : Set A)
-/
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

variable {R} in
/-
**NonUnitalAlgebra.elemental.le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlgeb
ra.elemental`。
形式化陈述：le_of_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A)
) (hx : x in s) : elemental R x <= s
参数：hs : IsClosed (s : Set A)；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.topologicalClosure_minimal`：topologicalClosure_minim
al {s t : NonUnitalSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.
topologicalClosure <= t
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem le_of_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A)) (hx : x ∈ s) :
    elemental R x ≤ s :=
  topologicalClosure_minimal (adjoin_le <| by simpa using hx) hs

variable {R} in
/-
**NonUnitalAlgebra.elemental.le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalAlge
bra.elemental`。
形式化陈述：le_iff_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A
)) : elemental R x <= s ↔ x in s
参数：hs : IsClosed (s : Set A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R
 x
· 使用定理 `NonUnitalAlgebra.elemental.le_of_mem`：le_of_mem {x : A} {s : NonUnitalSu
balgebra R A} (hs : IsClosed (s : Set A)) (hx : x in s) : elemental R x <= s
-/
theorem le_iff_mem {x : A} {s : NonUnitalSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩
/-
**NonUnitalAlgebra.elemental.isClosed** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebr
a.elemental`。
形式化陈述：isClosed (x : A) : IsClosed (elemental R x : Set A)
参数：x : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubalgebra.isClosed_topologicalClosure`：isClosed_topologicalClo
sure (s : NonUnitalSubalgebra R A) : IsClosed (s.topologicalClosure : Set A)
-/
instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

open scoped IsMulCommutative in
/-
**NonUnitalAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebra.elemen
tal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space A] {x : A} : NonUnitalCommSemiring (elemental R x) :=
  fast_instance% nonUnitalCommSemiringTopologicalClosure _ mul_comm
/-
**NonUnitalAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebra.elemen
tal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [TopologicalSpace A] [IsSemitopologicalRing A] [ContinuousConstSMul R A]
    [T2Space A] {x : A} : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm
/-
**NonUnitalAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalAlgebra.elemen
tal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A]
    [IsSemitopologicalSemiring A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
/-
**NonUnitalAlgebra.elemental.isClosedEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `No
nUnitalAlgebra.elemental`。
形式化陈述：isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elementa
l R x -> A) where eq_induced
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
The coercion from an elemental algebra to the full algebra is a `IsClosedEmbeddi
ng`.
-/
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
/-
**NonUnitalAlgebra.elemental.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空
间 `NonUnitalAlgebra.elemental`。
形式化陈述：le_centralizer_centralizer [T2Space A] (x : A) : elemental R x <= centrali
zer R (centralizer R {x})
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer
`：topologicalClosure_adjoin_le_centralizer_centralizer [IsScalarTower R A A] [SM
ulCommClass R A A] [T2Space A] (s : Set A) : (adjoin R s).topo…
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer R {x}

end elemental

end NonUnitalAlgebra

