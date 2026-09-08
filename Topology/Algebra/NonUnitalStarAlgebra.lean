/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalAlgebra
public import Mathlib.Topology.Algebra.Star

/-!
# Non-unital topological star (sub)algebras

A non-unital topological star algebra over a topological semiring `R` is a topological
(non-unital) semiring with a compatible continuous scalar multiplication by elements
of `R` and a continuous `star` operation. We reuse typeclasses `ContinuousSMul` and
`ContinuousStar` to express the latter two conditions.

## Results

Any non-unital star subalgebra of a non-unital topological star algebra is itself a
non-unital topological star algebra, and its closure is again a non-unital star subalgebra.

-/

@[expose] public section

namespace NonUnitalStarSubalgebra

section Semiring

variable {R A B : Type*} [CommSemiring R] [TopologicalSpace A] [Star A]
variable [NonUnitalSemiring A] [Module R A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

/-
**NonUnitalStarSubalgebra.instIsTopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：instIsTopologicalSemiring [IsTopologicalSemiring A] (s : NonUnitalStarSuba
lgebra R A) : IsTopologicalSemiring s
参数：s : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTopologicalSemiring [IsTopologicalSemiring A] (s : NonUnitalStarSubalgebra R A) :
    IsTopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instIsTopologicalSemiring
/-
**NonUnitalStarSubalgebra.instIsSemitopologicalSemiring** 是 Mathlib 中的一个实例，位于命名空
间 `NonUnitalStarSubalgebra`。
形式化陈述：instIsSemitopologicalSemiring [IsSemitopologicalSemiring A] (s : NonUnital
StarSubalgebra R A) : IsSemitopologicalSemiring s
参数：s : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSemitopologicalSemiring [IsSemitopologicalSemiring A]
    (s : NonUnitalStarSubalgebra R A) : IsSemitopologicalSemiring s :=
  s.toNonUnitalSubalgebra.instIsSemitopologicalSemiring

variable [IsSemitopologicalSemiring A]

/-- The (topological) closure of a non-unital star subalgebra of a non-unital topological star
algebra is itself a non-unital star subalgebra. -/
/-
**NonUnitalStarSubalgebra.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 `NonUnita
lStarSubalgebra`。
形式化陈述：topologicalClosure (s : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalg
ebra R A
参数：s : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological) closure of a non-unital star subalgebra of a non-unital topolo
gical star
algebra is itself a non-unital star subalgebra.
-/
def topologicalClosure (s : NonUnitalStarSubalgebra R A) : NonUnitalStarSubalgebra R A :=
  { s.toNonUnitalSubalgebra.topologicalClosure with
    star_mem' := fun h ↦ map_mem_closure continuous_star h fun _ ↦ star_mem
    carrier := _root_.closure (s : Set A) }
/-
**NonUnitalStarSubalgebra.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italStarSubalgebra`。
形式化陈述：le_topologicalClosure (s : NonUnitalStarSubalgebra R A) : s <= s.topologic
alClosure
参数：s : NonUnitalStarSubalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem le_topologicalClosure (s : NonUnitalStarSubalgebra R A) : s ≤ s.topologicalClosure :=
  subset_closure
/-
**NonUnitalStarSubalgebra.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 
`NonUnitalStarSubalgebra`。
形式化陈述：isClosed_topologicalClosure (s : NonUnitalStarSubalgebra R A) : IsClosed (
s.topologicalClosure : Set A)
参数：s : NonUnitalStarSubalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_topologicalClosure (s : NonUnitalStarSubalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := isClosed_closure
/-
**NonUnitalStarSubalgebra.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 `
NonUnitalStarSubalgebra`。
形式化陈述：topologicalClosure_minimal (s : NonUnitalStarSubalgebra R A) {t : NonUnita
lStarSubalgebra R A} (h : s <= t) (ht : IsClosed (t : Set A)) : s.topologicalClo
sure <= t
参数：s : NonUnitalStarSubalgebra R A；h : s <= t；ht : IsClosed (t : Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem topologicalClosure_minimal (s : NonUnitalStarSubalgebra R A)
    {t : NonUnitalStarSubalgebra R A} (h : s ≤ t) (ht : IsClosed (t : Set A)) :
    s.topologicalClosure ≤ t :=
  closure_minimal h ht

@[gcongr]
/-
**NonUnitalStarSubalgebra.topologicalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Non
UnitalStarSubalgebra`。
形式化陈述：topologicalClosure_mono {s t : NonUnitalStarSubalgebra R A} (h : s <= t) :
 s.topologicalClosure <= t.topologicalClosure
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
-/
theorem topologicalClosure_mono {s t : NonUnitalStarSubalgebra R A} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

/-- If a non-unital star subalgebra of a non-unital topological star algebra is commutative, then
so is its topological closure.

See note [reducible non-instances] -/
/-
**NonUnitalStarSubalgebra.nonUnitalCommSemiringTopologicalClosure** 是 Mathlib 中的
一个缩写定义，位于命名空间 `NonUnitalStarSubalgebra`。
形式化陈述：nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalStarSuba
lgebra R A) (hs : forall x y : s, x * y = y * x) : NonUnitalCommSemiring s.topol
ogicalClosure
参数：s : NonUnitalStarSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital star subalgebra of a non-unital topological star algebra is comm
utative, then
so is its topological closure.

See note [reducible non-instances]
-/
abbrev nonUnitalCommSemiringTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  fast_instance% s.toNonUnitalSubalgebra.nonUnitalCommSemiringTopologicalClosure hs

variable [TopologicalSpace B] [Star B] [NonUnitalSemiring B] [Module R B]
    [IsSemitopologicalSemiring B] [ContinuousConstSMul R B] [ContinuousStar B]
    (s : NonUnitalStarSubalgebra R A) {φ : A →⋆ₙₐ[R] B}
/-
**NonUnitalStarSubalgebra.map_topologicalClosure_le** 是 Mathlib 中的一个引理，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：map_topologicalClosure_le (hφ : Continuous φ) : map φ s.topologicalClosure
 <= (map φ s).topologicalClosure
参数：hφ : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
-/
lemma map_topologicalClosure_le (hφ : Continuous φ) :
    map φ s.topologicalClosure ≤ (map φ s).topologicalClosure :=
  image_closure_subset_closure_image hφ
/-
**NonUnitalStarSubalgebra.topologicalClosure_map_le** 是 Mathlib 中的一个引理，位于命名空间 `N
onUnitalStarSubalgebra`。
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
**NonUnitalStarSubalgebra.topologicalClosure_map** 是 Mathlib 中的一个引理，位于命名空间 `NonU
nitalStarSubalgebra`。
形式化陈述：topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) : (map φ 
s).topologicalClosure = map φ s.topologicalClosure
参数：hφ : IsClosedMap φ；hφ' : Continuous φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `IsClosedMap.closure_image_eq_of_continuous`：IsClosedMap.closure_image_eq
_of_continuous (f_closed : IsClosedMap f) (f_cont : Continuous f) (s : Set X) : 
closure (f '' s) = f '' closure …
-/
lemma topologicalClosure_map (hφ : IsClosedMap φ) (hφ' : Continuous φ) :
    (map φ s).topologicalClosure = map φ s.topologicalClosure :=
  SetLike.coe_injective <| hφ.closure_image_eq_of_continuous hφ' _

open NonUnitalStarAlgebra in
-- we have to shadow the variables because some things currently require `StarRing`
/-
**NonUnitalStarSubalgebra.topologicalClosure_adjoin_le_centralizer_centralizer**
 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarSubalgebra`。
形式化陈述：topologicalClosure_adjoin_le_centralizer_centralizer (R : Type*) {A : Type
*} [CommSemiring R] [StarRing R] [TopologicalSpace A] [NonUnitalSemiring A] [Sta
rRing A] [Module R A] [IsSemitopologicalSemiring A] [ContinuousStar A] [Continuo
usConstSMul R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] [T
2Space A] (s : Set A) : (adjoin R s).topologicalClosure <= centralizer R (centra
lizer R s)
参数：R : Type*；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.topologicalClosure_minimal`：topologicalClosure_m
inimal (s : NonUnitalStarSubalgebra R A) {t : NonUnitalStarSubalgebra R A} (h : 
s <= t) (ht : IsClosed (t : Set A)) : s.…
· 使用引理 `NonUnitalStarAlgebra.adjoin_le_centralizer_centralizer`：adjoin_le_centra
lizer_centralizer (s : Set A) : adjoin R s <= centralizer R (centralizer R s)
· 使用引理 `Set.isClosed_centralizer`：Set.isClosed_centralizer {M : Type*} (s : Set 
M) [Mul M] [TopologicalSpace M] [SeparatelyContinuousMul M] [T2Space M] : IsClos
ed (centralize…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma topologicalClosure_adjoin_le_centralizer_centralizer (R : Type*) {A : Type*}
    [CommSemiring R] [StarRing R] [TopologicalSpace A] [NonUnitalSemiring A] [StarRing A]
    [Module R A] [IsSemitopologicalSemiring A] [ContinuousStar A] [ContinuousConstSMul R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure ≤ centralizer R (centralizer R s) :=
  topologicalClosure_minimal _ (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [TopologicalSpace A]
variable [NonUnitalRing A] [Module R A] [Star A] [ContinuousStar A]
variable [ContinuousConstSMul R A]

/-
**NonUnitalStarSubalgebra.instIsTopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `NonUn
italStarSubalgebra`。
形式化陈述：instIsTopologicalRing [IsTopologicalRing A] (s : NonUnitalStarSubalgebra R
 A) : IsTopologicalRing s
参数：s : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsTopologicalRing [IsTopologicalRing A] (s : NonUnitalStarSubalgebra R A) :
    IsTopologicalRing s :=
  s.toNonUnitalSubring.instIsTopologicalRing
/-
**NonUnitalStarSubalgebra.instIsSemitopologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `N
onUnitalStarSubalgebra`。
形式化陈述：instIsSemitopologicalRing [IsSemitopologicalRing A] (s : NonUnitalStarSuba
lgebra R A) : IsSemitopologicalRing s
参数：s : NonUnitalStarSubalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSemitopologicalRing [IsSemitopologicalRing A] (s : NonUnitalStarSubalgebra R A) :
    IsSemitopologicalRing s :=
  s.toNonUnitalSubring.instIsSemitopologicalRing

variable [IsSemitopologicalRing A]

/-- If a non-unital star subalgebra of a non-unital topological star algebra is commutative, then
so is its topological closure.

See note [reducible non-instances]. -/
/-
**NonUnitalStarSubalgebra.nonUnitalCommRingTopologicalClosure** 是 Mathlib 中的一个缩写
定义，位于命名空间 `NonUnitalStarSubalgebra`。
形式化陈述：nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgeb
ra R A) (hs : forall x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalCl
osure
参数：s : NonUnitalStarSubalgebra R A；hs : forall x y : s, x * y = y * x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a non-unital star subalgebra of a non-unital topological star algebra is comm
utative, then
so is its topological closure.

See note [reducible non-instances].
-/
abbrev nonUnitalCommRingTopologicalClosure [T2Space A] (s : NonUnitalStarSubalgebra R A)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end Ring

end NonUnitalStarSubalgebra

namespace NonUnitalStarAlgebra

open NonUnitalStarSubalgebra

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [TopologicalSpace A] [IsSemitopologicalSemiring A] [ContinuousConstSMul R A]
variable [ContinuousStar A]

/-- The topological closure of the non-unital star subalgebra generated by a single element. -/
/-
**NonUnitalStarAlgebra.elemental** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarAlgebra
`。
形式化陈述：elemental (x : A) : NonUnitalStarSubalgebra R A
参数：x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological closure of the non-unital star subalgebra generated by a single 
element.
-/
def elemental (x : A) : NonUnitalStarSubalgebra R A :=
  adjoin R {x} |>.topologicalClosure

namespace elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**NonUnitalStarAlgebra.elemental.self_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arAlgebra.elemental`。
形式化陈述：self_mem (x : A) : x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s 
: NonUnitalStarSubalgebra R A) : s <= s.topologicalClosure
· 使用定理 `NonUnitalStarAlgebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleto
n (x : A) : x in adjoin R ({x} : Set A)
-/
theorem self_mem (x : A) : x ∈ elemental R x :=
  le_topologicalClosure _ <| self_mem_adjoin_singleton R x

@[simp, aesop safe (rule_sets := [SetLike])]
/-
**NonUnitalStarAlgebra.elemental.star_self_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUni
talStarAlgebra.elemental`。
形式化陈述：star_self_mem (x : A) : star x in elemental R x
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.le_topologicalClosure`：le_topologicalClosure (s 
: NonUnitalStarSubalgebra R A) : s <= s.topologicalClosure
· 使用定理 `NonUnitalStarAlgebra.star_self_mem_adjoin_singleton`：star_self_mem_adjoi
n_singleton (x : A) : star x in adjoin R ({x} : Set A)
-/
theorem star_self_mem (x : A) : star x ∈ elemental R x :=
  le_topologicalClosure _ <| star_self_mem_adjoin_singleton R x

variable {R} in
/-
**NonUnitalStarAlgebra.elemental.le_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalS
tarAlgebra.elemental`。
形式化陈述：le_of_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Se
t A)) (hx : x in s) : elemental R x <= s
参数：hs : IsClosed (s : Set A)；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.topologicalClosure_minimal`：topologicalClosure_m
inimal (s : NonUnitalStarSubalgebra R A) {t : NonUnitalStarSubalgebra R A} (h : 
s <= t) (ht : IsClosed (t : Set A)) : s.…
· 使用定理 `NonUnitalStarAlgebra.adjoin_le`：adjoin_le {S : NonUnitalStarSubalgebra R
 A} {s : Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem le_of_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A))
    (hx : x ∈ s) : elemental R x ≤ s :=
  topologicalClosure_minimal _ (adjoin_le <| by simpa using hx) hs

variable {R} in
/-
**NonUnitalStarAlgebra.elemental.le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarAlgebra.elemental`。
形式化陈述：le_iff_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : S
et A)) : elemental R x <= s ↔ x in s
参数：hs : IsClosed (s : Set A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgebra.elemental.self_mem`：self_mem (x : A) : x in element
al R x
· 使用定理 `NonUnitalStarAlgebra.elemental.le_of_mem`：le_of_mem {x : A} {s : NonUnit
alStarSubalgebra R A} (hs : IsClosed (s : Set A)) (hx : x in s) : elemental R x 
<= s
-/
theorem le_iff_mem {x : A} {s : NonUnitalStarSubalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x ≤ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem R x), fun h ↦ le_of_mem hs h⟩
/-
**NonUnitalStarAlgebra.elemental.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSt
arAlgebra.elemental`。
形式化陈述：isClosed (x : A) : IsClosed (elemental R x : Set A)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarSubalgebra.isClosed_topologicalClosure`：isClosed_topologica
lClosure (s : NonUnitalStarSubalgebra R A) : IsClosed (s.topologicalClosure : Se
t A)
-/
theorem isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

open scoped IsMulCommutative in
/-
**NonUnitalStarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgebr
a.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommSemiring (elemental R x) :=
  fast_instance% nonUnitalCommSemiringTopologicalClosure _ mul_comm
/-
**NonUnitalStarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgebr
a.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A : Type*} [CommRing R] [StarRing R] [NonUnitalRing A] [StarRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    [TopologicalSpace A] [IsSemitopologicalRing A] [ContinuousConstSMul R A] [ContinuousStar A]
    [T2Space A] {x : A} [IsStarNormal x] : NonUnitalCommRing (elemental R x) where
  mul_comm := mul_comm
/-
**NonUnitalStarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `NonUnitalStarAlgebr
a.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [UniformSpace A] [CompleteSpace A] [NonUnitalSemiring A] [StarRing A]
    [IsSemitopologicalSemiring A] [ContinuousStar A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] [ContinuousConstSMul R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/-- The coercion from an elemental algebra to the full algebra is a `IsClosedEmbedding`. -/
/-
**NonUnitalStarAlgebra.elemental.isClosedEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间
 `NonUnitalStarAlgebra.elemental`。
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
· 使用定理 `NonUnitalStarAlgebra.elemental.isClosed`：isClosed (x : A) : IsClosed (el
emental R x : Set A)

--- 原说明 ---
The coercion from an elemental algebra to the full algebra is a `IsClosedEmbeddi
ng`.
-/
theorem isClosedEmbedding_coe (x : A) : Topology.IsClosedEmbedding ((↑) : elemental R x → A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
/-
**NonUnitalStarAlgebra.elemental.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位
于命名空间 `NonUnitalStarAlgebra.elemental`。
形式化陈述：le_centralizer_centralizer [T2Space A] (x : A) : elemental R x <= centrali
zer R (centralizer R {x})
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalStarSubalgebra.topologicalClosure_adjoin_le_centralizer_central
izer`：topologicalClosure_adjoin_le_centralizer_centralizer (R : Type*) {A : Type
*} [CommSemiring R] [StarRing R] [TopologicalSpace A] [NonUnitalSe…
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x ≤ centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

end elemental

end NonUnitalStarAlgebra

