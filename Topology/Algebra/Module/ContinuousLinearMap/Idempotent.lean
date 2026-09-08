/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Idempotent continuous linear maps

In this file, we study the idempotent elements (`IsIdempotentElem`) of the ring `M →L[R] M` of
continuous endomorphisms of a topological `R`-module `M`.

## Main statements

* `ContinuousLinearMap.isIdempotentElem_toLinearMap_iff`: `T` is idempotent as an element of
  `M →L[R] M` if and only if it is such as an element of `M →ₗ[R] M`;
* `ContinuousLinearMap.IsIdempotentElem.ext_iff`: idempotent elements of `M →L[R] M` are determined
  by their range and kernel;
* `ContinuousLinearMap.IsIdempotentElem.commute_iff`: a continuous linear map `S` commutes with
  an idempotent `T` if and only if the range and kernel of `T` are `S`-invariant;
* `ContinuousLinearMap.IsIdempotentElem.isCLosed_range`: an idempotent continuous linear map
  has closed range.

Further results can be found in the `Mathlib/Topology/Algebra/Module/Complement.lean` module, where
we show that idempotent elements of `M →L[R] M` are precisely the projections associated to
topological complement submodules.
-/

@[expose] public section

namespace ContinuousLinearMap

@[grind =]
/-
**ContinuousLinearMap.isIdempotentElem_toLinearMap_iff** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSp
ace M] [AddCommMonoid M] [Module R M] {f : M ->L[R] M} : IsIdempotentElem f.toLi
nearMap ↔ IsIdempotentElem f
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
theorem isIdempotentElem_toLinearMap_iff {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] {f : M →L[R] M} :
    IsIdempotentElem f.toLinearMap ↔ IsIdempotentElem f := by
  simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← toLinearMap_comp, mul_def, coe_inj]

alias ⟨_, IsIdempotentElem.toLinearMap⟩ := isIdempotentElem_toLinearMap_iff

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

namespace IsIdempotentElem

/-- Idempotent operators are equal iff their range and kernels are. -/
/-
**ContinuousLinearMap.IsIdempotentElem.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMap.IsIdempotentElem`。
形式化陈述：ext_iff {p q : M ->L[R] M} (hp : IsIdempotentElem p) (hq : IsIdempotentEle
m q) : p = q ↔ p.range = q.range ∧ p.ker = q.ker
参数：hp : IsIdempotentElem p；hq : IsIdempotentElem q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsIdempotentElem.ext_iff`：∀ {R : Type u_1} [inst : Ring R] {E 
: Type u_2} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   {p q : E →ₗ
[R] E}, IsIdempotentElem…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …

--- 原说明 ---
Idempotent operators are equal iff their range and kernels are.
-/
lemma ext_iff {p q : M →L[R] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ p.range = q.range ∧ p.ker = q.ker := by
  simpa using LinearMap.IsIdempotentElem.ext_iff hp.toLinearMap hq.toLinearMap

alias ⟨_, ext⟩ := IsIdempotentElem.ext_iff

/-- `range f` is invariant under `T` if and only if `f ∘L T ∘L f = T ∘L f`,
for idempotent `f`. -/
/-
**ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff** 是 Mathlib 中
的一个引理，位于命名空间 `ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：range_mem_invtSubmodule_iff {f T : M ->L[R] M} (hf : IsIdempotentElem f) :
 f.range in Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff`：range_mem_invtSu
bmodule_iff (hf : IsIdempotentElem f) : range f in Module.End.invtSubmodule T ↔ 
f ∘ₗ T ∘ₗ f = T ∘ₗ f
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …

--- 原说明 ---
`range f` is invariant under `T` if and only if `f ∘L T ∘L f = T ∘L f`,
for idempotent `f`.
-/
lemma range_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.range ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = T ∘L f := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_range_mem_invtSubmodule,
  range_mem_invtSubmodule⟩ := IsIdempotentElem.range_mem_invtSubmodule_iff

/-- `ker f` is invariant under `T` if and only if `f ∘L T ∘L f = f ∘L T`,
for idempotent `f`. -/
/-
**ContinuousLinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff** 是 Mathlib 中的一
个引理，位于命名空间 `ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：ker_mem_invtSubmodule_iff {f T : M ->L[R] M} (hf : IsIdempotentElem f) : f
.ker in Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff`：ker_mem_invtSubmod
ule_iff (hf : IsIdempotentElem f) : ker f in Module.End.invtSubmodule T ↔ f ∘ₗ T
 ∘ₗ f = f ∘ₗ T
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …

--- 原说明 ---
`ker f` is invariant under `T` if and only if `f ∘L T ∘L f = f ∘L T`,
for idempotent `f`.
-/
lemma ker_mem_invtSubmodule_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    f.ker ∈ Module.End.invtSubmodule T ↔ f ∘L T ∘L f = f ∘L T := by
  simpa [← toLinearMap_comp] using
    LinearMap.IsIdempotentElem.ker_mem_invtSubmodule_iff (T := T) hf.toLinearMap

alias ⟨conj_eq_of_ker_mem_invtSubmodule,
  ker_mem_invtSubmodule⟩ := IsIdempotentElem.ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
/-
**ContinuousLinearMap.IsIdempotentElem.commute_iff** 是 Mathlib 中的一个引理，位于命名空间 `Co
ntinuousLinearMap.IsIdempotentElem`。
形式化陈述：commute_iff {f T : M ->L[R] M} (hf : IsIdempotentElem f) : Commute f T ↔ (
f.range in Module.End.invtSubmodule T ∧ f.ker in Module.End.invtSubmodule T)
参数：hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsIdempotentElem.commute_iff`：commute_iff (hf : IsIdempotentEl
em f) : Commute f T ↔ (range f in Module.End.invtSubmodule T ∧ ker f in Module.E
nd.invtSubmodule T)
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …

--- 原说明 ---
An idempotent operator `f` commutes with `T` if and only if
both `range f` and `ker f` are invariant under `T`.
-/
lemma commute_iff {f T : M →L[R] M}
    (hf : IsIdempotentElem f) :
    Commute f T ↔ (f.range ∈ Module.End.invtSubmodule T ∧ f.ker ∈ Module.End.invtSubmodule T) := by
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff (T := T) hf.toLinearMap

variable [IsTopologicalAddGroup M]

/-- An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
/-
**ContinuousLinearMap.IsIdempotentElem.commute_iff_of_isUnit** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：commute_iff_of_isUnit {f T : M ->L[R] M} (hT : IsUnit T) (hf : IsIdempoten
tElem f) : Commute f T ↔ f.range.map (T : M ->ₗ[R] M) = f.range ∧ f.ker.map (T :
 M ->ₗ[R] M) = f.ker
参数：hT : IsUnit T；hf : IsIdempotentElem f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.toLinearMapRingHom_apply`：∀ {R₁ : Type u_1} [inst : 
Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMon
oid M₁]   [inst_3 : _root_.Module …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.IsIdempotentElem.commute_iff_of_isUnit`：commute_iff_of_isUnit 
(hT : IsUnit T) (hf : IsIdempotentElem f) : Commute f T ↔ (range f).map T = rang
e f ∧ (ker f).map T = ker f
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …

--- 原说明 ---
An idempotent operator `f` commutes with a unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`.
-/
theorem commute_iff_of_isUnit {f T : M →L[R] M} (hT : IsUnit T)
    (hf : IsIdempotentElem f) :
    Commute f T ↔ f.range.map (T : M →ₗ[R] M) = f.range ∧ f.ker.map (T : M →ₗ[R] M) = f.ker := by
  have := hT.map ContinuousLinearMap.toLinearMapRingHom
  lift T to (M →L[R] M)ˣ using hT
  simpa [Commute, SemiconjBy, Module.End.mul_eq_comp, ← toLinearMap_comp] using!
    LinearMap.IsIdempotentElem.commute_iff_of_isUnit this hf.toLinearMap
/-
**ContinuousLinearMap.IsIdempotentElem.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap.IsIdempotentElem`。
形式化陈述：isClosed_range [T1Space M] {p : M ->L[R] M} (hp : IsIdempotentElem p) : Is
Closed (p.range : Set M)
参数：hp : IsIdempotentElem p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsIdempotentElem.range_eq_ker`：∀ {S : Type u_5} [inst : Semiri
ng S] {E : Type u_7} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module S E]   {p
 : E →ₗ[S] E}, IsIdempotentEl…
· 使用定理 `ContinuousLinearMap.IsIdempotentElem.toLinearMap`：∀ {R : Type u_1} {M : 
Type u_2} [inst : Semiring R] [inst_1 : TopologicalSpace M] [inst_2 : AddCommMon
oid M]   [inst_3 : _root_.Module R M] …
-/
theorem isClosed_range [T1Space M] {p : M →L[R] M}
    (hp : IsIdempotentElem p) : IsClosed (p.range : Set M) :=
  LinearMap.IsIdempotentElem.range_eq_ker hp.toLinearMap ▸ isClosed_ker (.id R M - p)

end IsIdempotentElem

end ContinuousLinearMap

