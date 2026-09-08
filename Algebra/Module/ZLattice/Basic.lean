/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Localization.Module

/-!
# ℤ-lattices

Let `E` be a finite-dimensional vector space over a `NormedLinearOrderedField` `K` with a solid
norm that is also a `FloorRing`, e.g. `ℝ`. A (full) `ℤ`-lattice `L` of `E` is a discrete
subgroup of `E` such that `L` spans `E` over `K`.

A `ℤ`-lattice `L` can be defined in two ways:
* For `b` a basis of `E`, then `L = Submodule.span ℤ (Set.range b)` is a ℤ-lattice of `E`
* As a `ℤ-submodule` of `E` with the additional properties:
  * `DiscreteTopology L`, that is `L` is discrete
  * `Submodule.span ℝ (L : Set E) = ⊤`, that is `L` spans `E` over `K`.

Results about the first point of view are in the `ZSpan` namespace and results about the second
point of view are in the `ZLattice` namespace.

## Main results and definitions

* `ZSpan.isAddFundamentalDomain`: for a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that
  the set defined by `ZSpan.fundamentalDomain` is a fundamental domain.
* `ZLattice.module_free`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is a free
  `ℤ`-module
* `ZLattice.rank`: a `ℤ`-submodule of `E` that is discrete and spans `E` over `K` is free
  of `ℤ`-rank equal to the `K`-rank of `E`
* `ZLattice.comap`: for `e : E → F` a linear map and `L : Submodule ℤ E`, define the pullback of
  `L` by `e`. If `L` is a `IsZLattice` and `e` is a continuous linear equiv, then it is also a
  `IsZLattice`, see `instIsZLatticeComap`.

## Note

There is also `Submodule.IsLattice` which has slightly different applications. There no
topology is needed and the discrete condition is replaced by finitely generated.

## Implementation Notes

A `ZLattice` could be defined either as a `AddSubgroup E` or a `Submodule ℤ E`. However, the module
aspect appears to be the more useful one (especially in computations involving basis) and is also
consistent with the `ZSpan` construction of `ℤ`-lattices.

-/

@[expose] public section


noncomputable section

namespace ZSpan

open MeasureTheory MeasurableSet Module Submodule Bornology

variable {E ι : Type*}

section NormedLatticeField

variable {K : Type*} [NormedField K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable (b : Basis ι K E)

/-
**ZSpan.span_top** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：span_top : span K (span Int (Set.range b) : Set E) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem span_top : span K (span ℤ (Set.range b) : Set E) = ⊤ := by simp [span_span_of_tower]
/-
**ZSpan.map** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) : Submodule.
map (f.restrictScalars Int : E ->ₗ[Int] F) (span Int (Set.range b)) = span Int (
Set.range (b.map f))
参数：f : E ≃ₗ[K] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map {F : Type*} [AddCommGroup F] [Module K F] (f : E ≃ₗ[K] F) :
    Submodule.map (f.restrictScalars ℤ : E →ₗ[ℤ] F) (span ℤ (Set.range b)) =
      span ℤ (Set.range (b.map f)) := by
  simp_rw [Submodule.map_span, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    Basis.coe_map, Set.range_comp]

open scoped Pointwise in
/-
**ZSpan.smul** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：smul {c : K} (hc : c != 0) : c • span Int (Set.range b) = span Int (Set.ra
nge (b.isUnitSMul (fun _ => hc.isUnit)))
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_span`：smul_span (a : α) (s : Set M) : a • span R s = span
 R (a • s)
· 使用引理 `Set.smul_set_range`：smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι
 -> β) : a • range f = range fun i => a • f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.isUnitSMul_apply`：isUnitSMul_apply {v : Basis ι R M} {w : ι
 -> R} (hw : forall i, IsUnit (w i)) (i : ι) : v.isUnitSMul hw i = w i • v i
-/
theorem smul {c : K} (hc : c ≠ 0) :
    c • span ℤ (Set.range b) = span ℤ (Set.range (b.isUnitSMul (fun _ ↦ hc.isUnit))) := by
  rw [smul_span, Set.smul_set_range]
  congr!
  rw [Basis.isUnitSMul_apply]

variable [LinearOrder K]

/-- The fundamental domain of the ℤ-lattice spanned by `b`. See `ZSpan.isAddFundamentalDomain`
for the proof that it is a fundamental domain. -/
/-
**ZSpan.fundamentalDomain** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain : Set E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fundamental domain of the ℤ-lattice spanned by `b`. See `ZSpan.isAddFundamen
talDomain`
for the proof that it is a fundamental domain.
-/
def fundamentalDomain : Set E := {m | ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1}

@[simp]
/-
**ZSpan.mem_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：mem_fundamentalDomain {m : E} : m in fundamentalDomain b ↔ forall i, b.rep
r m i in Set.Ico (0 : K) 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fundamentalDomain {m : E} :
    m ∈ fundamentalDomain b ↔ ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1 := Iff.rfl
/-
**ZSpan.map_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：map_fundamentalDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
 (f : E ≃ₗ[K] F) : f '' (fundamentalDomain b) = fundamentalDomain (b.map f)
参数：f : E ≃ₗ[K] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.mem_fundamentalDomain`：mem_fundamentalDomain {m : E} : m in fundam
entalDomain b ↔ forall i, b.repr m i in Set.Ico (0 : K) 1
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_fundamentalDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) :
    f '' (fundamentalDomain b) = fundamentalDomain (b.map f) := by
  ext x
  rw [mem_fundamentalDomain, Basis.map_repr, LinearEquiv.trans_apply, ← mem_fundamentalDomain,
    show f.symm x = f.toEquiv.symm x by rfl, ← Set.mem_image_equiv]
  rfl

@[simp]
/-
**ZSpan.fundamentalDomain_reindex** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain_reindex {ι' : Type*} (e : ι ≃ ι') : fundamentalDomain (b
.reindex e) = fundamentalDomain b
参数：e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_reindex`：repr_reindex : (b.reindex e).repr x = (b.repr
 x).mapDomain e
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fundamentalDomain_reindex {ι' : Type*} (e : ι ≃ ι') :
    fundamentalDomain (b.reindex e) = fundamentalDomain b := by
  ext
  simp [e.forall_congr_left]

variable [IsStrictOrderedRing K]
/-
**ZSpan.fundamentalDomain_pi_basisFun** 是 Mathlib 中的一个引理，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain_pi_basisFun [Fintype ι] : fundamentalDomain (Pi.basisFun
 Real ι) = Set.pi Set.univ fun _ : ι => Set.Ico (0 : Real) 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma fundamentalDomain_pi_basisFun [Fintype ι] :
    fundamentalDomain (Pi.basisFun ℝ ι) = Set.pi Set.univ fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
  ext; simp

variable [FloorRing K]

section Fintype

variable [Fintype ι]

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding down its coordinates on the basis `b`. -/
/-
**ZSpan.floor** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：floor (m : E) : span Int (Set.range b)
参数：m : E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ

--- 原说明 ---
The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b
` obtained
by rounding down its coordinates on the basis `b`.
-/
def floor (m : E) : span ℤ (Set.range b) := ∑ i, ⌊b.repr m i⌋ • b.restrictScalars ℤ i

/-- The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b` obtained
by rounding up its coordinates on the basis `b`. -/
/-
**ZSpan.ceil** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：ceil (m : E) : span Int (Set.range b)
参数：m : E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ

--- 原说明 ---
The map that sends a vector of `E` to the element of the ℤ-lattice spanned by `b
` obtained
by rounding up its coordinates on the basis `b`.
-/
def ceil (m : E) : span ℤ (Set.range b) := ∑ i, ⌈b.repr m i⌉ • b.restrictScalars ℤ i

@[simp]
/-
**ZSpan.repr_floor_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：repr_floor_apply (m : E) (i : ι) : b.repr (floor b m) i = ⌊b.repr m i⌋
参数：m : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Submodule.coe_sum`：coe_sum (x : ι -> p) (s : Finset ι) : ↑(∑ i in s, x i
) = ∑ i in s, (x i : M)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single'`：smul_single' {_ : Semiring R} (c : R) (a : α) (b :
 R) : c • Finsupp.single a b = Finsupp.single a (c * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem repr_floor_apply (m : E) (i : ι) : b.repr (floor b m) i = ⌊b.repr m i⌋ := by
  classical simp only [floor, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
/-
**ZSpan.repr_ceil_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b m) i = ⌈b.repr m i⌉
参数：m : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Submodule.coe_sum`：coe_sum (x : ι -> p) (s : Finset ι) : ↑(∑ i in s, x i
) = ∑ i in s, (x i : M)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single'`：smul_single' {_ : Semiring R} (c : R) (a : α) (b :
 R) : c • Finsupp.single a b = Finsupp.single a (c * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_apply'`：Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k
 i
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b m) i = ⌈b.repr m i⌉ := by
  classical simp only [ceil, ← Int.cast_smul_eq_zsmul K, b.repr.map_smul, Finsupp.single_apply,
    Finset.sum_apply', Basis.repr_self, Finsupp.smul_single', mul_one, Finset.sum_ite_eq', coe_sum,
    Finset.mem_univ, if_true, coe_smul_of_tower, Basis.restrictScalars_apply, map_sum]

@[simp]
/-
**ZSpan.floor_eq_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：floor_eq_self_of_mem (m : E) (h : m in span Int (Set.range b)) : (floor b 
m : E) = m
参数：m : E；h : m in span Int (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_floor_apply`：repr_floor_apply (m : E) (i : ι) : b.repr (floor
 b m) i = ⌊b.repr m i⌋
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.mem_span_iff_repr_mem`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [IsDomain R] [inst_2 : Ring S]   [
Nontrivial S] [inst_4 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
-/
theorem floor_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (floor b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : ℤ → K) (Int.floor_intCast z)

@[simp]
/-
**ZSpan.ceil_eq_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：ceil_eq_self_of_mem (m : E) (h : m in span Int (Set.range b)) : (ceil b m 
: E) = m
参数：m : E；h : m in span Int (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_ceil_apply`：repr_ceil_apply (m : E) (i : ι) : b.repr (ceil b 
m) i = ⌈b.repr m i⌉
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.mem_span_iff_repr_mem`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [IsDomain R] [inst_2 : Ring S]   [
Nontrivial S] [inst_4 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
-/
theorem ceil_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (ceil b m : E) = m := by
  apply b.ext_elem
  simp_rw [repr_ceil_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : ℤ → K) (Int.ceil_intCast z)

/-- The map that sends a vector `E` to the `fundamentalDomain` of the lattice,
see `ZSpan.fract_mem_fundamentalDomain`, and `fractRestrict` for the map with the codomain
restricted to `fundamentalDomain`. -/
/-
**ZSpan.fract** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：fract (m : E) : E
参数：m : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that sends a vector `E` to the `fundamentalDomain` of the lattice,
see `ZSpan.fract_mem_fundamentalDomain`, and `fractRestrict` for the map with th
e codomain
restricted to `fundamentalDomain`.
-/
def fract (m : E) : E := m - floor b m
/-
**ZSpan.fract_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_apply (m : E) : fract b m = m - floor b m
参数：m : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fract_apply (m : E) : fract b m = m - floor b m := rfl

@[simp]
/-
**ZSpan.repr_fract_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：repr_fract_apply (m : E) (i : ι) : b.repr (fract b m) i = Int.fract (b.rep
r m i)
参数：m : E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.fract.eq_1`：∀ {E : Type u_1} {ι : Type u_2} {K : Type u_3} [inst :
 NormedField K] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace K E] (b 
: Modu…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.coe_sub`：∀ {ι : Type u_1} {G : Type u_6} [inst : SubNegZeroMonoi
d G] (g₁ g₂ : ι →₀ G), ⇑(g₁ - g₂) = ⇑g₁ - ⇑g₂
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `ZSpan.repr_floor_apply`：repr_floor_apply (m : E) (i : ι) : b.repr (floor
 b m) i = ⌊b.repr m i⌋
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
-/
theorem repr_fract_apply (m : E) (i : ι) : b.repr (fract b m) i = Int.fract (b.repr m i) := by
  rw [fract, map_sub, Finsupp.coe_sub, Pi.sub_apply, repr_floor_apply, Int.fract]

@[simp]
/-
**ZSpan.fract_fract** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_fract (m : E) : fract b (fract b m) = fract b m
参数：m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `Int.fract_fract`：fract_fract (a : R) : fract (fract a) = fract a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fract_fract (m : E) : fract b (fract b m) = fract b m :=
  Basis.ext_elem b fun _ => by simp only [repr_fract_apply, Int.fract_fract]

@[simp]
/-
**ZSpan.fract_zSpan_add** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_zSpan_add (m : E) {v : E} (h : v in span Int (Set.range b)) : fract 
b (v + m) = fract b m
参数：m : E；h : v in span Int (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
（共 34 条，此处仅展示前 30 条）
-/
theorem fract_zSpan_add (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (v + m) = fract b m := by
  refine (Basis.ext_elem_iff b).mpr fun i => ?_
  simp_rw [repr_fract_apply, Int.fract_eq_fract]
  use (b.restrictScalars ℤ).repr ⟨v, h⟩ i
  rw [map_add, Finsupp.coe_add, Pi.add_apply, add_tsub_cancel_right,
    ← eq_intCast (algebraMap ℤ K) _, Basis.restrictScalars_repr_apply, coe_mk]

@[simp]
/-
**ZSpan.fract_add_ZSpan** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_add_ZSpan (m : E) {v : E} (h : v in span Int (Set.range b)) : fract 
b (m + v) = fract b m
参数：m : E；h : v in span Int (Set.range b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ZSpan.fract_zSpan_add`：fract_zSpan_add (m : E) {v : E} (h : v in span In
t (Set.range b)) : fract b (v + m) = fract b m
-/
theorem fract_add_ZSpan (m : E) {v : E} (h : v ∈ span ℤ (Set.range b)) :
    fract b (m + v) = fract b m := by rw [add_comm, fract_zSpan_add b m h]

variable {b} in
/-
**ZSpan.fract_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_eq_self {x : E} : fract b x = x ↔ x in fundamentalDomain b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fract_eq_self {x : E} : fract b x = x ↔ x ∈ fundamentalDomain b := by
  simp only [Basis.ext_elem_iff b, repr_fract_apply, Int.fract_eq_self,
    mem_fundamentalDomain, Set.mem_Ico]
/-
**ZSpan.fract_mem_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_mem_fundamentalDomain (x : E) : fract b x in fundamentalDomain b
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZSpan.fract_eq_self`：fract_eq_self {x : E} : fract b x = x ↔ x in fundam
entalDomain b
· 使用定理 `ZSpan.fract_fract`：fract_fract (m : E) : fract b (fract b m) = fract b m
-/
theorem fract_mem_fundamentalDomain (x : E) : fract b x ∈ fundamentalDomain b :=
  fract_eq_self.mp (fract_fract b _)

/-- The map `fract` with codomain restricted to `fundamentalDomain`. -/
/-
**ZSpan.fractRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：fractRestrict (x : E) : fundamentalDomain b
参数：x : E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZSpan.fract_mem_fundamentalDomain`：fract_mem_fundamentalDomain (x : E) :
 fract b x in fundamentalDomain b

--- 原说明 ---
The map `fract` with codomain restricted to `fundamentalDomain`.
-/
def fractRestrict (x : E) : fundamentalDomain b := ⟨fract b x, fract_mem_fundamentalDomain b x⟩
/-
**ZSpan.fractRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fractRestrict_surjective : Function.Surjective (fractRestrict b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZSpan.fract_eq_self`：fract_eq_self {x : E} : fract b x = x ↔ x in fundam
entalDomain b
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem fractRestrict_surjective : Function.Surjective (fractRestrict b) :=
  fun x => ⟨↑x, Subtype.ext (fract_eq_self.mpr (Subtype.mem x))⟩

@[simp]
/-
**ZSpan.fractRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fractRestrict_apply (x : E) : (fractRestrict b x : E) = fract b x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fractRestrict_apply (x : E) : (fractRestrict b x : E) = fract b x := rfl
/-
**ZSpan.fract_eq_fract** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fract_eq_fract (m n : E) : fract b m = fract b n ↔ -m + n in span Int (Set
.range b)
参数：m n : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
（共 38 条，此处仅展示前 30 条）
-/
theorem fract_eq_fract (m n : E) : fract b m = fract b n ↔ -m + n ∈ span ℤ (Set.range b) := by
  rw [eq_comm, Basis.ext_elem_iff b]
  simp_rw [repr_fract_apply, Int.fract_eq_fract, eq_comm, Basis.mem_span_iff_repr_mem,
    sub_eq_neg_add, map_add, map_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply,
    Pi.neg_apply, ← eq_intCast (algebraMap ℤ K) _, Set.mem_range]
/-
**ZSpan.norm_fract_le** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m‖ <= ∑ i, ‖b i‖
参数：m : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `norm_le_norm_of_abs_le_abs`：norm_le_norm_of_abs_le_abs {a b : α} (h : |a
| <= |b|) : ‖a‖ <= ‖b‖
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.abs_fract`：abs_fract : |fract a| = fract a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m‖ ≤ ∑ i, ‖b i‖ := by
  calc
    ‖fract b m‖ = ‖∑ i, b.repr (fract b m) i • b i‖ := by rw [b.sum_repr]
    _ = ‖∑ i, Int.fract (b.repr m i) • b i‖ := by simp_rw [repr_fract_apply]
    _ ≤ ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖Int.fract (b.repr m i)‖ * ‖b i‖ := by simp_rw [norm_smul]
    _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
  suffices ‖Int.fract ((b.repr m) i)‖ ≤ 1 by
    convert! mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i‖)
    exact (one_mul _).symm
  rw [(norm_one.symm : 1 = ‖(1 : K)‖)]
  apply norm_le_norm_of_abs_le_abs
  rw [abs_one, Int.abs_fract]
  exact le_of_lt (Int.fract_lt_one _)

section Unique

variable [Unique ι]

@[simp]
/-
**ZSpan.coe_floor_self** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：coe_floor_self (k : K) : (floor (Basis.singleton ι K) k : K) = ⌊k⌋
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_floor_apply`：repr_floor_apply (m : E) (i : ι) : b.repr (floor
 b m) i = ⌊b.repr m i⌋
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
-/
theorem coe_floor_self (k : K) : (floor (Basis.singleton ι K) k : K) = ⌊k⌋ :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_floor_apply, Basis.singleton_repr, Basis.singleton_repr]

@[simp]
/-
**ZSpan.coe_fract_self** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：coe_fract_self (k : K) : (fract (Basis.singleton ι K) k : K) = Int.fract k
参数：k : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.repr_fract_apply`：repr_fract_apply (m : E) (i : ι) : b.repr (fract
 b m) i = Int.fract (b.repr m i)
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
-/
theorem coe_fract_self (k : K) : (fract (Basis.singleton ι K) k : K) = Int.fract k :=
  Basis.ext_elem (Basis.singleton ι K) fun _ => by
    rw [repr_fract_apply, Basis.singleton_repr, Basis.singleton_repr]

end Unique

end Fintype

/-
**ZSpan.fundamentalDomain_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain_isBounded [Finite ι] [HasSolidNorm K] : IsBounded (funda
mentalDomain b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZSpan.fract_eq_self`：fract_eq_self {x : E} : fract b x = x ↔ x in fundam
entalDomain b
· 使用定理 `ZSpan.norm_fract_le`：norm_fract_le [HasSolidNorm K] (m : E) : ‖fract b m
‖ <= ∑ i, ‖b i‖
-/
theorem fundamentalDomain_isBounded [Finite ι] [HasSolidNorm K] :
    IsBounded (fundamentalDomain b) := by
  cases nonempty_fintype ι
  refine isBounded_iff_forall_norm_le.2 ⟨∑ j, ‖b j‖, fun x hx ↦ ?_⟩
  rw [← fract_eq_self.mpr hx]
  apply norm_fract_le
/-
**ZSpan.vadd_mem_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：vadd_mem_fundamentalDomain [Fintype ι] (y : span Int (Set.range b)) (x : E
) : y +ᵥ x in fundamentalDomain b ↔ y = -floor b x
参数：y : span Int (Set.range b)；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `NegMemClass.coe_neg`：∀ {G : Type u_1} [inst : AddGroup G] {S : Type u_4}
 {H : S} [inst_1 : SetLike S G] [inst_2 : AddSubgroupClass S G]   (x : ↥H), ↑(-x
) = -↑x
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ZSpan.fract_apply`：fract_apply (m : E) : fract b m = m - floor b m
· 使用定理 `ZSpan.fract_zSpan_add`：fract_zSpan_add (m : E) {v : E} (h : v in span In
t (Set.range b)) : fract b (v + m) = fract b m
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `Submodule.vadd_def`：vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : 
M) +ᵥ m
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ZSpan.fract_eq_self`：fract_eq_self {x : E} : fract b x = x ↔ x in fundam
entalDomain b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem vadd_mem_fundamentalDomain [Fintype ι] (y : span ℤ (Set.range b)) (x : E) :
    y +ᵥ x ∈ fundamentalDomain b ↔ y = -floor b x := by
  rw [Subtype.ext_iff, ← add_right_inj x, NegMemClass.coe_neg, ← sub_eq_add_neg, ← fract_apply,
    ← fract_zSpan_add b _ (Subtype.mem y), add_comm, ← vadd_eq_add, ← vadd_def, eq_comm, ←
    fract_eq_self]
/-
**ZSpan.exist_unique_vadd_mem_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan
`。
形式化陈述：exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) : exists! v : s
pan Int (Set.range b), v +ᵥ x in fundamentalDomain b
参数：x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZSpan.vadd_mem_fundamentalDomain`：vadd_mem_fundamentalDomain [Fintype ι]
 (y : span Int (Set.range b)) (x : E) : y +ᵥ x in fundamentalDomain b ↔ y = -flo
or b x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) :
    ∃! v : span ℤ (Set.range b), v +ᵥ x ∈ fundamentalDomain b := by
  cases nonempty_fintype ι
  refine ⟨-floor b x, ?_, fun y h => ?_⟩
  · exact (vadd_mem_fundamentalDomain b (-floor b x) x).mpr rfl
  · exact (vadd_mem_fundamentalDomain b y x).mp h

set_option backward.isDefEq.respectTransparency false in
/-- The map `ZSpan.fractRestrict` defines an equiv map between `E ⧸ span ℤ (Set.range b)`
and `ZSpan.fundamentalDomain b`. -/
/-
**ZSpan.quotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ZSpan`。
形式化陈述：quotientEquiv [Fintype ι] : E ⧸ span Int (Set.range b) ≃ (fundamentalDomai
n b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ZSpan.fractRestrict` defines an equiv map between `E ⧸ span ℤ (Set.rang
e b)`
and `ZSpan.fundamentalDomain b`.
-/
def quotientEquiv [Fintype ι] :
    E ⧸ span ℤ (Set.range b) ≃ (fundamentalDomain b) := by
  refine Equiv.ofBijective ?_ ⟨fun x y => ?_, fun x => ?_⟩
  · refine fun q => Quotient.liftOn q (fractRestrict b) (fun _ _ h => ?_)
    rw [Subtype.mk.injEq, fractRestrict_apply, fractRestrict_apply, fract_eq_fract]
    exact QuotientAddGroup.leftRel_apply.mp h
  · induction x, y using Quotient.inductionOn₂
    intro hxy
    rw [Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))), fractRestrict,
      Quotient.liftOn_mk (s := quotientRel (span ℤ (Set.range b))), fractRestrict,
      Subtype.mk.injEq] at hxy
    apply Quotient.sound'
    rwa [QuotientAddGroup.leftRel_apply, mem_toAddSubgroup, ← fract_eq_fract]
  · obtain ⟨a, rfl⟩ := fractRestrict_surjective b x
    exact ⟨Quotient.mk'' a, rfl⟩

@[simp]
/-
**ZSpan.quotientEquiv_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：quotientEquiv_apply_mk [Fintype ι] (x : E) : quotientEquiv b (Submodule.Qu
otient.mk x) = fractRestrict b x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientEquiv_apply_mk [Fintype ι] (x : E) :
    quotientEquiv b (Submodule.Quotient.mk x) = fractRestrict b x := rfl

@[simp]
/-
**ZSpan.quotientEquiv.symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan.quotientEquiv`
。
形式化陈述：∀ {E : Type u_1} {ι : Type u_2} {K : Type u_3} [inst : NormedField K] [ins
t_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace K E] (b : Module.Basis ι K E
) [inst_3 : LinearOrder K] [inst_4 : IsStrictOrderedRing K]   [inst_5 : FloorRin
g K] [inst_6 : Fintype ι] (x : ↑(ZSpan.fundamentalDomain b)),   (ZSpan.quotientE
quiv b).symm x = Submodule.Quotient.mk ↑x
参数：b : Module.Basis ι K E；x : ↑(ZSpan.fundamentalDomain b)；ZSpan.quotientEquiv b
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `ZSpan.quotientEquiv_apply_mk`：quotientEquiv_apply_mk [Fintype ι] (x : E)
 : quotientEquiv b (Submodule.Quotient.mk x) = fractRestrict b x
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `ZSpan.fractRestrict_apply`：fractRestrict_apply (x : E) : (fractRestrict 
b x : E) = fract b x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZSpan.fract_eq_self`：fract_eq_self {x : E} : fract b x = x ↔ x in fundam
entalDomain b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem quotientEquiv.symm_apply [Fintype ι] (x : fundamentalDomain b) :
    (quotientEquiv b).symm x = Submodule.Quotient.mk ↑x := by
  rw [Equiv.symm_apply_eq, quotientEquiv_apply_mk b ↑x, Subtype.ext_iff, fractRestrict_apply]
  exact (fract_eq_self.mpr x.prop).symm

end NormedLatticeField

section Real

/-
**ZSpan.discreteTopology_pi_basisFun** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：discreteTopology_pi_basisFun [Finite ι] : DiscreteTopology (span Int (Set.
range (Pi.basisFun Real ι)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `discreteTopology_iff_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   DiscreteTopo
logy G ↔ IsOpen {0}
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `pi_norm_lt_iff`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [
inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r : ℝ}, 0 < 
r → …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.mem_span_iff_repr_mem`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [IsDomain R] [inst_2 : Ring S]   [
Nontrivial S] [inst_4 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 40 条，此处仅展示前 30 条）
-/
theorem discreteTopology_pi_basisFun [Finite ι] :
    DiscreteTopology (span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  cases nonempty_fintype ι
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_⟩
  ext x
  rw [Set.mem_preimage, mem_ball_zero_iff, pi_norm_lt_iff zero_lt_one, Set.mem_singleton_iff]
  simp_rw [← coe_eq_zero, funext_iff, Pi.zero_apply, Real.norm_eq_abs]
  refine forall_congr' (fun i => ?_)
  rsuffices ⟨y, hy⟩ : ∃ (y : ℤ), (y : ℝ) = (x : ι → ℝ) i
  · rw [← hy, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff, Int.cast_eq_zero]
  exact ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ x).mp (SetLike.coe_mem x) i

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)
/-
**ZSpan.fundamentalDomain_subset_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan
`。
形式化陈述：fundamentalDomain_subset_parallelepiped [Fintype ι] : fundamentalDomain b 
subseteq parallelepiped b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.fundamentalDomain.eq_1`：∀ {E : Type u_1} {ι : Type u_2} {K : Type 
u_3} [inst : NormedField K] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace K E] (b : Modu…
· 使用定理 `parallelepiped_basis_eq`：parallelepiped_basis_eq (b : Basis ι Real E) : 
parallelepiped b = {x | forall i, b.repr x i in Set.Icc 0 1}
· 使用定理 `Set.ofPred_subset_ofPred`：ofPred_subset_ofPred {p q : α -> Prop} : { a |
 p a } subseteq { a | q a } ↔ forall a, p a -> q a
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
theorem fundamentalDomain_subset_parallelepiped [Fintype ι] :
    fundamentalDomain b ⊆ parallelepiped b := by
  rw [fundamentalDomain, parallelepiped_basis_eq, Set.ofPred_subset_ofPred]
  exact fun _ h i ↦ Set.Ico_subset_Icc_self (h i)
/-
**ZSpan.** 是 Mathlib 中的一个实例，位于命名空间 `ZSpan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] : DiscreteTopology (span ℤ (Set.range b)) := by
  have h : Set.MapsTo b.equivFun (span ℤ (Set.range b)) (span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
    intro _ hx
    rwa [SetLike.mem_coe, Basis.mem_span_iff_repr_mem] at hx ⊢
  convert! DiscreteTopology.of_continuous_injective ((continuous_equivFun_basis b).restrict h) ?_
  · exact discreteTopology_pi_basisFun
  · refine Subtype.map_injective _ (Basis.equivFun b).injective
/-
**ZSpan.** 是 Mathlib 中的一个实例，位于命名空间 `ZSpan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite ι] : DiscreteTopology (span ℤ (Set.range b)).toAddSubgroup :=
  inferInstanceAs <| DiscreteTopology (span ℤ (Set.range b))
/-
**ZSpan.setFinite_inter** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：setFinite_inter [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsB
ounded s) : Set.Finite (s inter span Int (Set.range b))
参数：hs : Bornology.IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfF
inite`：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : N
ormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι], DiscreteTopo…
· 使用定理 `Metric.finite_isBounded_inter_isClosed`：Metric.finite_isBounded_inter_is
Closed [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s) (hK : IsBounded K) (hs
 : IsClosed s) : Set.Finite …
· 使用引理 `DiscreteTopology.isDiscrete`：DiscreteTopology.isDiscrete [DiscreteTopolo
gy s] : IsDiscrete s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_toAddSubgroup`：coe_toAddSubgroup : (p.toAddSubgroup : Set 
M) = p
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem setFinite_inter [ProperSpace E] [Finite ι] {s : Set E} (hs : Bornology.IsBounded s) :
    Set.Finite (s ∩ span ℤ (Set.range b)) := by
  have : DiscreteTopology (span ℤ (Set.range b)) := inferInstance
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs ?_
  rw [← coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete

@[measurability]
/-
**ZSpan.fundamentalDomain_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace 
E] [Finite ι] : MeasurableSet (fundamentalDomain b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `measurableSet_preimage`：measurableSet_preimage {t : Set β} (hf : Measura
ble f) (ht : MeasurableSet t) : MeasurableSet (f ⁻¹' t)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
（共 34 条，此处仅展示前 30 条）
-/
theorem fundamentalDomain_measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] :
    MeasurableSet (fundamentalDomain b) := by
  cases nonempty_fintype ι
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  let D : Set (ι → ℝ) := Set.pi Set.univ fun _ : ι => Set.Ico (0 : ℝ) 1
  rw [(_ : fundamentalDomain b = b.equivFun.toLinearMap ⁻¹' D)]
  · refine measurableSet_preimage (LinearMap.continuous_of_finiteDimensional _).measurable ?_
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  · ext
    simp only [D, fundamentalDomain, Set.mem_Ico, Set.mem_ofPred_eq, LinearEquiv.coe_coe,
      Set.mem_preimage, Basis.equivFun_apply, Set.mem_pi, Set.mem_univ, forall_true_left]

/-- For a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that the set defined
by `ZSpan.fundamentalDomain` is a fundamental domain. -/
/-
**ZSpan.isAddFundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι] [inst_3 : MeasurableSpace E
] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E),   MeasureTheory.IsAddF
undamentalDomain (↥(Submodule.span ℤ (Set.range ⇑b))) (ZSpan.fundamentalDomain b
) μ
参数：b : Module.Basis ι ℝ E；μ : MeasureTheory.Measure E；↥(Submodule.span ℤ (Set.ra
nge ⇑b))；ZSpan.fundamentalDomain b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.mk'`：∀ {G : Type u_1} {α : Type u_3
} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableSpace α] {s :
 Set α}   {μ : MeasureTheory.M…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `ZSpan.fundamentalDomain_measurableSet`：fundamentalDomain_measurableSet [
MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] : MeasurableSet (fundamen
talDomain b)
· 使用定理 `ZSpan.exist_unique_vadd_mem_fundamentalDomain`：exist_unique_vadd_mem_fun
damentalDomain [Finite ι] (x : E) : exists! v : span Int (Set.range b), v +ᵥ x i
n fundamentalDomain b

--- 原说明 ---
For a ℤ-lattice `Submodule.span ℤ (Set.range b)`, proves that the set defined
by `ZSpan.fundamentalDomain` is a fundamental domain.
-/
protected theorem isAddFundamentalDomain [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)) (fundamentalDomain b) μ := by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (fundamentalDomain_measurableSet b))
    fun x => exist_unique_vadd_mem_fundamentalDomain b x

/-- A version of `ZSpan.isAddFundamentalDomain` for `AddSubgroup`. -/
/-
**ZSpan.isAddFundamentalDomain'** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι] [inst_3 : MeasurableSpace E
] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E),   MeasureTheory.IsAddF
undamentalDomain (↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup) (ZSpan.funda
mentalDomain b) μ
参数：b : Module.Basis ι ℝ E；μ : MeasureTheory.Measure E；↥(Submodule.span ℤ (Set.ra
nge ⇑b)).toAddSubgroup；ZSpan.fundamentalDomain b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZSpan.isAddFundamentalDomain`：∀ {E : Type u_1} {ι : Type u_2} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finit
e ι] [inst_3 : Mea…

--- 原说明 ---
A version of `ZSpan.isAddFundamentalDomain` for `AddSubgroup`.
-/
protected theorem isAddFundamentalDomain' [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)).toAddSubgroup (fundamentalDomain b) μ :=
  ZSpan.isAddFundamentalDomain b μ
/-
**ZSpan.measure_fundamentalDomain_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：measure_fundamentalDomain_ne_zero [Finite ι] [MeasurableSpace E] [BorelSpa
ce E] {μ : Measure E} [Measure.IsAddHaarMeasure μ] : μ (fundamentalDomain b) != 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.measure_ne_zero`：∀ {G : Type u_1} {
α : Type u_3} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableS
pace α] {s : Set α}   {μ : MeasureTheory.M…
· 使用定理 `Finsupp.instCountableSubtypeMemSubmoduleSpanRange`：∀ {M : Type u_1} {R :
 Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   {ι : Type u_3} [Countable R] […
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroOfNonempty`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {m : MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpen
PosMeasure]   [Nonempty X], NeZe…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `ZSpan.isAddFundamentalDomain`：∀ {E : Type u_1} {ι : Type u_2} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finit
e ι] [inst_3 : Mea…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem measure_fundamentalDomain_ne_zero [Finite ι] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    μ (fundamentalDomain b) ≠ 0 := by
  convert! (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
  exact inferInstanceAs <| VAddInvariantMeasure (span ℤ (Set.range b)).toAddSubgroup E μ
/-
**ZSpan.measure_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：measure_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace E] 
(μ : Measure E) [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι Real E
) : μ (fundamentalDomain b) = ENNReal.ofReal |b₀.det b| * μ (fundamentalDomain b
₀)
参数：μ : Measure E；b₀ : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {f : α -> β} (hf 
: Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `ZSpan.map_fundamentalDomain`：map_fundamentalDomain {F : Type*} [NormedAd
dCommGroup F] [NormedSpace K F] (f : E ≃ₗ[K] F) : f '' (fundamentalDomain b) = f
undamentalDomain …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.map_equiv`：map_equiv (b : Basis ι R M) (b' : Basis ι' R M')
 (e : ι ≃ ι') : b.map (b.equiv b' e) = b'.reindex e.symm
· 使用定理 `Equiv.refl_symm`：∀ {α : Sort u}, (Equiv.refl α).symm = Equiv.refl α
· 使用定理 `Module.Basis.reindex_refl`：reindex_refl : b.reindex (Equiv.refl ι) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.equiv_symm`：equiv_symm : (b.equiv b' e).symm = b'.equiv b e
.symm
· 使用定理 `Module.Basis.det_basis`：det_basis (b : Basis ι A M) (b' : Basis ι A M) :
 LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.addHaar_preimage_linearEquiv`：addHaar_preimage_lin
earEquiv (f : E ≃ₗ[Real] E) (s : Set E) : μ (f ⁻¹' s) = ENNReal.ofReal |LinearMa
p.det (f.symm : E ->ₗ[Real] E)| * μ s
-/
theorem measure_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι ℝ E) :
    μ (fundamentalDomain b) = ENNReal.ofReal |b₀.det b| * μ (fundamentalDomain b₀) := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  convert! μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), map_fundamentalDomain,
      Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl]
  · simp
/-
**ZSpan.measureReal_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：measureReal_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace
 E] (μ : Measure E) [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι Re
al E) : μ.real (fundamentalDomain b) = |b₀.det b| * μ.real (fundamentalDomain b₀
)
参数：μ : Measure E；b₀ : Basis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.measure_fundamentalDomain`：measure_fundamentalDomain [Fintype ι] [
DecidableEq ι] [MeasurableSpace E] (μ : Measure E) [BorelSpace E] [Measure.IsAdd
HaarMeasure μ] (b₀ : …
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measureReal_fundamentalDomain
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Basis ι ℝ E) :
    μ.real (fundamentalDomain b) = |b₀.det b| * μ.real (fundamentalDomain b₀) := by
  simp [measureReal_def, measure_fundamentalDomain b μ b₀]

@[simp]
/-
**ZSpan.volume_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι Real (ι 
-> Real)) : volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det|
参数：b : Basis ι Real (ι -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.measure_fundamentalDomain`：measure_fundamentalDomain [Fintype ι] [
DecidableEq ι] [MeasurableSpace E] (μ : Measure E) [BorelSpace E] [Measure.IsAdd
HaarMeasure μ] (b₀ : …
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用引理 `ZSpan.fundamentalDomain_pi_basisFun`：fundamentalDomain_pi_basisFun [Fint
ype ι] : fundamentalDomain (Pi.basisFun Real ι) = Set.pi Set.univ fun _ : ι => S
et.Ico (0 : Real) 1
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `Real.volume_Ico`：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
theorem volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ι → ℝ)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
  rw [measure_fundamentalDomain b volume (b₀ := Pi.basisFun ℝ ι), fundamentalDomain_pi_basisFun,
    volume_pi, Measure.pi_pi, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
    mul_one, ← Matrix.det_transpose]
  rfl

@[simp]
/-
**ZSpan.volume_real_fundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：volume_real_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι Rea
l (ι -> Real)) : volume.real (fundamentalDomain b) = |(Matrix.of b).det|
参数：b : Basis ι Real (ι -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZSpan.volume_fundamentalDomain`：volume_fundamentalDomain [Fintype ι] [De
cidableEq ι] (b : Basis ι Real (ι -> Real)) : volume (fundamentalDomain b) = ENN
Real.ofReal |(Matrix…
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (ι → ℝ)) :
    volume.real (fundamentalDomain b) = |(Matrix.of b).det| := by
  simp [measureReal_def]
/-
**ZSpan.fundamentalDomain_ae_parallelepiped** 是 Mathlib 中的一个定理，位于命名空间 `ZSpan`。
形式化陈述：fundamentalDomain_ae_parallelepiped [Fintype ι] [MeasurableSpace E] (μ : M
easure E) [BorelSpace E] [Measure.IsAddHaarMeasure μ] : fundamentalDomain b =ᵐ[μ
] parallelepiped b
参数：μ : Measure E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_symmDiff_eq_zero_iff`：measure_symmDiff_eq_zero_iff
 {s t : Set α} : μ (s ∆ t) = 0 ↔ s =ᵐ[μ] t
· 使用定理 `symmDiff_of_le`：symmDiff_of_le {a b : α} (h : a <= b) : a ∆ b = b \ a
· 使用定理 `ZSpan.fundamentalDomain_subset_parallelepiped`：fundamentalDomain_subset_
parallelepiped [Fintype ι] : fundamentalDomain b subseteq parallelepiped b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `parallelepiped_basis_eq`：parallelepiped_basis_eq (b : Basis ι Real E) : 
parallelepiped b = {x | forall i, b.repr x i in Set.Icc 0 1}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `Finset.sum_erase_add`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → ∑ 
x ∈ s.eras…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `AffineSubspace.vadd_mem_mk'`：vadd_mem_mk' {v : V} (p : P) {direction : S
ubmodule k V} (hv : v in direction) : v +ᵥ p in mk' p direction
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `Set.mem_sdiff_singleton`：mem_sdiff_singleton : a in s \ {b} ↔ a in s ∧ a
 != b
· 使用定理 `trivial`：True
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
（共 43 条，此处仅展示前 30 条）
-/
theorem fundamentalDomain_ae_parallelepiped [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] :
    fundamentalDomain b =ᵐ[μ] parallelepiped b := by
  classical
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  rw [← measure_symmDiff_eq_zero_iff, symmDiff_of_le (fundamentalDomain_subset_parallelepiped b)]
  suffices (parallelepiped b \ fundamentalDomain b) ⊆ ⋃ i,
      AffineSubspace.mk' (b i) (span ℝ (b '' (Set.univ \ {i}))) by
    refine measure_mono_null this
      (measure_iUnion_null_iff.mpr fun i ↦ Measure.addHaar_affineSubspace μ _ ?_)
    refine (ne_of_mem_of_not_mem' (AffineSubspace.mem_top _ _ 0)
      (AffineSubspace.mem_mk'.not.mpr ?_)).symm
    simp_rw [vsub_eq_sub, zero_sub, neg_mem_iff]
    exact linearIndependent_iff_notMem_span.mp b.linearIndependent i
  intro x hx
  simp_rw [parallelepiped_basis_eq, Set.mem_Icc, Set.mem_sdiff, Set.mem_ofPred_eq,
    mem_fundamentalDomain, Set.mem_Ico, not_forall, not_and, not_lt] at hx
  obtain ⟨i, hi⟩ := hx.2
  have : b.repr x i = 1 := le_antisymm (hx.1 i).2 (hi (hx.1 i).1)
  rw [← b.sum_repr x, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), this, one_smul, ← vadd_eq_add]
  refine Set.mem_iUnion.mpr ⟨i, AffineSubspace.vadd_mem_mk' _
    (sum_smul_mem _ _ (fun i hi ↦ Submodule.subset_span ?_))⟩
  exact ⟨i, Set.mem_sdiff_singleton.mpr ⟨trivial, Finset.ne_of_mem_erase hi⟩, rfl⟩

end Real

end ZSpan

section ZLattice

open Submodule Module ZSpan

-- TODO: generalize this class to other rings than `ℤ`
/-- `L : Submodule ℤ E` where `E` is a vector space over a normed field `K` is a `ℤ`-lattice if
it is discrete and spans `E` over `K`. -/
/-
**IsZLattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) →   [inst : NormedField K] →     {E : Type u_2} →       [in
st_1 : NormedAddCommGroup E] → [NormedSpace K E] → (L : Submodule ℤ E) → [Discre
teTopology ↥L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`L : Submodule ℤ E` where `E` is a vector space over a normed field `K` is a `ℤ`
-lattice if
it is discrete and spans `E` over `K`.
-/
class IsZLattice (K : Type*) [NormedField K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (L : Submodule ℤ E) [DiscreteTopology L] : Prop where
  /-- `L` spans the full space `E` over `K`. -/
  span_top : span K (L : Set E) = ⊤
/-
**instIsZLatticeRealSpan** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsZLatticeRealSpan {E ι : Type*} [NormedAddCommGroup E] [NormedSpace R
eal E] [Finite ι] (b : Basis ι Real E) : IsZLattice Real (span Int (Set.range b)
) where span_top
参数：b : Basis ι Real E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfF
inite`：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : N
ormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι], DiscreteTopo…
· 使用定理 `ZSpan.span_top`：span_top : span K (span Int (Set.range b) : Set E) = ⊤
-/
instance instIsZLatticeRealSpan {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Finite ι] (b : Basis ι ℝ E) :
    IsZLattice ℝ (span ℤ (Set.range b)) where
  span_top := ZSpan.span_top b

section NormedLinearOrderedField

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

/-
**ZLattice.FG** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.FG [hs : IsZLattice K L] : L.FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `Submodule.fg_of_fg_map_of_fg_inf_ker`：fg_of_fg_map_of_fg_inf_ker (f : M 
->ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).FG) (hs2 : (s ⊓ LinearMap.ker f).
FG) : s.FG
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsZLattice.span_top`：∀ {K : Type u_1} {inst : NormedField K} {E : Type u
_2} {inst_1 : NormedAddCommGroup E} {inst_2 : NormedSpace K E}   {L : Submodule 
ℤ E} {ins…
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.setFinite`：setFinite [Module.Finite R M] {b : Set M} (
h : LinearIndependent R fun x : b => (x : M)) : b.Finite
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Metric.finite_isBounded_inter_isClosed`：Metric.finite_isBounded_inter_is
Closed [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s) (hK : IsBounded K) (hs
 : IsClosed s) : Set.Finite …
· 使用引理 `DiscreteTopology.isDiscrete`：DiscreteTopology.isDiscrete [DiscreteTopolo
gy s] : IsDiscrete s
· 使用定理 `ZSpan.fundamentalDomain_isBounded`：fundamentalDomain_isBounded [Finite ι
] [HasSolidNorm K] : IsBounded (fundamentalDomain b)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AddSubgroup.isClosed_of_discrete`：∀ {G : Type u_1} [inst : AddGroup G] [
inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {H : AddSub
group G} [DiscreteTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `ZSpan.quotientEquiv_apply_mk`：quotientEquiv_apply_mk [Fintype ι] (x : E)
 : quotientEquiv b (Submodule.Quotient.mk x) = fractRestrict b x
（共 52 条，此处仅展示前 30 条）
-/
theorem ZLattice.FG [hs : IsZLattice K L] : L.FG := by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 0` with `span ℤ s` and `L ⧸ span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (span ℤ s).mkQ ?_ ?_
  · -- Let `b` be the `K`-basis of `E` formed by the vectors in `s`. The elements of
    -- `L ⧸ span ℤ s = L ⧸ span ℤ b` are in bijection with elements of `L ∩ fundamentalDomain b`
    -- so there are finitely many since `fundamentalDomain b` is bounded.
    refine fg_def.mpr ⟨map (span ℤ s).mkQ L, ?_, span_eq _⟩
    let b := Basis.mk h_lind (by
      rw [← hs.span_top, ← h_span]
      exact span_mono (by simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, subset_rfl]))
    rw [show span ℤ s = span ℤ (Set.range b) by simp [b, Basis.coe_mk, Subtype.range_coe_subtype]]
    have : Fintype s := h_lind.setFinite.fintype
    refine Set.Finite.of_finite_image (f := ((↑) : _ → E) ∘ quotientEquiv b) ?_
      (Function.Injective.injOn (Subtype.coe_injective.comp (quotientEquiv b).injective))
    have : ((fundamentalDomain b) ∩ L).Finite := by
      change ((fundamentalDomain b) ∩ L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed
        DiscreteTopology.isDiscrete (fundamentalDomain_isBounded b) inferInstance
    refine Set.Finite.subset this ?_
    rintro _ ⟨_, ⟨⟨x, ⟨h_mem, rfl⟩⟩, rfl⟩⟩
    rw [Function.comp_apply, mkQ_apply, quotientEquiv_apply_mk, fractRestrict_apply]
    refine ⟨?_, ?_⟩
    · exact fract_mem_fundamentalDomain b x
    · rw [fract, SetLike.mem_coe, sub_eq_add_neg]
      refine Submodule.add_mem _ h_mem
        (neg_mem (Set.mem_of_subset_of_mem ?_ (Subtype.mem (floor b x))))
      rw [SetLike.coe_subset_coe, Basis.coe_mk, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
      exact span_le.mpr h_incl
  · -- `span ℤ s` is finitely generated because `s` is finite
    rw [ker_mkQ, inf_of_le_right (span_le.mpr h_incl)]
    exact fg_span (LinearIndependent.setFinite h_lind)
/-
**ZLattice.module_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.module_finite [IsZLattice K L] : Module.Finite Int L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `ZLattice.FG`：ZLattice.FG [hs : IsZLattice K L] : L.FG
-/
theorem ZLattice.module_finite [IsZLattice K L] : Module.Finite ℤ L :=
  .of_fg (ZLattice.FG K L)
/-
**instModuleFinite_of_discrete_submodule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instModuleFinite_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] 
[NormedSpace Real E] [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteT
opology L] : Module.Finite Int L
参数：L : Submodule Int E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `Submodule.map_comap_eq_self`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `DiscreteTopology.preimage_of_continuous_injective`：DiscreteTopology.prei
mage_of_continuous_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpac
e Y] (s : Set Y) [DiscreteTopology s] {…
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `ZLattice.module_finite`：ZLattice.module_finite [IsZLattice K L] : Module
.Finite Int L
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
instance instModuleFinite_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.Finite ℤ L := by
  let f := (span ℝ (L : Set E)).subtype
  let L₀ := L.comap (f.restrictScalars ℤ)
  have h_img : f '' L₀ = L := by
    rw [← LinearMap.coe_restrictScalars ℤ f, ← Submodule.map_coe (f.restrictScalars ℤ),
      Submodule.map_comap_eq_self]
    exact fun x hx ↦ LinearMap.mem_range.mpr ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  suffices Module.Finite ℤ L₀ by
    have : L₀.map (f.restrictScalars ℤ) = L :=
      SetLike.ext'_iff.mpr h_img
    convert! this ▸ Module.Finite.map L₀ (f.restrictScalars ℤ)
  have : DiscreteTopology L₀ := by
    refine DiscreteTopology.preimage_of_continuous_injective (L : Set E) ?_ (injective_subtype _)
    exact LinearMap.continuous_of_finiteDimensional f
  have : IsZLattice ℝ L₀ := ⟨by
    rw [← (Submodule.map_injective_of_injective (injective_subtype _)).eq_iff, Submodule.map_span,
      Submodule.map_top, range_subtype, h_img]⟩
  exact ZLattice.module_finite ℝ L₀
/-
**ZLattice.module_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.module_free [IsZLattice K L] : Module.Free Int L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZLattice.module_finite`：ZLattice.module_finite [IsZLattice K L] : Module
.Finite Int L
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `IsAddTorsionFree.of_module_rat`：IsAddTorsionFree.of_module_rat [AddCommG
roup M] [Module Rat M] : IsAddTorsionFree M where nsmul_right_injective n hn x y
 hxy
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
-/
theorem ZLattice.module_free [IsZLattice K L] : Module.Free ℤ L := by
  have : Module.Finite ℤ L := module_finite K L
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance
/-
**instModuleFree_of_discrete_submodule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instModuleFree_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] [N
ormedSpace Real E] [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteTop
ology L] : Module.Free Int L
参数：L : Submodule Int E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `IsAddTorsionFree.of_module_rat`：IsAddTorsionFree.of_module_rat [AddCommG
roup M] [Module Rat M] : IsAddTorsionFree M where nsmul_right_injective n hn x y
 hxy
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
-/
instance instModuleFree_of_discrete_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.Free ℤ L := by
  have : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)
  have : IsAddTorsionFree E := .of_module_rat _
  infer_instance
/-
**ZLattice.rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = finrank K E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZLattice.module_finite`：ZLattice.module_finite [IsZLattice K L] : Module
.Finite Int L
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `IsAddTorsionFree.of_module_rat`：IsAddTorsionFree.of_module_rat [AddCommG
roup M] [Module Rat M] : IsAddTorsionFree M where nsmul_right_injective n hn x y
 hxy
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `IsZLattice.span_top`：∀ {K : Type u_1} {inst : NormedField K} {E : Type u
_2} {inst_1 : NormedAddCommGroup E} {inst_2 : NormedSpace K E}   {L : Submodule 
ℤ E} {ins…
· 使用定理 `Set.toFinset_range`：toFinset_range [DecidableEq α] [Fintype β] (f : β ->
 α) [Fintype (Set.range f)] : (Set.range f).toFinset = Finset.univ.image f
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 93 条，此处仅展示前 30 条）
-/
theorem ZLattice.rank [hs : IsZLattice K L] : finrank ℤ L = finrank K E := by
  classical
  have : Module.Finite ℤ L := module_finite K L
  have : Module ℚ E := Module.compHom E (algebraMap ℚ K)
  have : IsAddTorsionFree E := .of_module_rat _
  let b₀ := Module.Free.chooseBasis ℤ L
  -- Let `b` be a `ℤ`-basis of `L` formed of vectors of `E`
  let b := Subtype.val ∘ b₀
  have : LinearIndependent ℤ b :=
    LinearIndependent.map' b₀.linearIndependent (L.subtype) (ker_subtype _)
  -- We prove some assertions that will be useful later on
  have h_spanL : span ℤ (Set.range b) = L := by
    convert! congrArg (map (Submodule.subtype L)) b₀.span_eq
    · rw [map_span, Set.range_comp]
      rfl
    · exact (map_subtype_top _).symm
  have h_spanE : span K (Set.range b) = ⊤ := by
    rw [← span_span_of_tower (R := ℤ), h_spanL]
    exact hs.span_top
  have h_card : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) =
      (Set.range b).toFinset.card := by
    rw [Set.toFinset_range, Finset.univ.card_image_of_injective]
    · rfl
    · exact Subtype.coe_injective.comp (Basis.injective _)
  rw [finrank_eq_card_chooseBasisIndex]
    -- We prove that `finrank ℤ L ≤ finrank K E` and `finrank K E ≤ finrank ℤ L`
  refine le_antisymm ?_ ?_
  · -- To prove that `finrank ℤ L ≤ finrank K E`, we proceed by contradiction and prove that, in
    -- this case, there is a ℤ-relation between the vectors of `b`
    obtain ⟨t, ⟨ht_inc, ⟨ht_span, ht_lin⟩⟩⟩ := exists_linearIndependent K (Set.range b)
    -- `e` is a `K`-basis of `E` formed of vectors of `b`
    let e : Basis t K E := Basis.mk ht_lin (by simp [ht_span, h_spanE])
    have : Fintype t := Set.Finite.fintype ((Set.range b).toFinite.subset ht_inc)
    have h : LinearIndepOn ℤ id (Set.range b) := by
      rwa [linearIndepOn_id_range_iff (Subtype.coe_injective.comp b₀.injective)]
    contrapose! h
    -- Since `finrank ℤ L > finrank K E`, there exists a vector `v ∈ b` with `v ∉ e`
    obtain ⟨v, hv⟩ : (Set.range b \ Set.range e).Nonempty := by
      rw [Basis.coe_mk, Subtype.range_coe_subtype, Set.ofPred_mem_eq, ← Set.toFinset_nonempty]
      contrapose! h
      rw [Set.toFinset_sdiff, Finset.sdiff_eq_empty_iff_subset] at h
      replace h := Finset.card_le_card h
      rwa [h_card, ← topEquiv.finrank_eq, ← h_spanE, ← ht_span, finrank_span_set_eq_card ht_lin]
    -- Assume that `e ∪ {v}` is not `ℤ`-linear independent then we get the contradiction
    suffices ¬ LinearIndepOn ℤ id (insert v (Set.range e)) by
      contrapose this
      refine this.mono ?_
      exact Set.insert_subset (Set.mem_of_mem_sdiff hv) (by simp [e, ht_inc])
    -- We prove finally that `e ∪ {v}` is not ℤ-linear independent or, equivalently,
    -- not ℚ-linear independent by showing that `v ∈ span ℚ e`.
    rw [LinearIndepOn, LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn,
      linearIndepOn_id_insert (Set.notMem_of_mem_sdiff hv), not_and, not_not]
    intro _
    -- But that follows from the fact that there exist `n, m : ℕ`, `n ≠ m`
    -- such that `(n - m) • v ∈ span ℤ e` which is true since `n ↦ ZSpan.fract e (n • v)`
    -- takes value into the finite set `fundamentalDomain e ∩ L`
    have h_mapsto : Set.MapsTo (fun n : ℤ => fract e (n • v)) Set.univ
        (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) := by
      rw [Set.mapsTo_inter, Set.mapsTo_univ_iff, Set.mapsTo_univ_iff]
      refine ⟨fun _ ↦ mem_closedBall_zero_iff.mpr (norm_fract_le e _), fun _ => ?_⟩
      · rw [← h_spanL]
        refine sub_mem ?_ ?_
        · exact zsmul_mem (subset_span (Set.sdiff_subset hv)) _
        · exact span_mono (by simp [e, ht_inc]) (coe_mem _)
    have h_finite : Set.Finite (Metric.closedBall 0 (∑ i, ‖e i‖) ∩ (L : Set E)) := by
      change ((_ : Set E) ∩ L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall inferInstance
    obtain ⟨n, -, m, -, h_ne, h_eq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
      Set.infinite_univ h_mapsto h_finite
    have h_nz : (-n + m : ℚ) ≠ 0 := by
      rwa [Ne, add_eq_zero_iff_eq_neg.not, neg_inj, Rat.intCast_inj, ← Ne]
    apply (smul_mem_iff _ h_nz).mp
    refine span_subset_span ℤ ℚ _ ?_
    rwa [add_smul, neg_smul, SetLike.mem_coe, ← fract_eq_fract, Int.cast_smul_eq_zsmul ℚ,
      Int.cast_smul_eq_zsmul ℚ]
  · -- To prove that `finrank K E ≤ finrank ℤ L`, we use the fact `b` generates `E` over `K`
    -- and thus `finrank K E ≤ card b = finrank ℤ L`
    rw [← topEquiv.finrank_eq, ← h_spanE]
    convert! finrank_span_le_card (R := K) (Set.range b)

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

namespace Module.Basis

/-- Any `ℤ`-basis of `L` is also a `K`-basis of `E`. -/
/-
**Module.Basis.ofZLatticeBasis** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofZLatticeBasis : Basis ι K E
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZLattice.module_finite`：ZLattice.module_finite [IsZLattice K L] : Module
.Finite Int L
· 使用定理 `ZLattice.module_free`：ZLattice.module_free [IsZLattice K L] : Module.Fre
e Int L
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R

--- 原说明 ---
Any `ℤ`-basis of `L` is also a `K`-basis of `E`.
-/
def ofZLatticeBasis : Basis ι K E := by
  have : Module.Finite ℤ L := ZLattice.module_finite K L
  have : Free ℤ L := ZLattice.module_free K L
  let e := (Free.chooseBasis ℤ L).indexEquiv b
  have : Fintype ι := Fintype.ofEquiv _ e
  refine basisOfTopLeSpanOfCardEqFinrank (L.subtype ∘ b) ?_ ?_
  · rw [← span_span_of_tower ℤ, Set.range_comp, ← map_span, Basis.span_eq, Submodule.map_top,
      range_subtype, top_le_iff, hs.span_top]
  · rw [← Fintype.card_congr e, ← finrank_eq_card_chooseBasisIndex, ZLattice.rank K L]

@[simp]
/-
**Module.Basis.ofZLatticeBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ofZLatticeBasis_apply (i : ι) : b.ofZLatticeBasis K L i = b i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZLattice.module_free`：ZLattice.module_free [IsZLattice K L] : Module.Fre
e Int L
· 使用定理 `ZLattice.module_finite`：ZLattice.module_finite [IsZLattice K L] : Module
.Finite Int L
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `coe_basisOfTopLeSpanOfCardEqFinrank`：coe_basisOfTopLeSpanOfCardEqFinrank
 {ι : Type*} [Fintype ι] (b : ι -> M) (le_span : ⊤ <= span R (Set.range b)) (car
d_eq : Fintype.card ι = f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZLatticeBasis_apply (i : ι) : b.ofZLatticeBasis K L i = b i := by
  simp [Basis.ofZLatticeBasis]

@[simp]
/-
**Module.Basis.ofZLatticeBasis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：ofZLatticeBasis_repr_apply (x : L) (i : ι) : (b.ofZLatticeBasis K L).repr 
x i = b.repr x i
参数：x : L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem ofZLatticeBasis_repr_apply (x : L) (i : ι) :
    (b.ofZLatticeBasis K L).repr x i = b.repr x i := by
  suffices ((b.ofZLatticeBasis K L).repr.toLinearMap.restrictScalars ℤ) ∘ₗ L.subtype
      = Finsupp.mapRange.linearMap (Algebra.linearMap ℤ K) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  refine Basis.ext b fun i ↦ ?_
  simp_rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, coe_subtype, ← b.ofZLatticeBasis_apply K, repr_self,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]
/-
**Module.Basis.ofZLatticeBasis_span** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ofZLatticeBasis_span : span Int (Set.range (b.ofZLatticeBasis K)) = L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZLatticeBasis_span : span ℤ (Set.range (b.ofZLatticeBasis K)) = L := by
  calc span ℤ (Set.range (b.ofZLatticeBasis K))
    _ = span ℤ (L.subtype '' Set.range b) := by congr; ext; simp
    _ = map L.subtype (span ℤ (Set.range b)) := by rw [Submodule.map_span]
    _ = L := by simp [b.span_eq]

end Module.Basis

open MeasureTheory in
/-
**ZLattice.isAddFundamentalDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.isAddFundamentalDomain {E : Type*} [NormedAddCommGroup E] [Normed
Space Real E] [FiniteDimensional Real E] {L : Submodule Int E} [DiscreteTopology
 L] [IsZLattice Real L] [Finite ι] (b : Basis ι Int L) [MeasurableSpace E] [Open
sMeasurableSpace E] (μ : Measure E) : IsAddFundamentalDomain L (fundamentalDomai
n (b.ofZLatticeBasis Real)) μ
参数：b : Basis ι Int L；μ : Measure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.ofZLatticeBasis_span`：ofZLatticeBasis_span : span Int (Set.
range (b.ofZLatticeBasis K)) = L
· 使用定理 `ZSpan.isAddFundamentalDomain`：∀ {E : Type u_1} {ι : Type u_2} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finit
e ι] [inst_3 : Mea…
-/
theorem ZLattice.isAddFundamentalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Basis ι ℤ L) [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) :
    IsAddFundamentalDomain L (fundamentalDomain (b.ofZLatticeBasis ℝ)) μ := by
  convert! ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis ℝ) μ
  all_goals exact (b.ofZLatticeBasis_span ℝ).symm
/-
**instCountable_of_discrete_submodule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instCountable_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] [No
rmedSpace Real E] [FiniteDimensional Real E] (L : Submodule Int E) [DiscreteTopo
logy L] [IsZLattice Real L] : Countable L
参数：L : Submodule Int E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.ofZLatticeBasis_span`：ofZLatticeBasis_span : span Int (Set.
range (b.ofZLatticeBasis K)) = L
· 使用定理 `Finsupp.instCountableSubtypeMemSubmoduleSpanRange`：∀ {M : Type u_1} {R :
 Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   {ι : Type u_3} [Countable R] […
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance instCountable_of_discrete_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Countable L := by
  simp_rw [← (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  infer_instance

/--
Assume that the set `s` spans over `ℤ` a discrete set. Then its `ℝ`-rank is equal to its `ℤ`-rank.
-/
/-
**Real.finrank_eq_int_finrank_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.finrank_eq_int_finrank_of_discrete {E : Type*} [NormedAddCommGroup E]
 [NormedSpace Real E] [FiniteDimensional Real E] {s : Set E} (hs : DiscreteTopol
ogy (span Int s)) : Set.finrank Real s = Set.finrank Int s
参数：hs : DiscreteTopology (span Int s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_coe_preimage`：span_span_coe_preimage : span R (((↑) 
: span R s -> M) ⁻¹' s) = ⊤
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.finrank.eq_1`：∀ (R : Type u) {M : Type v} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (s : Set M),   Set.finrank R s
 = Mod…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `ZLattice.rank`：ZLattice.rank [hs : IsZLattice K L] : finrank Int L = fin
rank K E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…

--- 原说明 ---
Assume that the set `s` spans over `ℤ` a discrete set. Then its `ℝ`-rank is equa
l to its `ℤ`-rank.
-/
theorem Real.finrank_eq_int_finrank_of_discrete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : DiscreteTopology (span ℤ s)) :
    Set.finrank ℝ s = Set.finrank ℤ s := by
  let F := span ℝ s
  let L : Submodule ℤ (span ℝ s) := comap (F.restrictScalars ℤ).subtype (span ℤ s)
  let f := Submodule.comapSubtypeEquivOfLe (span_le_restrictScalars ℤ ℝ s)
  have : DiscreteTopology L := by
    let e : span ℤ s ≃L[ℤ] L :=
      ⟨f.symm, continuous_of_discreteTopology, Isometry.continuous fun _ ↦ congrFun rfl⟩
    exact e.toHomeomorph.discreteTopology
  have : IsZLattice ℝ L := ⟨eq_top_iff.mpr <|
    span_span_coe_preimage.symm.le.trans (span_mono (Set.preimage_mono subset_span))⟩
  rw [Set.finrank, Set.finrank, ← f.finrank_eq]
  exact (ZLattice.rank ℝ L).symm

end NormedLinearOrderedField

section Basis

variable {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

/--
Return an arbitrary `ℤ`-basis of a lattice `L` of `ι → ℝ` indexed by `ι`.
-/
/-
**IsZLattice.basis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsZLattice.basis : Basis ι Int L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return an arbitrary `ℤ`-basis of a lattice `L` of `ι → ℝ` indexed by `ι`.
-/
def IsZLattice.basis : Basis ι ℤ L :=
  (Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq
    (by rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]))

end Basis

section comap

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

/-- Let `e : E → F` a linear map, the map that sends a `L : Submodule ℤ E` to the
`Submodule ℤ F` that is the pullback of `L` by `e`. If `IsZLattice L` and `e` is a continuous
linear equiv, then it is a `IsZLattice` of `E`, see `instIsZLatticeComap`. -/
/-
**ZLattice.comap** 是 Mathlib 中的一个定义，位于命名空间 `ZLattice`。
形式化陈述：(K : Type u_1) →   [inst : NormedField K] →     {E : Type u_2} →       {F 
: Type u_3} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : Norm
edSpace K E] →             [inst_3 : NormedAddCommGroup F] → [inst_4 : NormedSpa
ce K F] → Submodule ℤ E → (F →ₗ[K] E) → Submodule ℤ F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `e : E → F` a linear map, the map that sends a `L : Submodule ℤ E` to the
`Submodule ℤ F` that is the pullback of `L` by `e`. If `IsZLattice L` and `e` is
 a continuous
linear equiv, then it is a `IsZLattice` of `E`, see `instIsZLatticeComap`.
-/
protected def ZLattice.comap (e : F →ₗ[K] E) := L.comap (e.restrictScalars ℤ)

@[simp]
/-
**ZLattice.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.coe_comap (e : F ->ₗ[K] E) : (ZLattice.comap K L e : Set F) = e ⁻
¹' L
参数：e : F ->ₗ[K] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ZLattice.coe_comap (e : F →ₗ[K] E) :
    (ZLattice.comap K L e : Set F) = e ⁻¹' L := rfl
/-
**ZLattice.comap_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_refl : ZLattice.comap K L (1 : E ->ₗ[K] E) = L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_id`：comap_id : comap (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem ZLattice.comap_refl :
    ZLattice.comap K L (1 : E →ₗ[K] E) = L := Submodule.comap_id L
/-
**ZLattice.comap_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_discreteTopology [hL : DiscreteTopology L] {e : F ->ₗ[K] E}
 (he₁ : Continuous e) (he₂ : Function.Injective e) : DiscreteTopology (ZLattice.
comap K L e)
参数：he₁ : Continuous e；he₂ : Function.Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.preimage_of_continuous_injective`：DiscreteTopology.prei
mage_of_continuous_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpac
e Y] (s : Set Y) [DiscreteTopology s] {…
-/
theorem ZLattice.comap_discreteTopology [hL : DiscreteTopology L] {e : F →ₗ[K] E}
    (he₁ : Continuous e) (he₂ : Function.Injective e) :
    DiscreteTopology (ZLattice.comap K L e) := by
  exact DiscreteTopology.preimage_of_continuous_injective L he₁ he₂
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DiscreteTopology L] (e : F ≃L[K] E) :
    DiscreteTopology (ZLattice.comap K L e.toLinearMap) :=
  ZLattice.comap_discreteTopology K L e.continuous e.injective
/-
**ZLattice.comap_span_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_span_top (hL : span K (L : Set E) = ⊤) {e : F ->ₗ[K] E} (he
 : (L : Set E) subseteq LinearMap.range e) : span K (ZLattice.comap K L e : Set 
F) = ⊤
参数：hL : span K (L : Set E) = ⊤；he : (L : Set E) subseteq LinearMap.range e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.coe_comap`：ZLattice.coe_comap (e : F ->ₗ[K] E) : (ZLattice.coma
p K L e : Set F) = e ⁻¹' L
· 使用定理 `Submodule.span_preimage_eq`：span_preimage_eq [RingHomSurjective τ₁₂] {f 
: M ->ₛₗ[τ₁₂] M₂} {s : Set M₂} (h₀ : s.Nonempty) (h₁ : s subseteq range f) : spa
n R (f ⁻¹' s) = …
· 使用定理 `Submodule.nonempty`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), (↑p
).Nonemp…
· 使用定理 `Submodule.comap_top`：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
-/
theorem ZLattice.comap_span_top (hL : span K (L : Set E) = ⊤) {e : F →ₗ[K] E}
    (he : (L : Set E) ⊆ LinearMap.range e) :
    span K (ZLattice.comap K L e : Set F) = ⊤ := by
  rw [ZLattice.coe_comap, Submodule.span_preimage_eq (Submodule.nonempty L) he, hL, comap_top]
/-
**instIsZLatticeComap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instIsZLatticeComap [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E) 
: IsZLattice K (ZLattice.comap K L e.toLinearMap) where span_top
参数：e : F ≃L[K] E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteTopologySubtypeMemSubmoduleIntComap`：∀ (K : Type u_1) [inst 
: NormedField K] {E : Type u_2} {F : Type u_3} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace K E] [inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZLattice.coe_comap`：ZLattice.coe_comap (e : F ->ₗ[K] E) : (ZLattice.coma
p K L e : Set F) = e ⁻¹' L
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `ContinuousLinearEquiv.coe_toLinearEquiv`：coe_toLinearEquiv (f : M₁ ≃SL[σ
₁₂] M₂) : ⇑f.toLinearEquiv = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.image_symm_eq_preimage`：∀ {R₁ : Type u_1} {R₂ : Ty
pe u_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ 
→+* R₁}   [inst_2 : RingHomInvPair…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `IsZLattice.span_top`：∀ {K : Type u_1} {inst : NormedField K} {E : Type u
_2} {inst_1 : NormedAddCommGroup E} {inst_2 : NormedSpace K E}   {L : Submodule 
ℤ E} {ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
instance instIsZLatticeComap [DiscreteTopology L] [IsZLattice K L] (e : F ≃L[K] E) :
    IsZLattice K (ZLattice.comap K L e.toLinearMap) where
  span_top := by
    rw [ZLattice.coe_comap, LinearEquiv.coe_coe, e.coe_toLinearEquiv, ← e.image_symm_eq_preimage,
      ← ContinuousLinearEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_coe, ← Submodule.map_span,
      IsZLattice.span_top, Submodule.map_top, e.symm.range]

@[simp]
/-
**ZLattice.comap_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_toAddSubgroup (e : F ->ₗ[K] E) : (ZLattice.comap K L e).toA
ddSubgroup = L.toAddSubgroup.comap e.toAddMonoidHom
参数：e : F ->ₗ[K] E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ZLattice.comap_toAddSubgroup (e : F →ₗ[K] E) :
    (ZLattice.comap K L e).toAddSubgroup = L.toAddSubgroup.comap e.toAddMonoidHom := rfl
/-
**ZLattice.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace K G] (
e : F ->ₗ[K] E) (e' : G ->ₗ[K] F) : (ZLattice.comap K (ZLattice.comap K L e) e')
 = ZLattice.comap K L (e ∘ₗ e')
参数：e : F ->ₗ[K] E；e' : G ->ₗ[K] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.comap_comp`：comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] 
M₃) (p : Submodule R₃ M₃) : comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap
 g p)
-/
theorem ZLattice.comap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
    (e : F →ₗ[K] E) (e' : G →ₗ[K] F) :
    (ZLattice.comap K (ZLattice.comap K L e) e') = ZLattice.comap K L (e ∘ₗ e') :=
  (Submodule.comap_comp _ _ L).symm

/-- If `e` is a linear equivalence, it induces a `ℤ`-linear equivalence between
`L` and `ZLattice.comap K L e`. -/
/-
**ZLattice.comap_equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ZLattice.comap_equiv (e : F ≃ₗ[K] E) : L ≃ₗ[Int] (ZLattice.comap K L e.toL
inearMap)
参数：e : F ≃ₗ[K] E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e` is a linear equivalence, it induces a `ℤ`-linear equivalence between
`L` and `ZLattice.comap K L e`.
-/
def ZLattice.comap_equiv (e : F ≃ₗ[K] E) :
    L ≃ₗ[ℤ] (ZLattice.comap K L e.toLinearMap) :=
  LinearEquiv.ofBijective
    ((e.symm.toLinearMap.restrictScalars ℤ).restrict
      (fun _ h ↦ by simpa [← SetLike.mem_coe] using h))
    ⟨fun _ _ h ↦ Subtype.ext_iff.mpr (e.symm.injective (congr_arg Subtype.val h)),
    fun ⟨x, hx⟩ ↦ ⟨⟨e x, by rwa [← SetLike.mem_coe, ZLattice.coe_comap] at hx⟩,
      by simp [Subtype.ext_iff]⟩⟩

@[simp]
/-
**ZLattice.comap_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZLattice.comap_equiv_apply (e : F ≃ₗ[K] E) (x : L) : ZLattice.comap_equiv 
K L e x = e.symm x
参数：e : F ≃ₗ[K] E；x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ZLattice.comap_equiv_apply (e : F ≃ₗ[K] E) (x : L) :
    ZLattice.comap_equiv K L e x = e.symm x := rfl

namespace Module.Basis

/-- The basis of `ZLattice.comap K L e` given by the image of a basis `b` of `L` by `e.symm`. -/
/-
**Module.Basis.ofZLatticeComap** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofZLatticeComap (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) : Basis ι 
Int (ZLattice.comap K L e.toLinearMap)
参数：e : F ≃ₗ[K] E；b : Basis ι Int L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis of `ZLattice.comap K L e` given by the image of a basis `b` of `L` by 
`e.symm`.
-/
def ofZLatticeComap (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) :
    Basis ι ℤ (ZLattice.comap K L e.toLinearMap) := b.map (ZLattice.comap_equiv K L e)

@[simp]
/-
**Module.Basis.ofZLatticeComap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ofZLatticeComap_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L) (i :
 ι) : b.ofZLatticeComap K L e i = e.symm (b i)
参数：e : F ≃ₗ[K] E；b : Basis ι Int L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZLatticeComap_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) (i : ι) :
    b.ofZLatticeComap K L e i = e.symm (b i) := by simp [Basis.ofZLatticeComap]

@[simp]
/-
**Module.Basis.ofZLatticeComap_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：ofZLatticeComap_repr_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι Int L)
 (x : L) (i : ι) : (b.ofZLatticeComap K L e).repr (ZLattice.comap_equiv K L e x)
 i = b.repr x i
参数：e : F ≃ₗ[K] E；b : Basis ι Int L；x : L；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofZLatticeComap_repr_apply (e : F ≃ₗ[K] E) {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    (b.ofZLatticeComap K L e).repr (ZLattice.comap_equiv K L e x) i = b.repr x i := by
  simp [Basis.ofZLatticeComap]

end Module.Basis
end comap

section NormedLinearOrderedField_comap

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [FiniteDimensional K F]
  [ProperSpace F]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

/-
**Module.Basis.ofZLatticeBasis_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.ofZLatticeBasis_comap (e : F ≃L[K] E) {ι : Type*} (b : Basis 
ι Int L) : (b.ofZLatticeComap K L e.toLinearEquiv).ofZLatticeBasis K (ZLattice.c
omap K L e.toLinearMap) = (b.ofZLatticeBasis K L).map e.symm.toLinearEquiv
参数：e : F ≃L[K] E；b : Basis ι Int L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `instDiscreteTopologySubtypeMemSubmoduleIntComap`：∀ (K : Type u_1) [inst 
: NormedField K] {E : Type u_2} {F : Type u_3} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : NormedSpace K E] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.ofZLatticeBasis_apply`：ofZLatticeBasis_apply (i : ι) : b.of
ZLatticeBasis K L i = b i
· 使用定理 `Module.Basis.ofZLatticeComap_apply`：ofZLatticeComap_apply (e : F ≃ₗ[K] E
) {ι : Type*} (b : Basis ι Int L) (i : ι) : b.ofZLatticeComap K L e i = e.symm (
b i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Module.Basis.ofZLatticeBasis_comap (e : F ≃L[K] E) {ι : Type*} (b : Basis ι ℤ L) :
    (b.ofZLatticeComap K L e.toLinearEquiv).ofZLatticeBasis K (ZLattice.comap K L e.toLinearMap) =
    (b.ofZLatticeBasis K L).map e.symm.toLinearEquiv := by
  ext
  simp

end NormedLinearOrderedField_comap

/-- If `f` is periodic wrt a ℤ-lattice, then the range of `f` is compact. -/
/-
**IsZLattice.isCompact_range_of_periodic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsZLattice.isCompact_range_of_periodic {E F : Type*} [NormedAddCommGroup E
] [NormedSpace Real E] [FiniteDimensional Real E] [TopologicalSpace F] (L : Subm
odule Int E) [DiscreteTopology L] [IsZLattice Real L] (f : E -> F) (hf : Continu
ous f) (hf' : forall z w, w in L -> f (z + w) = f z) : IsCompact (Set.range f)
参数：L : Submodule Int E；f : E -> F；hf : Continuous f；hf' : forall z w, w in L -> 
f (z + w) = f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZLattice.module_free`：ZLattice.module_free [IsZLattice K L] : Module.Fre
e Int L
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `parallelepiped_basis_eq`：parallelepiped_basis_eq (b : Basis ι Real E) : 
parallelepiped b = {x | forall i, b.repr x i in Set.Icc 0 1}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Module.Basis.ofZLatticeBasis_repr_apply`：ofZLatticeBasis_repr_apply (x :
 L) (i : ι) : (b.ofZLatticeBasis K L).repr x i = b.repr x i
· 使用定理 `Module.Basis.repr_linearCombination`：repr_linearCombination (v) : b.repr
 (Finsupp.linearCombination _ b v) = v
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is periodic wrt a ℤ-lattice, then the range of `f` is compact.
-/
lemma IsZLattice.isCompact_range_of_periodic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace F]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (f : E → F) (hf : Continuous f)
    (hf' : ∀ z w, w ∈ L → f (z + w) = f z) : IsCompact (Set.range f) := by
  have := ZLattice.module_free ℝ L
  let b := Module.Free.chooseBasis ℤ L
  convert! (b.ofZLatticeBasis ℝ).parallelepiped.isCompact.image hf
  refine le_antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨x, rfl⟩
  let x' : L := b.repr.symm (Finsupp.equivFunOnFinite.symm
    fun i ↦ ⌊(b.ofZLatticeBasis ℝ).repr x i⌋)
  refine ⟨x + (- x'), ?_, hf' _ _ (- x').2⟩
  simp [parallelepiped_basis_eq, x', Int.floor_le, Int.lt_floor_add_one, le_of_lt, add_comm (1 : ℝ)]

end ZLattice

