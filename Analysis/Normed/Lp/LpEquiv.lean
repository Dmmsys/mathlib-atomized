/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Equivalences among $L^p$ spaces

In this file we collect a variety of equivalences among various $L^p$ spaces.  In particular,
when `α` is a `Fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, if all `E i` for `i : α` are
normed, additive commutative groups, there is a natural linear isometric
equivalence `lpPiLpₗᵢ : lp E p ≃ₗᵢ PiLp p E`. In addition, when `α` is a discrete topological
space, the bounded continuous functions `α →ᵇ β` correspond exactly to `lp (fun _ ↦ β) ∞`.
Here there can be more structure, including ring and algebra structures,
and we implement these equivalences accordingly as well.

We keep this as a separate file so that the various $L^p$ space files don't import the others.

Recall that `PiLp` is just a type synonym for `Π i, E i` but given a different metric and norm
structure, although the topological, uniform and bornological structures coincide definitionally.
These structures are only defined on `PiLp` for `Fintype α`, so there are no issues of convergence
to consider.

While `PreLp` is also a type synonym for `Π i, E i`, it allows for infinite index types. On this
type there is a predicate `Memℓp` which says that the relevant `p`-norm is finite and `lp E p` is
the subtype of `PreLp` satisfying `Memℓp`.

## TODO

* Equivalence between `lp` and `MeasureTheory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`

-/

@[expose] public section

open WithLp

open scoped ENNReal

section LpPiLp


variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

section Finite

variable [Finite α]

/-- The canonical `Equiv` between `lp E p ≃ PiLp p E` when `E : α → Type u` with `[Finite α]`. -/
/-
**Equiv.lpPiLp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.lpPiLp : lp E p ≃ PiLp p E where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `Equiv` between `lp E p ≃ PiLp p E` when `E : α → Type u` with `[F
inite α]`.
-/
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := toLp p ⇑f
  invFun f := ⟨ofLp f, Memℓp.all f⟩
/-
**coe_equiv_lpPiLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f :=
  rfl
/-
**coe_equiv_lpPiLp_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : forall i, E 
i) = f
参数：f : PiLp p E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl

/-- The canonical `AddEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u` with
`[Finite α]`. -/
/-
**AddEquiv.lpPiLp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.lpPiLp : lp E p ≃+ PiLp p E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `AddEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u` w
ith
`[Finite α]`.
-/
def AddEquiv.lpPiLp : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun _f _g ↦ rfl }
/-
**coe_addEquiv_lpPiLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_addEquiv_lpPiLp (f : lp E p) : AddEquiv.lpPiLp f = ⇑f
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_addEquiv_lpPiLp (f : lp E p) : AddEquiv.lpPiLp f = ⇑f :=
  rfl
/-
**coe_addEquiv_lpPiLp_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_addEquiv_lpPiLp_symm (f : PiLp p E) : (AddEquiv.lpPiLp.symm f : forall
 i, E i) = f
参数：f : PiLp p E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_addEquiv_lpPiLp_symm (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl

end Finite

/-
**equiv_lpPiLp_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖
参数：f : lp E p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Memℓp.finite_dsupport`：finite_dsupport {f : forall i, E i} (hf : Memℓp f
 0) : Set.Finite { i | f i != 0 }
· 使用定理 `lp.memℓp`：∀ {α : Type u_3} {E : α → Type u_4} {p : ENNReal} [inst : (i :
 α) → NormedAddCommGroup (E i)] (f : ↥(lp E p)),   Memℓp (↑f) p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PiLp.norm_eq_card`：norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ != 0}.
toFinite.toFinset.card
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `lp.norm_eq_card_dsupport`：norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp
.memℓp f).finite_dsupport.toFinset.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.norm_eq_ciSup`：norm_eq_ciSup (f : PiLp ∞ β) : ‖f‖ = ⨆ i, ‖f i‖
· 使用定理 `lp.norm_eq_ciSup`：norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖
· 使用定理 `PiLp.norm_eq_sum`：norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) : ‖f‖ =
 (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `lp.norm_eq_tsum_rpow`：norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p)
 : ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl

section Equivₗᵢ

variable [Fintype α] (𝕜 : Type*) [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
variable (E)

/-- The canonical `LinearIsometryEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u`
with `[Fintype α]` and `[Fact (1 ≤ p)]`. -/
/-
**lpPiLp** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `LinearIsometryEquiv` between `lp E p` and `PiLp p E` when `E : α 
→ Type u`
with `[Fintype α]` and `[Fact (1 ≤ p)]`.
-/
noncomputable def lpPiLpₗᵢ [Fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun _k _f ↦ rfl
    norm_map' := equiv_lpPiLp_norm }

variable {𝕜 E}
/-
**coe_lpPiLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lpPiLpₗᵢ [Fact (1 ≤ p)] (f : lp E p) : (lpPiLpₗᵢ E 𝕜 f : ∀ i, E i) = f :=
  rfl
/-
**coe_lpPiLp** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lpPiLpₗᵢ_symm [Fact (1 ≤ p)] (f : PiLp p E) :
    ((lpPiLpₗᵢ E 𝕜).symm f : ∀ i, E i) = f :=
  rfl

end Equivₗᵢ

end LpPiLp

section LpBCF

open scoped BoundedContinuousFunction

open BoundedContinuousFunction

variable {α E R A : Type*} (𝕜 : Type*) [TopologicalSpace α] [DiscreteTopology α]
variable [NormedRing A] [NormOneClass A] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NonUnitalNormedRing R]

section NormedAddCommGroup

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as an `AddEquiv`. -/
/-
**AddEquiv.lpBCF** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.lpBCF : lp (fun _ : α => E) ∞ ≃+ (α ->ᵇ E) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as an `AddEquiv`.
-/
noncomputable def AddEquiv.lpBCF : lp (fun _ : α ↦ E) ∞ ≃+ (α →ᵇ E) where
  toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ <| le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _f _g := rfl
/-
**coe_addEquiv_lpBCF** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_addEquiv_lpBCF (f : lp (fun _ : α => E) ∞) : (AddEquiv.lpBCF f : α -> 
E) = f
参数：f : lp (fun _ : α => E) ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_addEquiv_lpBCF (f : lp (fun _ : α ↦ E) ∞) : (AddEquiv.lpBCF f : α → E) = f :=
  rfl
/-
**coe_addEquiv_lpBCF_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_addEquiv_lpBCF_symm (f : α ->ᵇ E) : (AddEquiv.lpBCF.symm f : α -> E) =
 f
参数：f : α ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_addEquiv_lpBCF_symm (f : α →ᵇ E) : (AddEquiv.lpBCF.symm f : α → E) = f :=
  rfl

variable (E)

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as a `LinearIsometryEquiv`. -/
/-
**lpBCF** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as a `LinearIsomet
ryEquiv`.
-/
noncomputable def lpBCFₗᵢ : lp (fun _ : α ↦ E) ∞ ≃ₗᵢ[𝕜] α →ᵇ E :=
  { AddEquiv.lpBCF with
    map_smul' := fun _ _ ↦ rfl
    norm_map' := fun f ↦ by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }


variable {𝕜 E}
/-
**coe_lpBCF** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lpBCFₗᵢ (f : lp (fun _ : α ↦ E) ∞) : (lpBCFₗᵢ E 𝕜 f : α → E) = f :=
  rfl
/-
**coe_lpBCF** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lpBCFₗᵢ_symm (f : α →ᵇ E) : ((lpBCFₗᵢ E 𝕜).symm f : α → E) = f :=
  rfl

end NormedAddCommGroup

section RingAlgebra

/-- The canonical map between `lp (fun _ : α ↦ R) ∞` and `α →ᵇ R` as a `RingEquiv`. -/
/-
**RingEquiv.lpBCF** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.lpBCF : lp (fun _ : α => R) ∞ ≃+* (α ->ᵇ R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map between `lp (fun _ : α ↦ R) ∞` and `α →ᵇ R` as a `RingEquiv`.
-/
noncomputable def RingEquiv.lpBCF : lp (fun _ : α ↦ R) ∞ ≃+* (α →ᵇ R) :=
  { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }
/-
**coe_ringEquiv_lpBCF** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_ringEquiv_lpBCF (f : lp (fun _ : α => R) ∞) : (RingEquiv.lpBCF f : α -
> R) = f
参数：f : lp (fun _ : α => R) ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem coe_ringEquiv_lpBCF (f : lp (fun _ : α ↦ R) ∞) : (RingEquiv.lpBCF f : α → R) = f :=
  rfl
/-
**coe_ringEquiv_lpBCF_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_ringEquiv_lpBCF_symm (f : α ->ᵇ R) : (RingEquiv.lpBCF.symm f : α -> R)
 = f
参数：f : α ->ᵇ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem coe_ringEquiv_lpBCF_symm (f : α →ᵇ R) : (RingEquiv.lpBCF.symm f : α → R) = f :=
  rfl

variable (α)

-- even `α` needs to be explicit here for elaboration
-- the `NormOneClass A` shouldn't really be necessary, but currently it is for
-- `one_memℓp_infty` to get the `Ring` instance on `lp`.
/-- The canonical map between `lp (fun _ : α ↦ A) ∞` and `α →ᵇ A` as an `AlgEquiv`. -/
/-
**AlgEquiv.lpBCF** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.lpBCF : lp (fun _ : α => A) ∞ ≃ₐ[𝕜] α ->ᵇ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map between `lp (fun _ : α ↦ A) ∞` and `α →ᵇ A` as an `AlgEquiv`.
-/
noncomputable def AlgEquiv.lpBCF : lp (fun _ : α ↦ A) ∞ ≃ₐ[𝕜] α →ᵇ A :=
  { RingEquiv.lpBCF with commutes' := fun _k ↦ rfl }


variable {α 𝕜}
/-
**coe_algEquiv_lpBCF** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_algEquiv_lpBCF (f : lp (fun _ : α => A) ∞) : (AlgEquiv.lpBCF α 𝕜 f : α
 -> A) = f
参数：f : lp (fun _ : α => A) ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem coe_algEquiv_lpBCF (f : lp (fun _ : α ↦ A) ∞) : (AlgEquiv.lpBCF α 𝕜 f : α → A) = f :=
  rfl
/-
**coe_algEquiv_lpBCF_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_algEquiv_lpBCF_symm (f : α ->ᵇ A) : ((AlgEquiv.lpBCF α 𝕜).symm f : α -
> A) = f
参数：f : α ->ᵇ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem coe_algEquiv_lpBCF_symm (f : α →ᵇ A) : ((AlgEquiv.lpBCF α 𝕜).symm f : α → A) = f :=
  rfl

end RingAlgebra

end LpBCF

