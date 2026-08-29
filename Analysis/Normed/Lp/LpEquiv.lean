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

In this file we collect a variety of equivalences among various $L^p$ spaces. In particular,
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


variable {α : Type*} {E : α -> Type*} [forall i, NormedAddCommGroup (E i)] {p : Real>=0∞}

section Finite

variable [Finite α]

/--
Definition of `Equiv.lpPiLp` / `Equiv.lpPiLp` 的定义

English:
definition Equiv.lpPiLp
  signature: : lp E p ≃ PiLp p E where
  body: toLp p ⇑f
  invFun f := ⟨ofLp f, Memℓp.all f⟩

中文:
定义 等价.lpPiLp
  签名: : lp E p ≃ PiLp p E where
  定义体: toLp p ⇑f
  invFun f := ⟨ofLp f, Memℓp.all f⟩
-/
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := toLp p ⇑f
  invFun f := ⟨ofLp f, Memℓp.all f⟩

/--
theorem `coe_equiv_lpPiLp` / 定理 `coe_equiv_lpPiLp`

English:
theorem coe_equiv_lpPiLp
  given: (f : lp E p)
  statement: Equiv.lpPiLp f = ⇑f
  proof: rfl

中文:
定理 coe_equiv_lpPiLp
  条件: (f : lp E p)
  结论: 等价.lpPiLp f = ⇑f
  证明: rfl
-/
theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f :=
  rfl

/--
theorem `coe_equiv_lpPiLp_symm` / 定理 `coe_equiv_lpPiLp_symm`

English:
theorem coe_equiv_lpPiLp_symm
  given: (f : PiLp p E)
  statement: (Equiv.lpPiLp.symm f : forall i, E i) = f
  proof: rfl

中文:
定理 coe_equiv_lpPiLp_symm
  条件: (f : PiLp p E)
  结论: (等价.lpPiLp.symm f : 对任意 i, E i) = f
  证明: rfl
-/
theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : forall i, E i) = f :=
  rfl

/--
Definition of `AddEquiv.lpPiLp` / `AddEquiv.lpPiLp` 的定义

English:
definition AddEquiv.lpPiLp
  signature: : lp E p ≃+ PiLp p E
  body: { Equiv.lpPiLp with map_add' := fun _f _g => rfl }

中文:
定义 加法等价.lpPiLp
  签名: : lp E p ≃+ PiLp p E
  定义体: { Equiv.lpPiLp with map_add' := fun _f _g => rfl }

Depends on / 依赖: Equiv.lpPiLp, lpPiLp, map_add
-/
def AddEquiv.lpPiLp : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun _f _g => rfl }

/--
theorem `coe_addEquiv_lpPiLp` / 定理 `coe_addEquiv_lpPiLp`

English:
theorem coe_addEquiv_lpPiLp
  given: (f : lp E p)
  statement: AddEquiv.lpPiLp f = ⇑f
  proof: rfl

中文:
定理 coe_addEquiv_lpPiLp
  条件: (f : lp E p)
  结论: 加法等价.lpPiLp f = ⇑f
  证明: rfl
-/
theorem coe_addEquiv_lpPiLp (f : lp E p) : AddEquiv.lpPiLp f = ⇑f :=
  rfl

/--
theorem `coe_addEquiv_lpPiLp_symm` / 定理 `coe_addEquiv_lpPiLp_symm`

English:
theorem coe_addEquiv_lpPiLp_symm
  given: (f : PiLp p E)
  proof: rfl

中文:
定理 coe_addEquiv_lpPiLp_symm
  条件: (f : PiLp p E)
  证明: rfl
-/
theorem coe_addEquiv_lpPiLp_symm (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : forall i, E i) = f :=
  rfl

end Finite

/--
theorem `equiv_lpPiLp_norm` / 定理 `equiv_lpPiLp_norm`

English:
theorem equiv_lpPiLp_norm
  given: [Fintype α] (f : lp E p)
  statement: ‖Equiv.lpPiLp f‖ = ‖f‖
  proof: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl

中文:
定理 equiv_lpPiLp_norm
  条件: [有限类型 α] (f : lp E p)
  结论: ‖等价.lpPiLp f‖ = ‖f‖
  证明: by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl

Depends on / 依赖: Equiv.lpPiLp, PiLp.norm_eq_card, PiLp.norm_eq_ciSup, PiLp.norm_eq_sum, lp.norm_eq_card_dsupport, lp.norm_eq_ciSup, lp.norm_eq_tsum_rpow, lpPiLp, norm_eq_card, norm_eq_card_dsupport, norm_eq_ciSup, norm_eq_sum, norm_eq_tsum_rpow, p.trichotomy, trichotomy, tsum_fintype
-/
theorem equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl

section Equivₗᵢ

variable [Fintype α] (𝕜 : Type*) [NontriviallyNormedField 𝕜] [forall i, NormedSpace 𝕜 (E i)]
variable (E)

/--
Definition of `lpPiLpₗᵢ` / `lpPiLpₗᵢ` 的定义

English:
definition lpPiLpₗᵢ
  signature: [Fact (1 <= p)]
  body: { AddEquiv.lpPiLp with
    map_smul' := fun _k _f => rfl
    norm_map' := equiv_lpPiLp_norm }

中文:
定义 lpPiLpₗᵢ
  签名: [Fact (1 <= p)]
  定义体: { AddEquiv.lpPiLp with
    map_smul' := fun _k _f => rfl
    norm_map' := equiv_lpPiLp_norm }

Depends on / 依赖: AddEquiv, AddEquiv.lpPiLp, equiv_lpPiLp_norm, lpPiLp, map_smul, norm_map
-/
noncomputable def lpPiLpₗᵢ [Fact (1 <= p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun _k _f => rfl
    norm_map' := equiv_lpPiLp_norm }

variable {𝕜 E}

/--
theorem `coe_lpPiLpₗᵢ` / 定理 `coe_lpPiLpₗᵢ`

English:
theorem coe_lpPiLpₗᵢ
  given: [Fact (1 <= p)] (f : lp E p)
  statement: (lpPiLpₗᵢ E 𝕜 f : forall i, E i) = f
  proof: rfl

中文:
定理 coe_lpPiLpₗᵢ
  条件: [Fact (1 <= p)] (f : lp E p)
  结论: (lpPiLpₗᵢ E 𝕜 f : 对任意 i, E i) = f
  证明: rfl
-/
theorem coe_lpPiLpₗᵢ [Fact (1 <= p)] (f : lp E p) : (lpPiLpₗᵢ E 𝕜 f : forall i, E i) = f :=
  rfl

/--
theorem `coe_lpPiLpₗᵢ_symm` / 定理 `coe_lpPiLpₗᵢ_symm`

English:
theorem coe_lpPiLpₗᵢ_symm
  given: [Fact (1 <= p)] (f : PiLp p E)
  proof: rfl

中文:
定理 coe_lpPiLpₗᵢ_symm
  条件: [Fact (1 <= p)] (f : PiLp p E)
  证明: rfl
-/
theorem coe_lpPiLpₗᵢ_symm [Fact (1 <= p)] (f : PiLp p E) :
    ((lpPiLpₗᵢ E 𝕜).symm f : forall i, E i) = f :=
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

/--
Definition of `AddEquiv.lpBCF` / `AddEquiv.lpBCF` 的定义

English:
definition AddEquiv.lpBCF
  signature: : lp (fun _ : α => E) ∞ ≃+ (α ->ᵇ E) where
  body: ofNormedAddCommGroupDiscrete f ‖f‖ le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _f _g := rfl

中文:
定义 加法等价.lpBCF
  签名: : lp (fun _ : α => E) ∞ ≃+ (α ->ᵇ E) where
  定义体: ofNormedAddCommGroupDiscrete f ‖f‖ le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _f _g := rfl

Depends on / 依赖: f.prop, le_ciSup, ofNormedAddCommGroupDiscrete, p_infty_iff.mp
-/
noncomputable def AddEquiv.lpBCF : lp (fun _ : α => E) ∞ ≃+ (α ->ᵇ E) where
toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _f _g := rfl


/--
theorem `coe_addEquiv_lpBCF` / 定理 `coe_addEquiv_lpBCF`

English:
theorem coe_addEquiv_lpBCF
  given: (f : lp (fun _ : α => E) ∞)
  statement: (AddEquiv.lpBCF f : α -> E) = f
  proof: rfl

中文:
定理 coe_addEquiv_lpBCF
  条件: (f : lp (fun _ : α => E) ∞)
  结论: (加法等价.lpBCF f : α -> E) = f
  证明: rfl
-/
theorem coe_addEquiv_lpBCF (f : lp (fun _ : α => E) ∞) : (AddEquiv.lpBCF f : α -> E) = f :=
  rfl

/--
theorem `coe_addEquiv_lpBCF_symm` / 定理 `coe_addEquiv_lpBCF_symm`

English:
theorem coe_addEquiv_lpBCF_symm
  given: (f : α ->ᵇ E)
  statement: (AddEquiv.lpBCF.symm f : α -> E) = f
  proof: rfl

中文:
定理 coe_addEquiv_lpBCF_symm
  条件: (f : α ->ᵇ E)
  结论: (加法等价.lpBCF.symm f : α -> E) = f
  证明: rfl
-/
theorem coe_addEquiv_lpBCF_symm (f : α ->ᵇ E) : (AddEquiv.lpBCF.symm f : α -> E) = f :=
  rfl

variable (E)

/--
Definition of `lpBCFₗᵢ` / `lpBCFₗᵢ` 的定义

English:
definition lpBCFₗᵢ
  signature: : lp (fun _ : α => E) ∞ ≃ₗᵢ[𝕜] α ->ᵇ E
  body: { AddEquiv.lpBCF with
    map_smul' := fun _ _ => rfl
    norm_map' := fun f => by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }

中文:
定义 lpBCFₗᵢ
  签名: : lp (fun _ : α => E) ∞ ≃ₗᵢ[𝕜] α ->ᵇ E
  定义体: { AddEquiv.lpBCF with
    map_smul' := fun _ _ => rfl
    norm_map' := fun f => by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }

Depends on / 依赖: AddEquiv, AddEquiv.lpBCF, lp.norm_eq_ciSup, map_smul, norm_eq_ciSup, norm_eq_iSup_norm, norm_map
-/
noncomputable def lpBCFₗᵢ : lp (fun _ : α => E) ∞ ≃ₗᵢ[𝕜] α ->ᵇ E :=
  { AddEquiv.lpBCF with
    map_smul' := fun _ _ => rfl
    norm_map' := fun f => by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }


variable {𝕜 E}

/--
theorem `coe_lpBCFₗᵢ` / 定理 `coe_lpBCFₗᵢ`

English:
theorem coe_lpBCFₗᵢ
  given: (f : lp (fun _ : α => E) ∞)
  statement: (lpBCFₗᵢ E 𝕜 f : α -> E) = f
  proof: rfl

中文:
定理 coe_lpBCFₗᵢ
  条件: (f : lp (fun _ : α => E) ∞)
  结论: (lpBCFₗᵢ E 𝕜 f : α -> E) = f
  证明: rfl
-/
theorem coe_lpBCFₗᵢ (f : lp (fun _ : α => E) ∞) : (lpBCFₗᵢ E 𝕜 f : α -> E) = f :=
  rfl

/--
theorem `coe_lpBCFₗᵢ_symm` / 定理 `coe_lpBCFₗᵢ_symm`

English:
theorem coe_lpBCFₗᵢ_symm
  given: (f : α ->ᵇ E)
  statement: ((lpBCFₗᵢ E 𝕜).symm f : α -> E) = f
  proof: rfl

中文:
定理 coe_lpBCFₗᵢ_symm
  条件: (f : α ->ᵇ E)
  结论: ((lpBCFₗᵢ E 𝕜).symm f : α -> E) = f
  证明: rfl
-/
theorem coe_lpBCFₗᵢ_symm (f : α ->ᵇ E) : ((lpBCFₗᵢ E 𝕜).symm f : α -> E) = f :=
  rfl

end NormedAddCommGroup

section RingAlgebra

/--
Definition of `RingEquiv.lpBCF` / `RingEquiv.lpBCF` 的定义

English:
definition RingEquiv.lpBCF
  signature: : lp (fun _ : α => R) ∞ ≃+* (α ->ᵇ R)
  body: { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }

中文:
定义 环等价.lpBCF
  签名: : lp (fun _ : α => R) ∞ ≃+* (α ->ᵇ R)
  定义体: { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }

Depends on / 依赖: AddEquiv, AddEquiv.lpBCF, map_mul
-/
noncomputable def RingEquiv.lpBCF : lp (fun _ : α => R) ∞ ≃+* (α ->ᵇ R) :=
  { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }

/--
theorem `coe_ringEquiv_lpBCF` / 定理 `coe_ringEquiv_lpBCF`

English:
theorem coe_ringEquiv_lpBCF
  given: (f : lp (fun _ : α => R) ∞)
  statement: (RingEquiv.lpBCF f : α -> R) = f
  proof: rfl

中文:
定理 coe_ringEquiv_lpBCF
  条件: (f : lp (fun _ : α => R) ∞)
  结论: (环等价.lpBCF f : α -> R) = f
  证明: rfl
-/
theorem coe_ringEquiv_lpBCF (f : lp (fun _ : α => R) ∞) : (RingEquiv.lpBCF f : α -> R) = f :=
  rfl

/--
theorem `coe_ringEquiv_lpBCF_symm` / 定理 `coe_ringEquiv_lpBCF_symm`

English:
theorem coe_ringEquiv_lpBCF_symm
  given: (f : α ->ᵇ R)
  statement: (RingEquiv.lpBCF.symm f : α -> R) = f
  proof: rfl

中文:
定理 coe_ringEquiv_lpBCF_symm
  条件: (f : α ->ᵇ R)
  结论: (环等价.lpBCF.symm f : α -> R) = f
  证明: rfl
-/
theorem coe_ringEquiv_lpBCF_symm (f : α ->ᵇ R) : (RingEquiv.lpBCF.symm f : α -> R) = f :=
  rfl

variable (α)

-- even `α` needs to be explicit here for elaboration
-- the `NormOneClass A` shouldn't really be necessary, but currently it is for
-- `one_memℓp_infty` to get the `Ring` instance on `lp`.
/--
Definition of `AlgEquiv.lpBCF` / `AlgEquiv.lpBCF` 的定义

English:
definition AlgEquiv.lpBCF
  signature: : lp (fun _ : α => A) ∞ ≃ₐ[𝕜] α ->ᵇ A
  body: { RingEquiv.lpBCF with commutes' := fun _k => rfl }

中文:
定义 代数等价.lpBCF
  签名: : lp (fun _ : α => A) ∞ ≃ₐ[𝕜] α ->ᵇ A
  定义体: { RingEquiv.lpBCF with commutes' := fun _k => rfl }

Depends on / 依赖: RingEquiv, RingEquiv.lpBCF, commutes
-/
noncomputable def AlgEquiv.lpBCF : lp (fun _ : α => A) ∞ ≃ₐ[𝕜] α ->ᵇ A :=
  { RingEquiv.lpBCF with commutes' := fun _k => rfl }


variable {α 𝕜}

/--
theorem `coe_algEquiv_lpBCF` / 定理 `coe_algEquiv_lpBCF`

English:
theorem coe_algEquiv_lpBCF
  given: (f : lp (fun _ : α => A) ∞)
  statement: (AlgEquiv.lpBCF α 𝕜 f : α -> A) = f
  proof: rfl

中文:
定理 coe_algEquiv_lpBCF
  条件: (f : lp (fun _ : α => A) ∞)
  结论: (代数等价.lpBCF α 𝕜 f : α -> A) = f
  证明: rfl
-/
theorem coe_algEquiv_lpBCF (f : lp (fun _ : α => A) ∞) : (AlgEquiv.lpBCF α 𝕜 f : α -> A) = f :=
  rfl

/--
theorem `coe_algEquiv_lpBCF_symm` / 定理 `coe_algEquiv_lpBCF_symm`

English:
theorem coe_algEquiv_lpBCF_symm
  given: (f : α ->ᵇ A)
  statement: ((AlgEquiv.lpBCF α 𝕜).symm f : α -> A) = f
  proof: rfl

中文:
定理 coe_algEquiv_lpBCF_symm
  条件: (f : α ->ᵇ A)
  结论: ((代数等价.lpBCF α 𝕜).symm f : α -> A) = f
  证明: rfl
-/
theorem coe_algEquiv_lpBCF_symm (f : α ->ᵇ A) : ((AlgEquiv.lpBCF α 𝕜).symm f : α -> A) = f :=
  rfl

end RingAlgebra

end LpBCF
