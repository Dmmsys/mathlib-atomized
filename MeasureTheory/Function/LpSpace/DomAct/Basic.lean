/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun.DomAct
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Action of `Mᵈᵐᵃ` on `Lᵖ` spaces

In this file we define action of `Mᵈᵐᵃ` on `MeasureTheory.Lp E p μ`
If `f : α → E` is a function representing an equivalence class in `Lᵖ(α, E)`, `M` acts on `α`,
and `c : M`, then `(.mk c : Mᵈᵐᵃ) • [f]` is represented by the function `a ↦ f (c • a)`.

We also prove basic properties of this action.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace DomMulAct

variable {M N α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : MeasureTheory.Measure α} {p : Real>=0∞}

section SMul

variable [SMul M α] [SMulInvariantMeasure M α μ] [MeasurableConstSMul M α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Mᵈᵐᵃ (Lp E p μ)
  body: Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f

@[to_additive (attr := simp)]

中文:
实例 :
  签名: SMul Mᵈᵐᵃ (Lp E p μ)
  定义体: Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f

@[to_additive (attr := simp)]

Depends on / 依赖: Lp.compMeasurePreserving, compMeasurePreserving, measurePreserving_smul, mk.symm
-/
instance : SMul Mᵈᵐᵃ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f

@[to_additive (attr := simp)]
/--
theorem `smul_Lp_val` / 定理 `smul_Lp_val`

English:
theorem smul_Lp_val
  given: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  statement: (c • f).1 = c • f.1
  proof: rfl

@[to_additive]

中文:
定理 smul_Lp_val
  条件: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  结论: (c • f).1 = c • f.1
  证明: rfl

@[to_additive]
-/
theorem smul_Lp_val (c : Mᵈᵐᵃ) (f : Lp E p μ) : (c • f).1 = c • f.1 := rfl

@[to_additive]
/--
theorem `smul_Lp_ae_eq` / 定理 `smul_Lp_ae_eq`

English:
theorem smul_Lp_ae_eq
  given: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  statement: c • f =ᵐ[μ] (f <| mk.symm c • ·)
  proof: Lp.coeFn_compMeasurePreserving _ _

@[to_additive]

中文:
定理 smul_Lp_ae_eq
  条件: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  结论: c • f =ᵐ[μ] (f <| mk.symm c • ·)
  证明: Lp.coeFn_compMeasurePreserving _ _

@[to_additive]

Depends on / 依赖: Lp.coeFn_compMeasurePreserving, coeFn_compMeasurePreserving
-/
theorem smul_Lp_ae_eq (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  Lp.coeFn_compMeasurePreserving _ _

@[to_additive]
/--
theorem `mk_smul_toLp` / 定理 `mk_smul_toLp`

English:
theorem mk_smul_toLp
  given: (c : M) {f : α -> E} (hf : MemLp f p μ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_smul_toLp
  条件: (c : M) {f : α -> E} (hf : MemLp f p μ)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_smul_toLp (c : M) {f : α -> E} (hf : MemLp f p μ) :
    mk c • hf.toLp f =
      (hf.comp_measurePreserving <| measurePreserving_smul c μ).toLp (f <| c • ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_Lp_const` / 定理 `smul_Lp_const`

English:
theorem smul_Lp_const
  given: [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E)
  proof: rfl

@[to_additive]

中文:
定理 smul_Lp_const
  条件: [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E)
  证明: rfl

@[to_additive]
-/
theorem smul_Lp_const [IsFiniteMeasure μ] (c : Mᵈᵐᵃ) (a : E) :
    c • Lp.const p μ a = Lp.const p μ a :=
  rfl

@[to_additive]
/--
theorem `mk_smul_indicatorConstLp` / 定理 `mk_smul_indicatorConstLp`

English:
theorem mk_smul_indicatorConstLp
  statement: (c : M)
  proof: rfl

中文:
定理 mk_smul_indicatorConstLp
  结论: (c : M)
  证明: rfl
-/
theorem mk_smul_indicatorConstLp (c : M)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (b : E) :
    mk c • indicatorConstLp p hs hμs b =
      indicatorConstLp p (hs.preimage <| measurable_const_smul c)
        (by rwa [SMulInvariantMeasure.measure_preimage_smul c hs]) b :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableConstSMul N α] :
  body: Subtype.val_injective.smulCommClass (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [SMul
  签名: N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableConstSMul N α] :
  定义体: Subtype.val_injective.smulCommClass (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.smulCommClass, smulCommClass, val_injective
-/
instance [SMul N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableConstSMul N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ => rfl) fun _ _ => rfl

instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass Mᵈᵐᵃ 𝕜 (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ => rfl) fun _ _ => rfl

instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass 𝕜 Mᵈᵐᵃ (Lp E p μ) :=
  .symm _ _ _

-- We don't have a typeclass for additive versions of the next few lemmas
-- Should we add `AddDistribAddAction` with `to_additive` both from `MulDistribMulAction`
-- and `DistribMulAction`?

@[to_additive]
/--
theorem `smul_Lp_add` / 定理 `smul_Lp_add`

English:
theorem smul_Lp_add
  given: (c : Mᵈᵐᵃ)
  statement: forall f g : Lp E p μ, c • (f + g) = c • f + c • g
  proof: by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

中文:
定理 smul_Lp_add
  条件: (c : Mᵈᵐᵃ)
  结论: 对任意 f g : Lp E p μ, c • (f + g) = c • f + c • g
  证明: by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

Depends on / 依赖: DomAddAct, DomAddAct.vadd_Lp_add, attribute, vadd_Lp_add
-/
theorem smul_Lp_add (c : Mᵈᵐᵃ) : forall f g : Lp E p μ, c • (f + g) = c • f + c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
attribute [simp] DomAddAct.vadd_Lp_add

@[to_additive (attr := simp 1001)]
/--
theorem `smul_Lp_zero` / 定理 `smul_Lp_zero`

English:
theorem smul_Lp_zero
  given: (c : Mᵈᵐᵃ)
  statement: c • (0 : Lp E p μ) = 0
  proof: rfl

@[to_additive]

中文:
定理 smul_Lp_zero
  条件: (c : Mᵈᵐᵃ)
  结论: c • (0 : Lp E p μ) = 0
  证明: rfl

@[to_additive]
-/
theorem smul_Lp_zero (c : Mᵈᵐᵃ) : c • (0 : Lp E p μ) = 0 := rfl

@[to_additive]
/--
theorem `smul_Lp_neg` / 定理 `smul_Lp_neg`

English:
theorem smul_Lp_neg
  given: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  statement: c • (-f) = -(c • f)
  proof: by
  rcases f with ⟨⟨_⟩, _⟩; rfl

@[to_additive]

中文:
定理 smul_Lp_neg
  条件: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  结论: c • (-f) = -(c • f)
  证明: by
  rcases f with ⟨⟨_⟩, _⟩; rfl

@[to_additive]
-/
theorem smul_Lp_neg (c : Mᵈᵐᵃ) (f : Lp E p μ) : c • (-f) = -(c • f) := by
  rcases f with ⟨⟨_⟩, _⟩; rfl

@[to_additive]
/--
theorem `smul_Lp_sub` / 定理 `smul_Lp_sub`

English:
theorem smul_Lp_sub
  given: (c : Mᵈᵐᵃ)
  statement: forall f g : Lp E p μ, c • (f - g) = c • f - c • g
  proof: by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

中文:
定理 smul_Lp_sub
  条件: (c : Mᵈᵐᵃ)
  结论: 对任意 f g : Lp E p μ, c • (f - g) = c • f - c • g
  证明: by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
-/
theorem smul_Lp_sub (c : Mᵈᵐᵃ) : forall f g : Lp E p μ, c • (f - g) = c • f - c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribSMul Mᵈᵐᵃ (Lp E p μ)
  body: rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

中文:
实例 :
  签名: DistribSMul Mᵈᵐᵃ (Lp E p μ)
  定义体: rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
-/
instance : DistribSMul Mᵈᵐᵃ (Lp E p μ) where
  smul_zero _ := rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

-- The next few lemmas follow from the `IsIsometricSMul` instance if `1 ≤ p`
@[to_additive (attr := simp)]
/--
theorem `norm_smul_Lp` / 定理 `norm_smul_Lp`

English:
theorem norm_smul_Lp
  given: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  statement: ‖c • f‖ = ‖f‖
  proof: Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]

中文:
定理 norm_smul_Lp
  条件: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  结论: ‖c • f‖ = ‖f‖
  证明: Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Lp.norm_compMeasurePreserving, norm_compMeasurePreserving
-/
theorem norm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
/--
theorem `nnnorm_smul_Lp` / 定理 `nnnorm_smul_Lp`

English:
theorem nnnorm_smul_Lp
  given: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  statement: ‖c • f‖₊ = ‖f‖₊
  proof: NNReal.eq Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]

中文:
定理 nnnorm_smul_Lp
  条件: (c : Mᵈᵐᵃ) (f : Lp E p μ)
  结论: ‖c • f‖₊ = ‖f‖₊
  证明: NNReal.eq Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Lp.norm_compMeasurePreserving, NNReal, NNReal.eq, norm_compMeasurePreserving
-/
theorem nnnorm_smul_Lp (c : Mᵈᵐᵃ) (f : Lp E p μ) : ‖c • f‖₊ = ‖f‖₊ :=
NNReal.eq Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
/--
theorem `dist_smul_Lp` / 定理 `dist_smul_Lp`

English:
theorem dist_smul_Lp
  given: (c : Mᵈᵐᵃ) (f g : Lp E p μ)
  statement: dist (c • f) (c • g) = dist f g
  proof: by
  simp only [dist, ← smul_Lp_neg, ← smul_Lp_add, norm_smul_Lp]

@[to_additive (attr := simp)]

中文:
定理 dist_smul_Lp
  条件: (c : Mᵈᵐᵃ) (f g : Lp E p μ)
  结论: dist (c • f) (c • g) = dist f g
  证明: by
  simp only [dist, ← smul_Lp_neg, ← smul_Lp_add, norm_smul_Lp]

@[to_additive (attr := simp)]

Depends on / 依赖: norm_smul_Lp, smul_Lp_add, smul_Lp_neg
-/
theorem dist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : dist (c • f) (c • g) = dist f g := by
  simp only [dist, ← smul_Lp_neg, ← smul_Lp_add, norm_smul_Lp]

@[to_additive (attr := simp)]
/--
theorem `edist_smul_Lp` / 定理 `edist_smul_Lp`

English:
theorem edist_smul_Lp
  given: (c : Mᵈᵐᵃ) (f g : Lp E p μ)
  statement: edist (c • f) (c • g) = edist f g
  proof: by
  simp only [Lp.edist_dist, dist_smul_Lp]

中文:
定理 edist_smul_Lp
  条件: (c : Mᵈᵐᵃ) (f g : Lp E p μ)
  结论: edist (c • f) (c • g) = edist f g
  证明: by
  simp only [Lp.edist_dist, dist_smul_Lp]

Depends on / 依赖: Lp.edist_dist, dist_smul_Lp, edist_dist
-/
theorem edist_smul_Lp (c : Mᵈᵐᵃ) (f g : Lp E p μ) : edist (c • f) (c • g) = edist f g := by
  simp only [Lp.edist_dist, dist_smul_Lp]

variable [Fact (1 <= p)]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIsometricSMul Mᵈᵐᵃ (Lp E p μ)
  body: ⟨edist_smul_Lp⟩

中文:
实例 :
  签名: IsIsometricSMul Mᵈᵐᵃ (Lp E p μ)
  定义体: ⟨edist_smul_Lp⟩

Depends on / 依赖: edist_smul_Lp
-/
instance : IsIsometricSMul Mᵈᵐᵃ (Lp E p μ) := ⟨edist_smul_Lp⟩

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [SMulInvariantMeasure M α μ] [MeasurableConstSMul M α]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Mᵈᵐᵃ (Lp E p μ)
  body: Subtype.val_injective.mulAction _ fun _ _ => rfl

中文:
实例 :
  签名: MulAction Mᵈᵐᵃ (Lp E p μ)
  定义体: Subtype.val_injective.mulAction _ fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.mulAction, mulAction, val_injective
-/
instance : MulAction Mᵈᵐᵃ (Lp E p μ) := Subtype.val_injective.mulAction _ fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction Mᵈᵐᵃ (Lp E p μ)
  body: Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

中文:
实例 :
  签名: DistribMulAction Mᵈᵐᵃ (Lp E p μ)
  定义体: Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.val_injective.distribMulAction, distribMulAction, val_injective
-/
instance : DistribMulAction Mᵈᵐᵃ (Lp E p μ) :=
  Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ => rfl⟩ fun _ _ => rfl

end MulAction

end DomMulAct
