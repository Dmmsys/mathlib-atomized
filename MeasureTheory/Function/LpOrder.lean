/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Order related properties of Lp spaces

## Results

- `Lp E p μ` is an ordered group when `E` is a `NormedLatticeAddCommGroup`.

## TODO

- move definitions of `Lp.posPart` and `Lp.negPart` to this file, and define them as
  `PosPart.pos` and `NegPart.neg` given by the lattice structure.

-/

public section



open TopologicalSpace MeasureTheory
open scoped ENNReal

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : Real>=0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedAddCommGroup E]

section PartialOrder

variable [PartialOrder E]

/--
theorem `coeFn_le` / 定理 `coeFn_le`

English:
theorem coeFn_le
  given: (f g : Lp E p μ)
  statement: f <=ᵐ[μ] g ↔ f <= g
  proof: by
  rw [← Subtype.coe_le_coe]; rw [← AEEqFun.coeFn_le]

中文:
定理 coeFn_le
  条件: (f g : Lp E p μ)
  结论: f <=ᵐ[μ] g ↔ f <= g
  证明: by
  rw [← Subtype.coe_le_coe]; rw [← AEEqFun.coeFn_le]

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_le, Subtype, Subtype.coe_le_coe, coeFn_le, coe_le_coe
-/
theorem coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <= g := by
  rw [← Subtype.coe_le_coe]; rw [← AEEqFun.coeFn_le]

/--
theorem `coeFn_nonneg` / 定理 `coeFn_nonneg`

English:
theorem coeFn_nonneg
  given: (f : Lp E p μ)
  statement: 0 <=ᵐ[μ] f ↔ 0 <= f
  proof: by
  rw [← coeFn_le]
  exact ⟨(Lp.coeFn_zero E p μ).trans_le, (Lp.coeFn_zero E p μ).symm.trans_le⟩

中文:
定理 coeFn_nonneg
  条件: (f : Lp E p μ)
  结论: 0 <=ᵐ[μ] f ↔ 0 <= f
  证明: by
  rw [← coeFn_le]
  exact ⟨(Lp.coeFn_zero E p μ).trans_le, (Lp.coeFn_zero E p μ).symm.trans_le⟩

Depends on / 依赖: Lp.coeFn_zero, coeFn_le, coeFn_zero, symm.trans_le, trans_le
-/
theorem coeFn_nonneg (f : Lp E p μ) : 0 <=ᵐ[μ] f ↔ 0 <= f := by
  rw [← coeFn_le]
  exact ⟨(Lp.coeFn_zero E p μ).trans_le, (Lp.coeFn_zero E p μ).symm.trans_le⟩

variable [IsOrderedAddMonoid E]

/--
Instance `instAddLeftMono` / 实例 `instAddLeftMono`

English:
instance instAddLeftMono
  signature: : AddLeftMono (Lp E p μ)
  body: by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1]; rw [h2]; rw [Pi.add_apply]; rw [Pi.add_apply]
  exact add_le_add le_rfl h3

中文:
实例 instAddLeftMono
  签名: : AddLeftMono (Lp E p μ)
  定义体: by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1]; rw [h2]; rw [Pi.add_apply]; rw [Pi.add_apply]
  exact add_le_add le_rfl h3

Depends on / 依赖: Pi.add_apply, add_apply, add_le_add, coeFn_add, coeFn_le, filter_upwards, le_rfl
-/
instance instAddLeftMono : AddLeftMono (Lp E p μ) := by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1]; rw [h2]; rw [Pi.add_apply]; rw [Pi.add_apply]
  exact add_le_add le_rfl h3

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid (Lp E p μ)
  body: { add_le_add_left := fun _ _ => add_le_add_left }

中文:
实例 instIsOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 (Lp E p μ)
  定义体: { add_le_add_left := fun _ _ => add_le_add_left }

Depends on / 依赖: add_le_add_left
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (Lp E p μ) :=
  { add_le_add_left := fun _ _ => add_le_add_left }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: (1 <= p)] [ClosedIciTopology E] : OrderClosedTopology (Lp E p μ) where
  body: isClosed_le_of_isClosed_nonneg IsSeqClosed.isClosed
      fun f f₀ (hf : forall n, 0 <= f n) h_tendsto => by
    simp only [← coeFn_nonneg] at hf ⊢
.exists_seq_tendsto_ae obtain ⟨φ, -, hφ⟩ := tendstoInMeasure_of_tendsto_Lp h_tendsto
    filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
    exact ge_of_tendsto' hφx fun _ => Set.mem_iInter.mp hx _

中文:
实例 [Fact
  签名: (1 <= p)] [ClosedIci拓扑 E] : OrderClosed拓扑 (Lp E p μ) where
  定义体: isClosed_le_of_isClosed_nonneg IsSeqClosed.isClosed
      fun f f₀ (hf : forall n, 0 <= f n) h_tendsto => by
    simp only [← coeFn_nonneg] at hf ⊢
.exists_seq_tendsto_ae obtain ⟨φ, -, hφ⟩ := tendstoInMeasure_of_tendsto_Lp h_tendsto
    filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
    exact ge_of_tendsto' hφx fun _ => Set.mem_iInter.mp hx _

Depends on / 依赖: IsSeqClosed, IsSeqClosed.isClosed, isClosed, isClosed_le_of_isClosed_nonneg
-/
instance [Fact (1 <= p)] [ClosedIciTopology E] : OrderClosedTopology (Lp E p μ) where
isClosed_le' := isClosed_le_of_isClosed_nonneg IsSeqClosed.isClosed
      fun f f₀ (hf : forall n, 0 <= f n) h_tendsto => by
    simp only [← coeFn_nonneg] at hf ⊢
.exists_seq_tendsto_ae obtain ⟨φ, -, hφ⟩ := tendstoInMeasure_of_tendsto_Lp h_tendsto
    filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
    exact ge_of_tendsto' hφx fun _ => Set.mem_iInter.mp hx _

end PartialOrder

section Lattice

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

/--
theorem `_root_.MeasureTheory.MemLp.sup` / 定理 `_root_.MeasureTheory.MemLp.sup`

English:
theorem _root_.MeasureTheory.MemLp.sup
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))

中文:
定理 _root_.测度论.MemLp.上确界
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, MemLp.mono, hf.norm.add, hg.norm, norm_sup_le_add, of_forall
-/
theorem _root_.MeasureTheory.MemLp.sup {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊔ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))

/--
theorem `_root_.MeasureTheory.MemLp.inf` / 定理 `_root_.MeasureTheory.MemLp.inf`

English:
theorem _root_.MeasureTheory.MemLp.inf
  given: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  proof: MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))

中文:
定理 _root_.测度论.MemLp.下确界
  条件: {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ)
  证明: MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, MemLp.mono, hf.norm.add, hg.norm, norm_inf_le_add, of_forall
-/
theorem _root_.MeasureTheory.MemLp.inf {f g : α -> E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊓ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))

/--
theorem `_root_.MeasureTheory.MemLp.abs` / 定理 `_root_.MeasureTheory.MemLp.abs`

English:
theorem _root_.MeasureTheory.MemLp.abs
  given: {f : α -> E} (hf : MemLp f p μ)
  statement: MemLp |f| p μ
  proof: hf.sup hf.neg

中文:
定理 _root_.测度论.MemLp.abs
  条件: {f : α -> E} (hf : MemLp f p μ)
  结论: MemLp |f| p μ
  证明: hf.sup hf.neg

Depends on / 依赖: hf.neg, hf.sup
-/
theorem _root_.MeasureTheory.MemLp.abs {f : α -> E} (hf : MemLp f p μ) : MemLp |f| p μ :=
  hf.sup hf.neg

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (Lp E p μ)
  body: Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memLp] at *
      exact (memLp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memLp] at *
    exact (memLp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)

中文:
实例 instLattice
  签名: : 格 (Lp E p μ)
  定义体: Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memLp] at *
      exact (memLp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memLp] at *
    exact (memLp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_inf, AEEqFun.coeFn_sup, Subtype, Subtype.lattice, coeFn_inf, coeFn_sup, hf.inf, hf.sup, lattice, memLp_congr_ae, mem_Lp_iff_memLp
-/
instance instLattice : Lattice (Lp E p μ) :=
  Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memLp] at *
      exact (memLp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memLp] at *
    exact (memLp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)

/--
theorem `coeFn_sup` / 定理 `coeFn_sup`

English:
theorem coeFn_sup
  given: (f g : Lp E p μ)
  statement: ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g
  proof: AEEqFun.coeFn_sup _ _

中文:
定理 coeFn_sup
  条件: (f g : Lp E p μ)
  结论: ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g
  证明: AEEqFun.coeFn_sup _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_sup, coeFn_sup
-/
theorem coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AEEqFun.coeFn_sup _ _

/--
theorem `coeFn_inf` / 定理 `coeFn_inf`

English:
theorem coeFn_inf
  given: (f g : Lp E p μ)
  statement: ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g
  proof: AEEqFun.coeFn_inf _ _

中文:
定理 coeFn_inf
  条件: (f g : Lp E p μ)
  结论: ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g
  证明: AEEqFun.coeFn_inf _ _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_inf, coeFn_inf
-/
theorem coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AEEqFun.coeFn_inf _ _

/--
theorem `coeFn_abs` / 定理 `coeFn_abs`

English:
theorem coeFn_abs
  given: (f : Lp E p μ)
  statement: ⇑|f| =ᵐ[μ] fun x => |f x|
  proof: AEEqFun.coeFn_abs _

中文:
定理 coeFn_abs
  条件: (f : Lp E p μ)
  结论: ⇑|f| =ᵐ[μ] fun x => |f x|
  证明: AEEqFun.coeFn_abs _

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_abs, coeFn_abs
-/
theorem coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AEEqFun.coeFn_abs _

/--
Instance `instHasSolidNorm` / 实例 `instHasSolidNorm`

English:
instance instHasSolidNorm
  signature: [Fact (1 <= p)]
  body: { solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)]
      refine eLpNorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf]; rw [hxg] at hx
      exact HasSolidNorm.solid hx }

中文:
实例 instHasSolidNorm
  签名: [Fact (1 <= p)]
  定义体: { solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)]
      refine eLpNorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf]; rw [hxg] at hx
      exact HasSolidNorm.solid hx }

Depends on / 依赖: ENNReal, ENNReal.toReal_le_toReal, HasSolidNorm, HasSolidNorm.solid, Lp.coeFn_abs, Lp.eLpNorm_ne_top, Lp.norm_def, coeFn_abs, coeFn_le, eLpNorm_mono_ae, eLpNorm_ne_top, filter_upwards, norm_def, simp_rw, toReal_le_toReal
-/
instance instHasSolidNorm [Fact (1 <= p)] :
    HasSolidNorm (Lp E p μ) :=
  { solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)]
      refine eLpNorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf]; rw [hxg] at hx
      exact HasSolidNorm.solid hx }

end Lattice

end Order

end Lp

end MeasureTheory
