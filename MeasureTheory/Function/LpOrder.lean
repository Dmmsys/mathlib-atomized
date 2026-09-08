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

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedAddCommGroup E]

section PartialOrder

variable [PartialOrder E]

/-
**MeasureTheory.Lp.coeFn_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <= g
参数：f g : Lp E p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coeFn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← AEEqFun.coeFn_le]
/-
**MeasureTheory.Lp.coeFn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_nonneg (f : Lp E p μ) : 0 <=ᵐ[μ] f ↔ 0 <= f
参数：f : Lp E p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `Filter.EventuallyEq.trans_le`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f =ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem coeFn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coeFn_le]
  exact ⟨(Lp.coeFn_zero E p μ).trans_le, (Lp.coeFn_zero E p μ).symm.trans_le⟩

variable [IsOrderedAddMonoid E]
/-
**MeasureTheory.Lp.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instAddLeftMono : AddLeftMono (Lp E p μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
instance instAddLeftMono : AddLeftMono (Lp E p μ) := by
  refine ⟨fun f g₁ g₂ hg₁₂ => ?_⟩
  rw [← coeFn_le] at hg₁₂ ⊢
  filter_upwards [coeFn_add f g₁, coeFn_add f g₂, hg₁₂] with _ h1 h2 h3
  rw [h1, h2, Pi.add_apply, Pi.add_apply]
  exact add_le_add le_rfl h3
/-
**MeasureTheory.Lp.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Lp`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid (Lp E p μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid (Lp E p μ) :=
  { add_le_add_left := fun _ _ => add_le_add_left }
/-
**MeasureTheory.Lp.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fact (1 ≤ p)] [ClosedIciTopology E] : OrderClosedTopology (Lp E p μ) where
  isClosed_le' := isClosed_le_of_isClosed_nonneg <| IsSeqClosed.isClosed <|
      fun f f₀ (hf : ∀ n, 0 ≤ f n) h_tendsto ↦ by
    simp only [← coeFn_nonneg] at hf ⊢
    obtain ⟨φ, -, hφ⟩ := tendstoInMeasure_of_tendsto_Lp h_tendsto |>.exists_seq_tendsto_ae
    filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
    exact ge_of_tendsto' hφx fun _ ↦ Set.mem_iInter.mp hx _

end PartialOrder

section Lattice

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

/-
**MeasureTheory.Lp._root_.MeasureTheory.MemLp.sup** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.sup {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊔ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))
/-
**MeasureTheory.Lp._root_.MeasureTheory.MemLp.inf** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.inf {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊓ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))
/-
**MeasureTheory.Lp._root_.MeasureTheory.MemLp.abs** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.MemLp.abs {f : α → E} (hf : MemLp f p μ) : MemLp |f| p μ :=
  hf.sup hf.neg
/-
**MeasureTheory.Lp.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：instLattice : Lattice (Lp E p μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
-/
instance instLattice : Lattice (Lp E p μ) :=
  Subtype.lattice
    (fun f g hf hg => by
      rw [mem_Lp_iff_memLp] at *
      exact (memLp_congr_ae (AEEqFun.coeFn_sup _ _)).mpr (hf.sup hg))
    fun f g hf hg => by
    rw [mem_Lp_iff_memLp] at *
    exact (memLp_congr_ae (AEEqFun.coeFn_inf _ _)).mpr (hf.inf hg)
/-
**MeasureTheory.Lp.coeFn_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sup`：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g)
 =ᵐ[μ] fun x => f x ⊔ g x
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
-/
theorem coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AEEqFun.coeFn_sup _ _
/-
**MeasureTheory.Lp.coeFn_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g
参数：f g : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_inf`：coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g)
 =ᵐ[μ] fun x => f x ⊓ g x
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
-/
theorem coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AEEqFun.coeFn_inf _ _
/-
**MeasureTheory.Lp.coeFn_abs** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x|
参数：f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEEqFun.coeFn_abs`：coeFn_abs {β} [TopologicalSpace β] [Lat
tice β] [TopologicalLattice β] [AddGroup β] [IsTopologicalAddGroup β] (f : α ->ₘ
[μ] β) : ⇑|f| =ᵐ[μ] f…
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
-/
theorem coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AEEqFun.coeFn_abs _
/-
**MeasureTheory.Lp.instHasSolidNorm** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp`
。
形式化陈述：instHasSolidNorm [Fact (1 <= p)] : HasSolidNorm (Lp E p μ)
参数：1 <= p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.eLpNorm_mono_ae`：eLpNorm_mono_ae {f : α -> F} {g : α -> G}
 (h : forallᵐ x ∂μ, ‖f x‖ <= ‖g x‖) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_abs`：coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x 
=> |f x|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasSolidNorm.solid`：∀ {α : Type u_1} {inst : NormedAddCommGroup α} {inst
_1 : Lattice α} [self : HasSolidNorm α] ⦃x y : α⦄,   |x| ≤ |y| → ‖x‖ ≤ ‖y‖
-/
instance instHasSolidNorm [Fact (1 ≤ p)] :
    HasSolidNorm (Lp E p μ) :=
  { solid := fun f g hfg => by
      rw [← coeFn_le] at hfg
      simp_rw [Lp.norm_def, ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)]
      refine eLpNorm_mono_ae ?_
      filter_upwards [hfg, Lp.coeFn_abs f, Lp.coeFn_abs g] with x hx hxf hxg
      rw [hxf, hxg] at hx
      exact HasSolidNorm.solid hx }

end Lattice

end Order

end Lp

end MeasureTheory

