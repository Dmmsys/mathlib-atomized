/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Group.AEStabilizer
public import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodic group actions

A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/

public section

open Set Filter MeasureTheory MulAction
open scoped Pointwise

/--
An additive group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar addition `(g +ᵥ ·)`, `g : G`,
then it is either null or conull.
-/
/-
**ErgodicVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → (α : Type u_2) → [VAdd G α] → {x : MeasurableSpace α} → M
easureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group action of `G` on a space `α` with measure `μ` is called *ergod
ic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar addition `(g +ᵥ ·)`, `g : G`,
then it is either null or conull.
-/
class ErgodicVAdd (G α : Type*) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends VAddInvariantMeasure G α μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s : Set α} : MeasurableSet s →
    (∀ g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) → EventuallyConst s (ae μ)

/--
A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/
@[to_additive, mk_iff]
/-
**ErgodicSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → (α : Type u_2) → [SMul G α] → {x : MeasurableSpace α} → M
easureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/
class ErgodicSMul (G α : Type*) [SMul G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends SMulInvariantMeasure G α μ where
  aeconst_of_forall_preimage_smul_ae_eq {s : Set α} : MeasurableSet s →
    (∀ g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) → EventuallyConst s (ae μ)

attribute [to_additive] ergodicSMul_iff

namespace MeasureTheory

variable (G : Type*) {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

@[to_additive]
/-
**MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：aeconst_of_forall_preimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : 
Set α} (hm : NullMeasurableSet s μ) (h : forall g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) : 
EventuallyConst s (ae μ)
参数：hm : NullMeasurableSet s μ；h : forall g : G, (g • ·) ⁻¹' s =ᵐ[μ] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyConst.congr`：∀ {α : Type u_1} {β : Type u_2} {l : Filte
r α} {f g : α → β},   Filter.EventuallyConst f l → f =ᶠ[l] g → Filter.Eventually
Const g l
· 使用定理 `ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq`：∀ {G : Type u_1} {α :
 Type u_2} {inst : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure 
α}   [self : ErgodicSMul G α μ] {s : Se…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.tendsto_smul_ae`：tendsto_smul_ae (c : G) : Filter.Tendsto 
(c • ·) (ae μ) (ae μ)
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem aeconst_of_forall_preimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : Set α}
    (hm : NullMeasurableSet s μ) (h : ∀ g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) := by
  rcases hm with ⟨t, htm, hst⟩
  refine .congr ?_ hst.symm
  refine ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq htm fun g : G ↦ ?_
  refine .trans (.trans ?_ (h g)) hst
  exact tendsto_smul_ae _ _ hst.symm

section Group

variable [Group G] [MulAction G α] [ErgodicSMul G α μ] {s : Set α}

@[to_additive]
/-
**MeasureTheory.aeconst_of_forall_smul_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：aeconst_of_forall_smul_ae_eq (hm : NullMeasurableSet s μ) (h : forall g : 
G, g • s =ᵐ[μ] s) : EventuallyConst s (ae μ)
参数：hm : NullMeasurableSet s μ；h : forall g : G, g • s =ᵐ[μ] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq`：aeconst_of_forall_p
reimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : Set α} (hm : NullMeasurab
leSet s μ) (h : forall g : G, (g • ·) ⁻¹'…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
-/
theorem aeconst_of_forall_smul_ae_eq (hm : NullMeasurableSet s μ) (h : ∀ g : G, g • s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  aeconst_of_forall_preimage_smul_ae_eq G hm fun g ↦ by
    simpa only [preimage_smul] using h g⁻¹

@[to_additive]
/-
**MeasureTheory._root_.MulAction.aeconst_of_aestabilizer_eq_top** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAction.aeconst_of_aestabilizer_eq_top
    (hm : NullMeasurableSet s μ) (h : aestabilizer G μ s = ⊤) : EventuallyConst s (ae μ) :=
  aeconst_of_forall_smul_ae_eq G hm <| (Subgroup.eq_top_iff' _).1 h

end Group

/-
**MeasureTheory._root_.ErgodicSMul.of_aestabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ErgodicSMul.of_aestabilizer [Group G] [MulAction G α] [SMulInvariantMeasure G α μ]
    (h : ∀ s, MeasurableSet s → aestabilizer G μ s = ⊤ → EventuallyConst s (ae μ)) :
    ErgodicSMul G α μ :=
  ⟨fun hm hs ↦ h _ hm <| (Subgroup.eq_top_iff' _).2 fun g ↦ by
    simpa only [preimage_smul_inv] using! hs g⁻¹⟩
/-
**MeasureTheory.ergodicSMul_iterateMulAct** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ergodicSMul_iterateMulAct {f : α -> α} (hf : Measurable f) : ErgodicSMul (
IterateMulAct f) α μ ↔ Ergodic f μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.preimage_iterate`：preimage_iterate {s : Set α} (h : I
sFixedPt (Set.preimage f) s) (n : Nat) : IsFixedPt (Set.preimage f^[n]) s
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Ergodic.toMeasurePreserving`：∀ {α : Type u_1} {m : MeasurableSpace α} {f
 : α → α} {μ : autoParam (MeasureTheory.Measure α) Ergodic._auto_1},   Ergodic f
 μ → MeasureTheor…
· 使用定理 `QuasiErgodic.aeconst_set₀`：aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : N
ullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) : EventuallyConst s (ae μ)
· 使用定理 `Ergodic.quasiErgodic`：quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem ergodicSMul_iterateMulAct {f : α → α} (hf : Measurable f) :
    ErgodicSMul (IterateMulAct f) α μ ↔ Ergodic f μ := by
  simp only [ergodicSMul_iff, smulInvariantMeasure_iterateMulAct, hf]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ⟨?_⟩⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  · intro s hm hs
    refine h₂ hm fun n ↦ ?_
    nth_rewrite 2 [← Function.IsFixedPt.preimage_iterate hs n.val]
    rfl
  · intro s hm hs
    exact h.quasiErgodic.aeconst_set₀ hm.nullMeasurableSet <| hs (.mk 1)

end MeasureTheory

