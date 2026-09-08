/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Ergodicity from minimality

In this file we prove that the left shift `(a * ·)` on a compact topological group `G`
is ergodic with respect to the Haar measure if and only if it is minimal,
i.e., the powers `a ^ n` are dense in `G`.

The proof of the more difficult "if minimal, then ergodic" implication
is based on the ergodicity of the left action of a group on itself
and the following fact that we prove in `ergodic_smul_of_denseRange_pow` below:

If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map.

We also prove that a continuous monoid homomorphism `f : G →* G` is ergodic,
if it is surjective and the preimages of `1` under iterations of `f` are dense in the group.
This theorem applies, e.g., to the map `z ↦ n • z` on the additive circle or a torus.
-/

public section

open MeasureTheory Filter Set Function
open scoped Pointwise Topology

section SMul

variable {M : Type*} [TopologicalSpace M]
  {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [SMul M X] [ContinuousSMul M X]
  {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] {s : Set X}

/-- Let `M` act continuously on an R₁ topological space `X`.
Let `μ` be a finite inner regular measure on `X` which is ergodic with respect to this action.
If a null measurable set `s` is a.e. equal
to its preimages under the action of a dense set of elements of `M`,
then it is either null or conull. -/
@[to_additive /-- Let `M` act continuously on an R₁ topological space `X`.
Let `μ` be a finite inner regular measure on `X` which is ergodic with respect to this action.
If a null measurable set `s` is a.e. equal
to its preimages under the action of a dense set of elements of `M`,
then it is either null or conull. -/]
/-
**aeconst_of_dense_setOfPred_preimage_smul_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aeconst_of_dense_setOfPred_preimage_smul_ae (hsm : NullMeasurableSet s μ) 
(hd : Dense {g : M | (g • ·) ⁻¹' s =ᵐ[μ] s}) : EventuallyConst s (ae μ)
参数：hsm : NullMeasurableSet s μ；hd : Dense {g : M | (g • ·) ⁻¹' s =ᵐ[μ] s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq`：aeconst_of_forall_p
reimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : Set α} (hm : NullMeasurab
leSet s μ) (h : forall g : G, (g • ·) ⁻¹'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `ContinuousSMul.continuous_smul`：∀ {M : Type u_1} {X : Type u_2} {inst : 
SMul M X} {inst_1 : TopologicalSpace M} {inst_2 : TopologicalSpace X}   [self : 
ContinuousSMul M X],…
· 使用定理 `MeasureTheory.isClosed_setOfPred_preimage_ae_eq`：isClosed_setOfPred_prei
mage_ae_eq {f : Z -> C(X, Y)} (hf : Continuous f) (hfm : forall z, MeasurePreser
ving (f z) μ ν) (s : Set X) {t : Set …
· 使用定理 `MeasureTheory.Measure.InnerRegular.instInnerRegularCompactLTTop`：∀ {α : 
Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Top
ologicalSpace α]   [μ.InnerRegular], μ.InnerRegularCo…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
-/
theorem aeconst_of_dense_setOfPred_preimage_smul_ae (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : M | (g • ·) ⁻¹' s =ᵐ[μ] s}) : EventuallyConst s (ae μ) := by
  borelize M
  refine aeconst_of_forall_preimage_smul_ae_eq M hsm ?_
  rwa [dense_iff_closure_eq, IsClosed.closure_eq, eq_univ_iff_forall] at hd
  let f : C(M × X, X) := ⟨(· • ·).uncurry, continuous_smul⟩
  exact isClosed_setOfPred_preimage_ae_eq f.curry.continuous (measurePreserving_smul · μ) _ hsm
    (measure_ne_top _ _)

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_ae := aeconst_of_dense_setOfPred_preimage_smul_ae

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_ae := aeconst_of_dense_setOfPred_preimage_vadd_ae

@[to_additive]
/-
**aeconst_of_dense_setOfPred_preimage_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aeconst_of_dense_setOfPred_preimage_smul_eq (hsm : NullMeasurableSet s μ) 
(hd : Dense {g : M | (g • ·) ⁻¹' s = s}) : EventuallyConst s (ae μ)
参数：hsm : NullMeasurableSet s μ；hd : Dense {g : M | (g • ·) ⁻¹' s = s}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aeconst_of_dense_setOfPred_preimage_smul_ae`：aeconst_of_dense_setOfPred_
preimage_smul_ae (hsm : NullMeasurableSet s μ) (hd : Dense {g : M | (g • ·) ⁻¹' 
s =ᵐ[μ] s}) : EventuallyConst s (…
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Filter.EventuallyEq.of_eq`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g : α → β}, f = g → f =ᶠ[l] g
-/
theorem aeconst_of_dense_setOfPred_preimage_smul_eq (hsm : NullMeasurableSet s μ)
    (hd : Dense {g : M | (g • ·) ⁻¹' s = s}) : EventuallyConst s (ae μ) :=
  aeconst_of_dense_setOfPred_preimage_smul_ae hsm <| hd.mono fun _ h ↦ mem_ofPred.2 <| .of_eq h

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_smul_eq := aeconst_of_dense_setOfPred_preimage_smul_eq

@[deprecated (since := "2026-07-09")]
alias aeconst_of_dense_setOf_preimage_vadd_eq := aeconst_of_dense_setOfPred_preimage_vadd_eq

/-- If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map. -/
@[to_additive /-- If an additive monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its natural multiples are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the vector addition of `g` is an ergodic map. -/]
/-
**ergodic_smul_of_denseRange_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ergodic_smul_of_denseRange_pow {M : Type*} [Monoid M] [TopologicalSpace M]
 [MulAction M X] [ContinuousSMul M X] {g : M} (hg : DenseRange (g ^ · : Nat -> M
)) (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] : Er
godic (g • ·) μ
参数：hg : DenseRange (g ^ · : Nat -> M)；μ : Measure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `aeconst_of_dense_setOfPred_preimage_smul_eq`：aeconst_of_dense_setOfPred_
preimage_smul_eq (hsm : NullMeasurableSet s μ) (hd : Dense {g : M | (g • ·) ⁻¹' 
s = s}) : EventuallyConst s (ae μ…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_iterate`：∀ {M : Type u_1} {α : Type u_5} [inst : Monoid M] [inst_1 
: MulAction M α] (a : M) (n : ℕ),   (fun x => a • x)^[n] = fun x => a ^ n • x
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
-/
theorem ergodic_smul_of_denseRange_pow {M : Type*} [Monoid M] [TopologicalSpace M]
    [MulAction M X] [ContinuousSMul M X] {g : M} (hg : DenseRange (g ^ · : ℕ → M))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul M X μ] :
    Ergodic (g • ·) μ := by
  borelize M
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs ↦ ?_⟩⟩
  refine aeconst_of_dense_setOfPred_preimage_smul_eq hsm.nullMeasurableSet (hg.mono ?_)
  refine range_subset_iff.2 fun n ↦ ?_
  rw [mem_ofPred, ← smul_iterate, preimage_iterate_eq, iterate_fixed hs]

end SMul

section IsScalarTower

variable {M X : Type*} [Monoid M] [SMul M X]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular]

/-- If `N` acts continuously and ergodically on `X` and `M` acts minimally on `N`,
then the corresponding action of `M` on `X` is ergodic. -/
@[to_additive
  /-- If `N` acts additively continuously and ergodically on `X` and `M` acts minimally on `N`,
then the corresponding action of `M` on `X` is ergodic. -/]
/-
**ErgodicSMul.trans_isMinimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ErgodicSMul.trans_isMinimal (N : Type*) [MulAction M N] [Monoid N] [Topolo
gicalSpace N] [MulAction.IsMinimal M N] [MulAction N X] [IsScalarTower M N X] [C
ontinuousSMul N X] [ErgodicSMul N X μ] : ErgodicSMul M X μ where measure_preimag
e_smul c s hsm
参数：N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `MeasureTheory.SMulInvariantMeasure.measure_preimage_smul`：∀ {M : Type u_
1} {α : Type u_2} {inst : SMul M α} {x : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [self : MeasureTheory.SMulInvarian…
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aeconst_of_dense_setOfPred_preimage_smul_ae`：aeconst_of_dense_setOfPred_
preimage_smul_ae (hsm : NullMeasurableSet s μ) (hd : Dense {g : M | (g • ·) ⁻¹' 
s =ᵐ[μ] s}) : EventuallyConst s (…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MulAction.dense_orbit`：MulAction.dense_orbit [IsMinimal M α] (x : α) : D
ense (orbit M x)
-/
theorem ErgodicSMul.trans_isMinimal (N : Type*) [MulAction M N]
    [Monoid N] [TopologicalSpace N] [MulAction.IsMinimal M N]
    [MulAction N X] [IsScalarTower M N X] [ContinuousSMul N X] [ErgodicSMul N X μ] :
    ErgodicSMul M X μ where
  measure_preimage_smul c s hsm := by
    simpa only [smul_one_smul] using SMulInvariantMeasure.measure_preimage_smul (c • 1 : N) hsm
  aeconst_of_forall_preimage_smul_ae_eq {s} hsm hs := by
    refine aeconst_of_dense_setOfPred_preimage_smul_ae (M := N) hsm.nullMeasurableSet ?_
    refine (MulAction.dense_orbit M 1).mono ?_
    rintro _ ⟨g, rfl⟩
    simpa using hs g

end IsScalarTower

section MulActionGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
  {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] {s : Set X}

@[to_additive]
/-
**aeconst_of_dense_aestabilizer_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aeconst_of_dense_aestabilizer_smul (hsm : NullMeasurableSet s μ) (hd : Den
se (MulAction.aestabilizer G μ s : Set G)) : EventuallyConst s (ae μ)
参数：hsm : NullMeasurableSet s μ；hd : Dense (MulAction.aestabilizer G μ s : Set G)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `aeconst_of_dense_setOfPred_preimage_smul_ae`：aeconst_of_dense_setOfPred_
preimage_smul_ae (hsm : NullMeasurableSet s μ) (hd : Dense {g : M | (g • ·) ⁻¹' 
s =ᵐ[μ] s}) : EventuallyConst s (…
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Dense.preimage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set Y},   Dense s → IsOpenMap
 f →…
· 使用定理 `isOpenMap_inv`：isOpenMap_inv : IsOpenMap (Inv.inv : G -> G)
-/
theorem aeconst_of_dense_aestabilizer_smul (hsm : NullMeasurableSet s μ)
    (hd : Dense (MulAction.aestabilizer G μ s : Set G)) : EventuallyConst s (ae μ) :=
  aeconst_of_dense_setOfPred_preimage_smul_ae hsm <|
    (hd.preimage (isOpenMap_inv _)).mono fun g hg ↦ by
    simpa only [preimage_smul] using! hg

set_option backward.isDefEq.respectTransparency.types false in
/-- If a monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its integer powers are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the scalar multiplication by `g` is an ergodic map. -/
@[to_additive /-- If an additive monoid `M` continuously acts on an R₁ topological space `X`,
`g` is an element of `M` such that its integer multiples are dense in `M`,
and `μ` is a finite inner regular measure on `X` which is ergodic with respect to the action of `M`,
then the vector addition of `g` is an ergodic map. -/]
/-
**ergodic_smul_of_denseRange_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ergodic_smul_of_denseRange_zpow {g : G} (hg : DenseRange (g ^ · : Int -> G
)) (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] : Er
godic (g • ·) μ
参数：hg : DenseRange (g ^ · : Int -> G)；μ : Measure X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ErgodicSMul.toSMulInvariantMeasure`：∀ {G : Type u_1} {α : Type u_2} {ins
t : SMul G α} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [self : Er
godicSMul G α μ], Measur…
· 使用定理 `aeconst_of_dense_aestabilizer_smul`：aeconst_of_dense_aestabilizer_smul (
hsm : NullMeasurableSet s μ) (hd : Dense (MulAction.aestabilizer G μ s : Set G))
 : EventuallyConst s (ae…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.coe_zpowers`：coe_zpowers (g : G) : ↑(zpowers g) = Set.range (g 
^ · : Int -> G)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Subgroup.zpowers_inv`：zpowers_inv : zpowers g⁻¹ = zpowers g
· 使用定理 `Subgroup.zpowers_le`：zpowers_le {g : G} {H : Subgroup G} : zpowers g <= 
H ↔ g in H
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MulAction.mem_aestabilizer`：mem_aestabilizer : g in aestabilizer G μ s ↔
 g • s =ᵐ[μ] s
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem ergodic_smul_of_denseRange_zpow {g : G} (hg : DenseRange (g ^ · : ℤ → G))
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegular] [ErgodicSMul G X μ] :
    Ergodic (g • ·) μ := by
  borelize G
  refine ⟨measurePreserving_smul _ _, ⟨fun s hsm hs ↦ ?_⟩⟩
  refine aeconst_of_dense_aestabilizer_smul hsm.nullMeasurableSet (hg.mono ?_)
  rw [← Subgroup.coe_zpowers, SetLike.coe_subset_coe, ← Subgroup.zpowers_inv, Subgroup.zpowers_le,
    MulAction.mem_aestabilizer, ← preimage_smul, hs]

end MulActionGroup

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

/-- If the left multiplication by `g` is ergodic
with respect to a measure which is positive on nonempty open sets,
then the integer powers of `g` are dense in `G`. -/
@[to_additive /-- If the left addition of `g` is ergodic
with respect to a measure which is positive on nonempty open sets,
then the integer multiples of `g` are dense in `G`. -/]
/-
**DenseRange.zpow_of_ergodic_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.zpow_of_ergodic_mul_left [OpensMeasurableSpace G] {μ : Measure 
G} [μ.IsOpenPosMeasure] {g : G} (hg : Ergodic (g * ·) μ) : DenseRange (g ^ · : I
nt -> G)
参数：hg : Ergodic (g * ·) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.fun_div'`：∀ {G : Type u_1} {X : Type u_3} [inst : Topological
Space X] [inst_1 : TopologicalSpace G] [inst_2 : Div G]   [ContinuousDiv G] {f g
 : X → G}…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
（共 53 条，此处仅展示前 30 条）
-/
theorem DenseRange.zpow_of_ergodic_mul_left [OpensMeasurableSpace G]
    {μ : Measure G} [μ.IsOpenPosMeasure] {g : G} (hg : Ergodic (g * ·) μ) :
    DenseRange (g ^ · : ℤ → G) := by
  intro a
  by_contra h
  obtain ⟨V, hV₁, hVo, hV⟩ :
      ∃ V : Set G, 1 ∈ V ∧ IsOpen V ∧ ∀ x ∈ V, ∀ y ∈ V, ∀ m : ℤ, g ^ m ≠ a * x / y := by
    rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds] at h
    have : Tendsto (fun (x, y) ↦ a * x / y) (𝓝 1) (𝓝 a) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    rw [nhds_prod_eq] at this
    simpa [(nhds_basis_opens (1 : G)).prod_self.mem_iff, prod_subset_iff, and_assoc] using this h
  set s := ⋃ m : ℤ, g ^ m • V
  have hso : IsOpen s := isOpen_iUnion fun m ↦ hVo.smul _
  have hsne : s.Nonempty := ⟨1, mem_iUnion.2 ⟨0, by simpa⟩⟩
  have hd : Disjoint s (a • V) := by
    simp_rw [s, disjoint_iUnion_left, disjoint_left]
    rintro m _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hV y hy x hx m
    simp_all
  have hgs : (g * ·) ⁻¹' s = s := by
    simp only [s, preimage_iUnion, ← smul_eq_mul, preimage_smul]
    refine iUnion_congr_of_surjective _ (add_left_surjective (-1)) fun m ↦ ?_
    simp [zpow_add, mul_smul]
  cases hg.measure_self_or_compl_eq_zero hso.measurableSet hgs with
  | inl h => exact hso.measure_ne_zero _ hsne h
  | inr h =>
    refine (hVo.smul a).measure_ne_zero μ (.image _ ⟨1, hV₁⟩) (measure_mono_null ?_ h)
    rwa [disjoint_right] at hd

variable [SecondCountableTopology G] [BorelSpace G] {g : G}

@[to_additive]
/-
**ergodic_mul_left_of_denseRange_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ergodic_mul_left_of_denseRange_pow (hg : DenseRange (g ^ · : Nat -> G)) (μ
 : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] : Ergo
dic (g * ·) μ
参数：hg : DenseRange (g ^ · : Nat -> G)；μ : Measure G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ergodic_smul_of_denseRange_pow`：ergodic_smul_of_denseRange_pow {M : Type
*} [Monoid M] [TopologicalSpace M] [MulAction M X] [ContinuousSMul M X] {g : M} 
(hg : DenseRange (g …
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `instIsTopologicalTorsor`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Top
ologicalSpace G] [IsTopologicalGroup G], IsTopologicalTorsor G
· 使用定理 `instErgodicSMulOfIsMulLeftInvariant`：∀ {G : Type u_1} [inst : Group G] [
inst_1 : MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]   {μ : MeasureT
heory.Measure G} [Measure…
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
-/
theorem ergodic_mul_left_of_denseRange_pow (hg : DenseRange (g ^ · : ℕ → G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_pow hg μ

@[to_additive]
/-
**ergodic_mul_left_of_denseRange_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ergodic_mul_left_of_denseRange_zpow (hg : DenseRange (g ^ · : Int -> G)) (
μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] : Erg
odic (g * ·) μ
参数：hg : DenseRange (g ^ · : Int -> G)；μ : Measure G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ergodic_smul_of_denseRange_zpow`：ergodic_smul_of_denseRange_zpow {g : G}
 (hg : DenseRange (g ^ · : Int -> G)) (μ : Measure X) [IsFiniteMeasure μ] [μ.Inn
erRegular] [ErgodicSM…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `instIsTopologicalTorsor`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Top
ologicalSpace G] [IsTopologicalGroup G], IsTopologicalTorsor G
· 使用定理 `instErgodicSMulOfIsMulLeftInvariant`：∀ {G : Type u_1} [inst : Group G] [
inst_1 : MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]   {μ : MeasureT
heory.Measure G} [Measure…
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
-/
theorem ergodic_mul_left_of_denseRange_zpow (hg : DenseRange (g ^ · : ℤ → G))
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant] :
    Ergodic (g * ·) μ :=
  ergodic_smul_of_denseRange_zpow hg μ

@[to_additive]
/-
**ergodic_mul_left_iff_denseRange_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ergodic_mul_left_iff_denseRange_zpow (μ : Measure G) [IsFiniteMeasure μ] [
μ.InnerRegular] [μ.IsMulLeftInvariant] [NeZero μ] : Ergodic (g * ·) μ ↔ DenseRan
ge (g ^ · : Int -> G)
参数：μ : Measure G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.zpow_of_ergodic_mul_left`：DenseRange.zpow_of_ergodic_mul_left
 [OpensMeasurableSpace G] {μ : Measure G} [μ.IsOpenPosMeasure] {g : G} (hg : Erg
odic (g * ·) μ) : DenseRa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.isOpenPosMeasure_of_mulLeftInvariant_of_innerRegular`：∀ {G
 : Type u_1} [inst : MeasurableSpace G] [inst_1 : TopologicalSpace G] [BorelSpac
e G] {μ : MeasureTheory.Measure G}   [inst_3 : Group G] …
· 使用定理 `ergodic_mul_left_of_denseRange_zpow`：ergodic_mul_left_of_denseRange_zpow
 (hg : DenseRange (g ^ · : Int -> G)) (μ : Measure G) [IsFiniteMeasure μ] [μ.Inn
erRegular] [μ.IsMulLeftIn…
-/
theorem ergodic_mul_left_iff_denseRange_zpow (μ : Measure G) [IsFiniteMeasure μ]
    [μ.InnerRegular] [μ.IsMulLeftInvariant] [NeZero μ] :
    Ergodic (g * ·) μ ↔ DenseRange (g ^ · : ℤ → G) :=
  ⟨.zpow_of_ergodic_mul_left, (ergodic_mul_left_of_denseRange_zpow · μ)⟩

end IsTopologicalGroup

namespace MonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Let `f : G →* G` be a group endomorphism of a topological group with second countable topology.
If the preimages of `1` under the iterations of `f` are dense,
then it is pre-ergodic with respect to any finite inner regular left invariant measure. -/
@[to_additive /-- Let `f : G →+ G` be an additive group endomorphism
of a topological additive group with second countable topology.
If the preimages of `0` under the iterations of `f` are dense,
then it is pre-ergodic with respect to any finite inner regular left invariant measure. -/]
/-
**MonoidHom.preErgodic_of_dense_iUnion_preimage_one** 是 Mathlib 中的一个定理，位于命名空间 `M
onoidHom`。
形式化陈述：preErgodic_of_dense_iUnion_preimage_one {μ : Measure G} [IsFiniteMeasure μ
] [μ.InnerRegular] [μ.IsMulLeftInvariant] (f : G ->* G) (hf : Dense (⋃ n, f^[n] 
⁻¹' 1)) : PreErgodic f μ
参数：f : G ->* G；hf : Dense (⋃ n, f^[n] ⁻¹' 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aeconst_of_dense_setOfPred_preimage_smul_eq`：aeconst_of_dense_setOfPred_
preimage_smul_eq (hsm : NullMeasurableSet s μ) (hd : Dense {g : M | (g • ·) ⁻¹' 
s = s}) : EventuallyConst s (ae μ…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsTopologicalTorsor.toContinuousSMul`：∀ {V : Type u_1} {inst : Group V} 
{inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : Torsor V P}   {inst_3 : T
opologicalSpace P} [self :…
· 使用定理 `instIsTopologicalTorsor`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Top
ologicalSpace G] [IsTopologicalGroup G], IsTopologicalTorsor G
· 使用定理 `instErgodicSMulOfIsMulLeftInvariant`：∀ {G : Type u_1} [inst : Group G] [
inst_1 : MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]   {μ : MeasureT
heory.Measure G} [Measure…
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_iterate_eq`：preimage_iterate_eq {f : α -> α} {n : Nat} : Se
t.preimage f^[n] = (Set.preimage f)^[n]
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `iterate_map_mul`：iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [
MulHomClass F M M] (f : F) (n : Nat) (x y : M) : f^[n] (x * y) = f^[n] x * f^[n]
 y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.mem_one`：mem_one : a in (1 : Set α) ↔ a = 1
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
（共 32 条，此处仅展示前 30 条）
-/
theorem preErgodic_of_dense_iUnion_preimage_one
    {μ : Measure G} [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMulLeftInvariant]
    (f : G →* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) : PreErgodic f μ := by
  refine ⟨fun s hsm hs ↦
    aeconst_of_dense_setOfPred_preimage_smul_eq (M := G) hsm.nullMeasurableSet ?_⟩
  refine hf.mono <| iUnion_subset fun n x hx ↦ ?_
  have hsn : f^[n] ⁻¹' s = s := by
    rw [preimage_iterate_eq, iterate_fixed hs]
  rw [mem_preimage, Set.mem_one] at hx
  rw [mem_ofPred, ← hsn]
  ext y
  simp [hx]

/-- Let `f : G →* G` be a continuous surjective group endomorphism
of a compact topological group with second countable topology.
If the preimages of `1` under the iterations of `f` are dense,
then `f` is ergodic with respect to any finite inner regular left invariant measure. -/
@[to_additive /-- Let `f : G →+ G` be a continuous surjective additive group endomorphism
of a compact topological additive group with second countable topology.
If the preimages of `0` under the iterations of `f` are dense,
then `f` is ergodic with respect to any finite inner regular left invariant measure. -/]
/-
**MonoidHom.ergodic_of_dense_iUnion_preimage_one** 是 Mathlib 中的一个定理，位于命名空间 `Mono
idHom`。
形式化陈述：ergodic_of_dense_iUnion_preimage_one [CompactSpace G] {μ : Measure G} [μ.I
sHaarMeasure] (f : G ->* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) (hcont : Continuous 
f) (hsurj : Surjective f) : Ergodic f μ
参数：f : G ->* G；hf : Dense (⋃ n, f^[n] ⁻¹' 1)；hcont : Continuous f；hsurj : Surjec
tive f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.measurePreserving`：∀ {G : Type u_1} [inst : TopologicalSpace G
] [inst_1 : Group G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]   [Bore
lSpace G] {H : Ty…
· 使用定理 `MonoidHom.preErgodic_of_dense_iUnion_preimage_one`：preErgodic_of_dense_i
Union_preimage_one {μ : Measure G} [IsFiniteMeasure μ] [μ.InnerRegular] [μ.IsMul
LeftInvariant] (f : G ->* G) (hf : Dens…
· 使用定理 `MeasureTheory.CompactSpace.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α] [Compact
Space α]   [MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfIsHaarMeasureOfCompactSpace`：∀ {
G : Type u_1} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup
 G] [inst_3 : MeasurableSpace G]   [BorelSpace G] [Compac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
theorem ergodic_of_dense_iUnion_preimage_one [CompactSpace G] {μ : Measure G} [μ.IsHaarMeasure]
    (f : G →* G) (hf : Dense (⋃ n, f^[n] ⁻¹' 1)) (hcont : Continuous f) (hsurj : Surjective f) :
    Ergodic f μ :=
  ⟨f.measurePreserving hcont hsurj rfl, f.preErgodic_of_dense_iUnion_preimage_one hf⟩

end MonoidHom

