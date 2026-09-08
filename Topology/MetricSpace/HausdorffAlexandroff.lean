/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.Instances.CantorSet
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Hausdorff–Alexandroff Theorem

In this file, we prove the Hausdorff–Alexandroff theorem, which states that every
nonempty compact metric space is a continuous image of the Cantor set.

## Main theorems

* `exists_nat_bool_continuous_surjective_of_compact`: Hausdorff–Alexandroff Theorem.

## Proof Outline

First, note that the Cantor set is homeomorphic to `ℕ → Bool`, as shown in
`cantorSetHomeomorphNatToBool`. Therefore, in this file, we work only with the space
`ℕ → Bool` and refer to it as the "Cantor space".

The proof consists of three steps. Let `X` be a compact metric space.

1. Every compact metric space is homeomorphic to a closed subset of the Hilbert cube.
   This is already proved in `exists_closed_embedding_to_hilbert_cube`. Using this result,
   we may assume that `X` is a closed subset of the Hilbert cube.
2. We construct a continuous surjection `cantorToHilbert` from the Cantor space to the Hilbert
   cube.
3. Taking the preimage of `X` under this surjection, it remains to prove that any closed
   subset of the Cantor space is the continuous image of the Cantor space.
-/

@[expose] public section

namespace Real

/-- Convert a sequence of binary digits to a real number from `unitInterval`. -/
/-
**Real.fromBinary** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：fromBinary : (Nat -> Bool) -> unitInterval
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool

--- 原说明 ---
Convert a sequence of binary digits to a real number from `unitInterval`.
-/
noncomputable def fromBinary : (ℕ → Bool) → unitInterval :=
  let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
    (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
  Subtype.coind (ofDigits ∘ φ) (fun _ ↦ ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)
/-
**Real.fromBinary_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fromBinary_continuous : Continuous fromBinary
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Real.continuous_ofDigits`：continuous_ofDigits {b : Nat} : Continuous (@o
fDigits b)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem fromBinary_continuous : Continuous fromBinary :=
  Continuous.subtype_mk (continuous_ofDigits.comp' (Homeomorph.continuous _)) _
/-
**Real.fromBinary_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fromBinary_surjective : fromBinary.Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coind_surjective`：∀ {α : Type u_7} {β : Type u_8} {f : α → β} {p
 : Set β} (h : ∀ (a : α), f a ∈ p),   Set.SurjOn f Set.univ p → Function.Surject
ive (Subtype.c…
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `Set.SurjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.SurjOn g t p → Set.Su
rjOn …
· 使用定理 `Real.ofDigits_SurjOn`：ofDigits_SurjOn {b : Nat} (hb : 1 < b) : Set.SurjO
n (ofDigits (b
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
theorem fromBinary_surjective : fromBinary.Surjective := by
  refine Subtype.coind_surjective _ ((ofDigits_SurjOn (by norm_num)).comp ?_)
  simp only [Set.surjOn_univ, Homeomorph.surjective _]

end Real

open Real

/-- A continuous surjection from the Cantor space to the Hilbert cube. -/
/-
**cantorToHilbert** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cantorToHilbert (x : Nat -> Bool) : Nat -> unitInterval
参数：x : Nat -> Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous surjection from the Cantor space to the Hilbert cube.
-/
noncomputable def cantorToHilbert (x : ℕ → Bool) : ℕ → unitInterval :=
  Pi.map (fun _ b ↦ fromBinary b) (cantorSpaceHomeomorphNatToCantorSpace x)
/-
**cantorToHilbert_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorToHilbert_continuous : Continuous cantorToHilbert
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Real.fromBinary_continuous`：fromBinary_continuous : Continuous fromBinar
y
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem cantorToHilbert_continuous : Continuous cantorToHilbert :=
  continuous_pi (fun _ ↦ fromBinary_continuous.comp (by fun_prop))
/-
**cantorToHilbert_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cantorToHilbert_surjective : cantorToHilbert.Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Function.Surjective.piMap`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → 
Sort u_3} {f : (i : ι) → α i → β i},   (∀ (i : ι), Function.Surjective (f i)) → 
Function.Surjec…
· 使用定理 `Real.fromBinary_surjective`：fromBinary_surjective : fromBinary.Surjectiv
e
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
theorem cantorToHilbert_surjective : cantorToHilbert.Surjective :=
  (Function.Surjective.piMap (fun _ ↦ fromBinary_surjective)).comp
    cantorSpaceHomeomorphNatToCantorSpace.surjective

attribute [local instance] PiNat.metricSpace in
/-
**exists_retractionCantorSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_retractionCantorSet {X : Set (Nat -> Bool)} (h_closed : IsClosed X)
 (h_nonempty : X.Nonempty) : exists f : (Nat -> Bool) -> (Nat -> Bool), Continuo
us f ∧ Set.range f = X
参数：Nat -> Bool；h_closed : IsClosed X；h_nonempty : X.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `PiNat.exists_lipschitz_retraction_of_isClosed`：exists_lipschitz_retracti
on_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) : 
exists f : (forall n, E n) -> foral…
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
-/
theorem exists_retractionCantorSet {X : Set (ℕ → Bool)} (h_closed : IsClosed X)
    (h_nonempty : X.Nonempty) : ∃ f : (ℕ → Bool) → (ℕ → Bool), Continuous f ∧ Set.range f = X := by
  obtain ⟨f, fs, frange, hf⟩ := PiNat.exists_lipschitz_retraction_of_isClosed h_closed h_nonempty
  exact ⟨f, hf.continuous, frange⟩

/-- **Hausdorff–Alexandroff theorem**: every nonempty compact metric space is a continuous image
of the Cantor set. -/
/-
**exists_nat_bool_continuous_surjective_of_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nat_bool_continuous_surjective_of_compact (X : Type*) [Nonempty X] 
[MetricSpace X] [CompactSpace X] : exists f : (Nat -> Bool) -> X, Continuous f ∧
 Function.Surjective f
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Metric.PiNatEmbed.exists_embedding_to_hilbert_cube`：exists_embedding_to_
hilbert_cube : exists F : X -> Nat -> I, IsEmbedding F
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `cantorToHilbert_continuous`：cantorToHilbert_continuous : Continuous cant
orToHilbert
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Continuous.isClosedEmbedding`：Continuous.isClosedEmbedding [CompactSpace
 X] [T2Space Y] {f : X -> Y} (h : Continuous f) (hf : Function.Injective f) : Is
ClosedEmbedding f
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `exists_retractionCantorSet`：exists_retractionCantorSet {X : Set (Nat -> 
Bool)} (h_closed : IsClosed X) (h_nonempty : X.Nonempty) : exists f : (Nat -> Bo
ol) -> (Nat -> B…
· 使用定理 `Set.Nonempty.preimage`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.No
nempty → ∀ {f : α → β}, Function.Surjective f → (f ⁻¹' s).Nonempty
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `cantorToHilbert_surjective`：cantorToHilbert_surjective : cantorToHilbert
.Surjective
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.coind_surjective`：∀ {α : Type u_7} {β : Type u_8} {f : α → β} {p
 : Set β} (h : ∀ (a : α), f a ∈ p),   Set.SurjOn f Set.univ p → Function.Surject
ive (Subtype.c…
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用引理 `Set.restrictPreimage_surjective`：restrictPreimage_surjective (hf : Surje
ctive f) : Surjective (t.restrictPreimage f)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
**Hausdorff–Alexandroff theorem**: every nonempty compact metric space is a cont
inuous image
of the Cantor set.
-/
theorem exists_nat_bool_continuous_surjective_of_compact (X : Type*) [Nonempty X] [MetricSpace X]
    [CompactSpace X] : ∃ f : (ℕ → Bool) → X, Continuous f ∧ Function.Surjective f := by
  -- `X` is homeomorphic to a closed subset `KH` of the Hilbert cube.
  let : TopologicalSpace.SeparableSpace X :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨emb, h_emb⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let KH : Set (ℕ → unitInterval) := Set.range emb
  let g : X ≃ₜ KH := h_emb.toHomeomorph
  -- `KC` is the closed preimage of `KH` under the continuous surjection `cantorToHilbert`.
  let KC : Set (ℕ → Bool) := cantorToHilbert ⁻¹' KH
  have hKC_closed : IsClosed KC :=
    IsClosed.preimage cantorToHilbert_continuous (Topology.IsClosedEmbedding.isClosed_range
    <| Continuous.isClosedEmbedding (Topology.IsEmbedding.continuous h_emb) h_emb.injective)
  -- Take a retraction `f'` from the Cantor space to `KC`.
  obtain ⟨f, hf_continuous, hf_surjective⟩ := exists_retractionCantorSet hKC_closed
    <| Set.Nonempty.preimage (Set.range_nonempty emb) cantorToHilbert_surjective
  let f' : (ℕ → Bool) → KC := Subtype.coind f (by simp [← hf_surjective])
  have hf'_surjective : Function.Surjective f' := Subtype.coind_surjective _ (by grind [Set.SurjOn])
  -- Let `h` be the restriction of `cantorToHilbert` to `KC → KH`.
  let h : KC → KH := KH.restrictPreimage cantorToHilbert
  have hh_continuous : Continuous h := Continuous.restrictPreimage cantorToHilbert_continuous
  have hh_surjective : Function.Surjective h :=
    Set.restrictPreimage_surjective _ cantorToHilbert_surjective
  -- Take the composition `g.symm ∘ h ∘ f'` as the desired continuous surjection from the Cantor
  -- space to `X`.
  exact ⟨g.symm ∘ h ∘ f', by fun_prop, g.symm.surjective.comp <| hh_surjective.comp hf'_surjective⟩
