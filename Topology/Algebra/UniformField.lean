/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.Field` and
`UniformSpace.Completion.IsTopologicalDivisionRing`.
-/

@[expose] public section

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

/-- A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
/-
**CompletableTopField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → [Field K] → [UniformSpace K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform
 structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.
-/
class CompletableTopField : Prop extends T0Space K where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ → Cauchy (map (fun x => x⁻¹) F)

namespace UniformSpace

namespace Completion

/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [T0Space K] : Nontrivial (hat K) :=
  (isUniformEmbedding_coe K).injective.nontrivial

variable {K}

/-- extension of inversion to the completion of a field. -/
/-
**UniformSpace.Completion.hatInv** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.Complet
ion`。
形式化陈述：hatInv : hat K -> hat K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)

--- 原说明 ---
extension of inversion to the completion of a field.
-/
def hatInv : hat K → hat K :=
  isDenseInducing_coe.extend fun x : K => (↑x⁻¹ : hat K)

@[fun_prop]
/-
**UniformSpace.Completion.continuous_hatInv** 是 Mathlib 中的一个定理，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：continuous_hatInv [CompletableTopField K] {x : hat K} (h : x != 0) : Conti
nuousAt hatInv x
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.continuousAt_extend`：continuousAt_extend [T3Space γ] {b 
: β} {f : α -> γ} (di : IsDenseInducing i) (hf : forallᶠ x in 𝓝 b, exists c, Ten
dsto f (comap i <| 𝓝 x) (…
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `compl_singleton_mem_nhds`：compl_singleton_mem_nhds [T1Space X] {x y : X}
 (h : y != x) : {x}ᶜ in 𝓝 y
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Cauchy.map`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α] 
[inst : UniformSpace β] {f : Filter α} {m : α → β},   Cauchy f → UniformContinuo
…
· 使用定理 `CompletableTopField.nice`：∀ {K : Type u_1} {inst : Field K} {inst_1 : Un
iformSpace K} [self : CompletableTopField K] (F : Filter K),   Cauchy F → nhds 0
 ⊓ F = ⊥ → Cau…
· 使用定理 `IsDenseInducing.comap_nhds_neBot`：comap_nhds_neBot (di : IsDenseInducing
 i) (b : β) : NeBot (comap i (𝓝 b))
· 使用定理 `Cauchy.comap`：∀ {α : Type u} {β : Type v} [uniformSpace : UniformSpace α
] [inst : UniformSpace β] {f : Filter β} {m : α → β},   Cauchy f →     Filter.co
ma…
· 使用定理 `cauchy_nhds`：cauchy_nhds {a : α} : Cauchy (𝓝 a)
· 使用定理 `UniformSpace.Completion.comap_coe_eq_uniformity`：comap_coe_eq_uniformity
 : ((𝓤 _).comap fun p : α × α => ((p.1 : Completion α), (p.2 : Completion α))) =
 𝓤 α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `eq_of_nhds_neBot`：eq_of_nhds_neBot [T2Space X] {x y : X} (h : NeBot (𝓝 x
 ⊓ 𝓝 y)) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 34 条，此处仅展示前 30 条）
-/
theorem continuous_hatInv [CompletableTopField K] {x : hat K} (h : x ≠ 0) :
    ContinuousAt hatInv x := by
  refine isDenseInducing_coe.continuousAt_extend ?_
  apply mem_of_superset (compl_singleton_mem_nhds h)
  intro y y_ne
  rw [mem_compl_singleton_iff] at y_ne
  apply CompleteSpace.complete
  have : (fun (x : K) => (↑x⁻¹ : hat K)) =
      ((fun (y : K) => (↑y : hat K)) ∘ (fun (x : K) => (x⁻¹ : K))) := by
    simp [Function.comp_def]
  rw [this, ← Filter.map_map]
  apply Cauchy.map _ (Completion.uniformContinuous_coe K)
  apply CompletableTopField.nice
  · have := isDenseInducing_coe.comap_nhds_neBot y
    apply cauchy_nhds.comap
    rw [Completion.comap_coe_eq_uniformity]
  · have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 y = ⊥ := by
      by_contra h
      exact y_ne (eq_of_nhds_neBot <| neBot_iff.mpr h).symm
    rw [isDenseInducing_coe.nhds_eq_comap (0 : K), ← Filter.comap_inf]
    norm_cast
    rw [eq_bot]
    exact comap_bot

open scoped Classical in
/--
The value of `hat_inv` at zero is not really specified, although it's probably zero.
Here we explicitly enforce the `inv_zero` axiom.
-/
/-
**UniformSpace.Completion.instInvCompletion** 是 Mathlib 中的一个实例，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：instInvCompletion : Inv (hat K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value of `hat_inv` at zero is not really specified, although it's probably z
ero.
Here we explicitly enforce the `inv_zero` axiom.
-/
instance instInvCompletion : Inv (hat K) :=
  ⟨fun x => if x = 0 then 0 else hatInv x⟩

variable [IsTopologicalDivisionRing K]
/-
**UniformSpace.Completion.hatInv_extends** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace
.Completion`。
形式化陈述：hatInv_extends {x : K} (h : x != 0) : hatInv (x : hat K) = ↑(x⁻¹ : K)
参数：h : x != 0。
该定理/引理给出了一组等式。
继承自：{x : K} (h : x != 0) : hatInv (x : hat K) = ↑(x⁻¹ : K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_at`：extend_eq_at [T2Space γ] (di : IsDenseIndu
cing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
· 使用定理 `ContinuousInv₀.continuousAt_inv₀`：∀ {G₀ : Type u_4} {inst : Zero G₀} {in
st_1 : Inv G₀} {inst_2 : TopologicalSpace G₀} [self : ContinuousInv₀ G₀] ⦃x : G₀
⦄,   x ≠ 0 → Continuou…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
-/
theorem hatInv_extends {x : K} (h : x ≠ 0) : hatInv (x : hat K) = ↑(x⁻¹ : K) :=
  isDenseInducing_coe.extend_eq_at ((continuous_coe K).continuousAt.comp (continuousAt_inv₀ h))

variable [CompletableTopField K]

@[norm_cast]
/-
**UniformSpace.Completion.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `IsDenseEmbedding.injective`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {e : α → β},   IsDenseEmbedding e 
→ Function.Injec…
· 使用定理 `UniformSpace.Completion.isDenseEmbedding_coe`：isDenseEmbedding_coe [T0Sp
ace α] : IsDenseEmbedding ((↑) : α -> Completion α)
· 使用定理 `CompletableTopField.toT0Space`：∀ {K : Type u_1} {inst : Field K} {inst_1
 : UniformSpace K} [self : CompletableTopField K], T0Space K
· 使用定理 `UniformSpace.Completion.hatInv_extends`：hatInv_extends {x : K} (h : x !=
 0) : hatInv (x : hat K) = ↑(x⁻¹ : K)
-/
theorem coe_inv (x : K) : (x : hat K)⁻¹ = ((x⁻¹ : K) : hat K) := by
  by_cases h : x = 0
  · rw [h, inv_zero]
    dsimp [Inv.inv]
    norm_cast
    simp
  · conv_lhs => dsimp [Inv.inv]
    rw [if_neg]
    · exact hatInv_extends h
    · exact fun H => h (isDenseEmbedding_coe.injective H)

variable [IsUniformAddGroup K]
/-
**UniformSpace.Completion.mul_hatInv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：mul_hatInv_cancel {x : hat K} (x_ne : x != 0) : x * hatInv x = 1
参数：x_ne : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousAt.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `UniformSpace.Completion.instContinuousMul`：∀ {α : Type u_1} [inst : Ring
 α] [inst_1 : UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α],   Con
tinuousMul (UniformSpace.Comple…
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `UniformSpace.Completion.continuous_hatInv`：continuous_hatInv [Completabl
eTopField K] {x : hat K} (h : x != 0) : ContinuousAt hatInv x
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `mem_closure_of_mem_closure_union`：mem_closure_of_mem_closure_union (h : 
x in closure (s₁ union s₂)) (h₁ : s₁ᶜ in 𝓝 x) : x in closure s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `compl_singleton_mem_nhds`：compl_singleton_mem_nhds [T1Space X] {x y : X}
 (h : y != x) : {x}ᶜ in 𝓝 y
· 使用定理 `mem_closure_image`：mem_closure_image (hf : ContinuousAt f x) (hx : x in 
closure s) : f x in closure (f '' s)
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `UniformSpace.Completion.hatInv_extends`：hatInv_extends {x : K} (h : x !=
 0) : hatInv (x : hat K) = ↑(x⁻¹ : K)
· 使用引理 `Set.mem_compl_singleton_iff`：mem_compl_singleton_iff : a in ({b} : Set α
)ᶜ ↔ a != b
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `UniformSpace.Completion.coe_one`：coe_one : ((1 : α) : Completion α) = 1
（共 32 条，此处仅展示前 30 条）
-/
theorem mul_hatInv_cancel {x : hat K} (x_ne : x ≠ 0) : x * hatInv x = 1 := by
  have : T1Space (hat K) := T2Space.t1Space
  let f := fun x : hat K => x * hatInv x
  let c := (fun (x : K) => (x : hat K))
  change f x = 1
  have cont : ContinuousAt f x := by fun_prop
  have clo : x ∈ closure (c '' {0}ᶜ) := by
    have := isDenseInducing_coe.dense x
    rw [← image_univ, show (univ : Set K) = {0} ∪ {0}ᶜ from (union_compl_self _).symm,
      image_union] at this
    apply mem_closure_of_mem_closure_union this
    rw [image_singleton]
    exact compl_singleton_mem_nhds x_ne
  have fxclo : f x ∈ closure (f '' c '' {0}ᶜ) := mem_closure_image cont clo
  have : f '' c '' {0}ᶜ ⊆ {1} := by
    rw [image_image]
    rintro _ ⟨z, z_ne, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_compl_singleton_iff] at z_ne
    dsimp [f]
    rw [hatInv_extends z_ne, ← coe_mul]
    rw [mul_inv_cancel₀ z_ne, coe_one]
  replace fxclo := closure_mono this fxclo
  rwa [closure_singleton, mem_singleton_iff] at fxclo
/-
**UniformSpace.Completion.instField** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Comp
letion`。
形式化陈述：instField : Field (hat K) where mul_inv_cancel
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField : Field (hat K) where
  mul_inv_cancel := fun x x_ne => by simp only [Inv.inv, if_neg x_ne, mul_hatInv_cancel x_ne]
  inv_zero := by simp only [Inv.inv, ite_true]
  -- TODO: use a better defeq
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with
    continuousAt_inv₀ := by
      intro x x_ne
      have : { y | hatInv y = y⁻¹ } ∈ 𝓝 x :=
        haveI : {(0 : hat K)}ᶜ ⊆ { y : hat K | hatInv y = y⁻¹ } := by
          intro y y_ne
          rw [mem_compl_singleton_iff] at y_ne
          dsimp [Inv.inv]
          rw [if_neg y_ne]
        mem_of_superset (compl_singleton_mem_nhds x_ne) this
      exact ContinuousAt.congr (continuous_hatInv x_ne) this }

end Completion

end UniformSpace

variable (L : Type*) [Field L] [UniformSpace L] [CompletableTopField L]

/-
**Subfield.completableTopField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subfield.completableTopField (K : Subfield L) : CompletableTopField K wher
e nice F F_cau inf_F
参数：K : Subfield L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletableTopField.toT0Space`：∀ {K : Type u_1} {inst : Field K} {inst_1
 : UniformSpace K} [self : CompletableTopField K], T0Space K
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `isUniformEmbedding_subtype_val`：isUniformEmbedding_subtype_val {p : α ->
 Prop} : IsUniformEmbedding (Subtype.val : Subtype p -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.cauchy_map_iff`：IsUniformInducing.cauchy_map_iff {f : 
α -> β} (hf : IsUniformInducing f) {F : Filter α} : Cauchy (map f F) ↔ Cauchy F
· 使用定理 `Filter.map_comm`：map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) : map ψ (ma
p φ F) = map ρ (map θ F)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CompletableTopField.nice`：∀ {K : Type u_1} {inst : Field K} {inst_1 : Un
iformSpace K} [self : CompletableTopField K] (F : Filter K),   Cauchy F → nhds 0
 ⊓ F = ⊥ → Cau…
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
-/
instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K where
  nice F F_cau inf_F := by
    let i : K →+* L := K.subtype
    have hi : IsUniformInducing i := isUniformEmbedding_subtype_val.isUniformInducing
    rw [← hi.cauchy_map_iff] at F_cau ⊢
    rw [map_comm (show (i ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ i by ext; rfl)]
    apply CompletableTopField.nice _ F_cau
    rw [← Filter.push_pull', ← map_zero i, ← hi.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) completableTopField_of_complete (L : Type*) [Field L] [UniformSpace L]
    [IsTopologicalDivisionRing L] [T0Space L] [CompleteSpace L] : CompletableTopField L where
  nice F cau_F hF := by
    have : NeBot F := cau_F.1
    rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
    have hx' : x ≠ 0 := by
      rintro rfl
      rw [inf_eq_right.mpr hx] at hF
      exact cau_F.1.ne hF
    exact Filter.Tendsto.cauchy_map <|
      calc
        map (fun x => x⁻¹) F ≤ map (fun x => x⁻¹) (𝓝 x) := map_mono hx
        _ ≤ 𝓝 x⁻¹ := continuousAt_inv₀ hx'

variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

/-- The pullback of a completable topological field along a uniform inducing
ring homomorphism is a completable topological field. -/
/-
**IsUniformInducing.completableTopField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.completableTopField [UniformSpace α] [T0Space α] {f : α 
->+* β} (hf : IsUniformInducing f) : CompletableTopField α
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.cauchy_map_iff`：IsUniformInducing.cauchy_map_iff {f : 
α -> β} (hf : IsUniformInducing f) {F : Filter α} : Cauchy (map f F) ↔ Cauchy F
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.map_comm`：map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) : map ψ (ma
p φ F) = map ρ (map θ F)
· 使用定理 `CompletableTopField.nice`：∀ {K : Type u_1} {inst : Field K} {inst_1 : Un
iformSpace K} [self : CompletableTopField K] (F : Filter K),   Cauchy F → nhds 0
 ⊓ F = ⊥ → Cau…
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥

--- 原说明 ---
The pullback of a completable topological field along a uniform inducing
ring homomorphism is a completable topological field.
-/
theorem IsUniformInducing.completableTopField
    [UniformSpace α] [T0Space α]
    {f : α →+* β} (hf : IsUniformInducing f) :
    CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  rw [← IsUniformInducing.cauchy_map_iff hf] at F_cau ⊢
  have h_comm : (f ∘ fun x => x⁻¹) = (fun x => x⁻¹) ∘ f := by
    ext; simp only [Function.comp_apply, map_inv₀]
  rw [Filter.map_comm h_comm]
  apply CompletableTopField.nice _ F_cau
  rw [← Filter.push_pull', ← map_zero f, ← hf.isInducing.nhds_eq_comap, inf_F, Filter.map_bot]
