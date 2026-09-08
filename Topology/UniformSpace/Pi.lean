/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Indexed product of uniform spaces
-/

public section


noncomputable section

open scoped Uniformity Topology
open Filter UniformSpace Function Set

universe u

variable {ι ι' β : Type*} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)] [UniformSpace β]

/-
**Pi.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.uniformSpace : UniformSpace (forall i, α i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.uniformSpace : UniformSpace (∀ i, α i) :=
  UniformSpace.ofCoreEq (⨅ i, UniformSpace.comap (eval i) (U i)).toCore
      Pi.topologicalSpace <|
    Eq.symm toTopologicalSpace_iInf
/-
**Pi.uniformSpace_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, UniformSpace.comap (eval i) 
(U i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.ext`：∀ {α : Type ua} {u₁ u₂ : UniformSpace α}, uniformity α
 = uniformity α → u₁ = u₂
-/
lemma Pi.uniformSpace_eq :
    Pi.uniformSpace α = ⨅ i, UniformSpace.comap (eval i) (U i) := by
  ext : 1; rfl
/-
**Pi.uniformity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i
, a.2 i)) (𝓤 (α i))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
-/
theorem Pi.uniformity :
    𝓤 (∀ i, α i) = ⨅ i : ι, (Filter.comap fun a => (a.1 i, a.2 i)) (𝓤 (α i)) :=
  iInf_uniformity

variable {α}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Countable ι] [∀ i, IsCountablyGenerated (𝓤 (α i))] :
    IsCountablyGenerated (𝓤 (∀ i, α i)) := by
  rw [Pi.uniformity]
  infer_instance
/-
**uniformContinuous_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_pi {β : Type*} [UniformSpace β] {f : β -> forall i, α i}
 : UniformContinuous f ↔ forall i, UniformContinuous fun x => f x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.uniformity`：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.coma
p fun a => (a.1 i, a.2 i)) (𝓤 (α i))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem uniformContinuous_pi {β : Type*} [UniformSpace β] {f : β → ∀ i, α i} :
    UniformContinuous f ↔ ∀ i, UniformContinuous fun x => f x i := by
  simp only [UniformContinuous, Pi.uniformity, tendsto_iInf, tendsto_comap_iff, Function.comp_def]

variable (α)
/-
**Pi.uniformContinuous_proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : forall i : ι
, α i => a i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem Pi.uniformContinuous_proj (i : ι) : UniformContinuous fun a : ∀ i : ι, α i => a i :=
  uniformContinuous_pi.1 uniformContinuous_id i
/-
**Pi.uniformContinuous_precomp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_precomp' (φ : ι' -> ι) : UniformContinuous (fun (f : 
(forall i, α i)) (j : ι') => f (φ j))
参数：φ : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `Pi.uniformContinuous_proj`：Pi.uniformContinuous_proj (i : ι) : UniformCo
ntinuous fun a : forall i : ι, α i => a i
-/
theorem Pi.uniformContinuous_precomp' (φ : ι' → ι) :
    UniformContinuous (fun (f : (∀ i, α i)) (j : ι') ↦ f (φ j)) :=
  uniformContinuous_pi.mpr fun j ↦ uniformContinuous_proj α (φ j)
/-
**Pi.uniformContinuous_precomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_precomp (φ : ι' -> ι) : UniformContinuous (· ∘ φ : (ι
 -> β) -> (ι' -> β))
参数：φ : ι' -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.uniformContinuous_precomp'`：Pi.uniformContinuous_precomp' (φ : ι' -> 
ι) : UniformContinuous (fun (f : (forall i, α i)) (j : ι') => f (φ j))
-/
theorem Pi.uniformContinuous_precomp (φ : ι' → ι) :
    UniformContinuous (· ∘ φ : (ι → β) → (ι' → β)) :=
  Pi.uniformContinuous_precomp' _ φ
/-
**Pi.uniformContinuous_postcomp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_postcomp' {β : ι -> Type*} [forall i, UniformSpace (β
 i)] {g : forall i, α i -> β i} (hg : forall i, UniformContinuous (g i)) : Unifo
rmContinuous (fun (f : (forall i, α i)) (i : ι) => g i (f i))
参数：β i；hg : forall i, UniformContinuous (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuous_pi`：uniformContinuous_pi {β : Type*} [UniformSpace β] 
{f : β -> forall i, α i} : UniformContinuous f ↔ forall i, UniformContinuous fun
 x => f x …
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Pi.uniformContinuous_proj`：Pi.uniformContinuous_proj (i : ι) : UniformCo
ntinuous fun a : forall i : ι, α i => a i
-/
theorem Pi.uniformContinuous_postcomp' {β : ι → Type*} [∀ i, UniformSpace (β i)]
    {g : ∀ i, α i → β i} (hg : ∀ i, UniformContinuous (g i)) :
    UniformContinuous (fun (f : (∀ i, α i)) (i : ι) ↦ g i (f i)) :=
  uniformContinuous_pi.mpr fun i ↦ (hg i).comp <| uniformContinuous_proj α i
/-
**Pi.uniformContinuous_postcomp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_postcomp {α : Type*} [UniformSpace α] {g : α -> β} (h
g : UniformContinuous g) : UniformContinuous (g ∘ · : (ι -> α) -> (ι -> β))
参数：hg : UniformContinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.uniformContinuous_postcomp'`：Pi.uniformContinuous_postcomp' {β : ι ->
 Type*} [forall i, UniformSpace (β i)] {g : forall i, α i -> β i} (hg : forall i
, UniformContinuous …
-/
theorem Pi.uniformContinuous_postcomp {α : Type*} [UniformSpace α] {g : α → β}
    (hg : UniformContinuous g) : UniformContinuous (g ∘ · : (ι → α) → (ι → β)) :=
  Pi.uniformContinuous_postcomp' _ fun _ ↦ hg
/-
**Pi.uniformSpace_comap_precomp'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformSpace_comap_precomp' (φ : ι' -> ι) : UniformSpace.comap (fun g i
' => g (φ i')) (Pi.uniformSpace (fun i' => α (φ i'))) = ⨅ i', UniformSpace.comap
 (eval (φ i')) (U (φ i'))
参数：φ : ι' -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)
· 使用定理 `UniformSpace.comap_iInf`：UniformSpace.comap_iInf {ι α γ} {u : ι -> Unifo
rmSpace γ} {f : α -> γ} : (⨅ i, u i).comap f = ⨅ i, (u i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.uniformSpace_comap_precomp' (φ : ι' → ι) :
    UniformSpace.comap (fun g i' ↦ g (φ i')) (Pi.uniformSpace (fun i' ↦ α (φ i'))) =
    ⨅ i', UniformSpace.comap (eval (φ i')) (U (φ i')) := by
  simp [Pi.uniformSpace_eq, UniformSpace.comap_iInf, ← UniformSpace.comap_comap, comp_def]
/-
**Pi.uniformSpace_comap_precomp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformSpace_comap_precomp (φ : ι' -> ι) : UniformSpace.comap (· ∘ φ) (
Pi.uniformSpace (fun _ => β)) = ⨅ i', UniformSpace.comap (eval (φ i')) ‹UniformS
pace β›
参数：φ : ι' -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Pi.uniformSpace_comap_precomp'`：Pi.uniformSpace_comap_precomp' (φ : ι' -
> ι) : UniformSpace.comap (fun g i' => g (φ i')) (Pi.uniformSpace (fun i' => α (
φ i'))) = ⨅ i', Unif…
-/
lemma Pi.uniformSpace_comap_precomp (φ : ι' → ι) :
    UniformSpace.comap (· ∘ φ) (Pi.uniformSpace (fun _ ↦ β)) =
    ⨅ i', UniformSpace.comap (eval (φ i')) ‹UniformSpace β› :=
  uniformSpace_comap_precomp' (fun _ ↦ β) φ
/-
**Pi.uniformContinuous_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformContinuous_restrict (S : Set ι) : UniformContinuous (S.domRestri
ct : (forall i : ι, α i) -> (forall i : S, α i))
参数：S : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.uniformContinuous_precomp'`：Pi.uniformContinuous_precomp' (φ : ι' -> 
ι) : UniformContinuous (fun (f : (forall i, α i)) (j : ι') => f (φ j))
-/
lemma Pi.uniformContinuous_restrict (S : Set ι) :
    UniformContinuous (S.domRestrict : (∀ i : ι, α i) → (∀ i : S, α i)) :=
  Pi.uniformContinuous_precomp' _ ((↑) : S → ι)
/-
**Pi.uniformSpace_comap_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformSpace_comap_restrict (S : Set ι) : UniformSpace.comap (S.domRest
rict) (Pi.uniformSpace (fun i : S => α i)) = ⨅ i in S, UniformSpace.comap (eval 
i) (U i)
参数：S : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.uniformSpace_comap_precomp'`：Pi.uniformSpace_comap_precomp' (φ : ι' -
> ι) : UniformSpace.comap (fun g i' => g (φ i')) (Pi.uniformSpace (fun i' => α (
φ i'))) = ⨅ i', Unif…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.uniformSpace_comap_restrict (S : Set ι) :
    UniformSpace.comap (S.domRestrict) (Pi.uniformSpace (fun i : S ↦ α i)) =
    ⨅ i ∈ S, UniformSpace.comap (eval i) (U i) := by
  simp +unfoldPartialApp
    [← iInf_subtype'', ← uniformSpace_comap_precomp' _ ((↑) : S → ι), Set.domRestrict]
/-
**cauchy_pi_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_pi_iff [Nonempty ι] {l : Filter (forall i, α i)} : Cauchy l ↔ foral
l i, Cauchy (map (eval i) l)
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cauchy_pi_iff [Nonempty ι] {l : Filter (∀ i, α i)} :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace, cauchy_comap_uniformSpace]
/-
**cauchy_pi_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cauchy_pi_iff' {l : Filter (forall i, α i)} [l.NeBot] : Cauchy l ↔ forall 
i, Cauchy (map (eval i) l)
参数：forall i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cauchy_pi_iff' {l : Filter (∀ i, α i)} [l.NeBot] :
    Cauchy l ↔ ∀ i, Cauchy (map (eval i) l) := by
  simp_rw +instances [Pi.uniformSpace_eq, cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace]
/-
**Cauchy.pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Cauchy.pi [Nonempty ι] {l : forall i, Filter (α i)} (hl : forall i, Cauchy
 (l i)) : Cauchy (Filter.pi l)
参数：α i；hl : forall i, Cauchy (l i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_eval_pi`：map_eval_pi (f : forall i, Filter (α i)) [forall i, 
NeBot (f i)] (i : ι) : map (eval i) (pi f) = f i
-/
lemma Cauchy.pi [Nonempty ι] {l : ∀ i, Filter (α i)} (hl : ∀ i, Cauchy (l i)) :
    Cauchy (Filter.pi l) := by
  have := fun i ↦ (hl i).1
  simpa [cauchy_pi_iff]
/-
**Pi.complete** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.complete [forall i, CompleteSpace (α i)] : CompleteSpace (forall i, α i
) where complete {f} hf
参数：α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_pi`：nhds_pi {a : forall i, A i} : 𝓝 a = pi fun i => 𝓝 (a i)
· 使用定理 `Filter.le_pi`：le_pi {g : Filter (forall i, α i)} : g <= pi f ↔ forall i,
 Tendsto (eval i) g (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance Pi.complete [∀ i, CompleteSpace (α i)] : CompleteSpace (∀ i, α i) where
  complete {f} hf := by
    have := hf.1
    simp_rw [cauchy_pi_iff', cauchy_iff_exists_le_nhds] at hf
    choose x hx using hf
    use x
    rwa [nhds_pi, le_pi]
/-
**Pi.uniformSpace_comap_restrict_sUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.uniformSpace_comap_restrict_sUnion (𝔖 : Set (Set ι)) : UniformSpace.com
ap (⋃₀ 𝔖).domRestrict (Pi.uniformSpace (fun i : (⋃₀ 𝔖) => α i)) = ⨅ S in 𝔖, Unif
ormSpace.comap S.domRestrict (Pi.uniformSpace (fun i : S => α i))
参数：𝔖 : Set (Set ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_comap_restrict`：Pi.uniformSpace_comap_restrict (S : Set 
ι) : UniformSpace.comap (S.domRestrict) (Pi.uniformSpace (fun i : S => α i)) = ⨅
 i in S, UniformSpac…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iInf_sUnion`：iInf_sUnion (S : Set (Set α)) (f : α -> β) : (⨅ x in ⋃₀ S, 
f x) = ⨅ (s in S) (x in s), f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.uniformSpace_comap_restrict_sUnion (𝔖 : Set (Set ι)) :
    UniformSpace.comap (⋃₀ 𝔖).domRestrict (Pi.uniformSpace (fun i : (⋃₀ 𝔖) ↦ α i)) =
    ⨅ S ∈ 𝔖, UniformSpace.comap S.domRestrict (Pi.uniformSpace (fun i : S ↦ α i)) := by
  simp_rw [Pi.uniformSpace_comap_restrict α, iInf_sUnion]

/-- An infimum of complete uniformities is complete,
as long as the whole family is bounded by some common T2 topology. -/
/-
**CompleteSpace.iInf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSpace`。
形式化陈述：∀ {ι : Type u_4} {X : Type u_5} {u : ι → UniformSpace X},   (∀ (i : ι), Co
mpleteSpace X) → (∃ t, T2Space X ∧ ∀ (i : ι), (u i).toTopologicalSpace ≤ t) → Co
mpleteSpace X
参数：∀ (i : ι), CompleteSpace X；∃ t, T2Space X ∧ ∀ (i : ι), (u i).toTopologicalSpa
ce ≤ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.uniformity`：Pi.uniformity : 𝓤 (forall i, α i) = ⨅ i : ι, (Filter.coma
p fun a => (a.1 i, a.2 i)) (𝓤 (α i))
· 使用定理 `Filter.comap_iInf`：comap_iInf {f : ι -> Filter β} : comap m (⨅ i, f i) =
 ⨅ i, comap m (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_id'`：comap_id' : comap (fun x => x) f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `completeSpace_iff_isComplete_range`：completeSpace_iff_isComplete_range {
f : α -> β} (hf : IsUniformInducing f) : CompleteSpace α ↔ IsComplete (range f)
· 使用定理 `Set.range_const_eq_diagonal`：range_const_eq_diagonal {α β : Type*} [hβ :
 Nonempty β] : range (const α) = {f : α -> β | forall x y, f x = f y}
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `induced_mono`：induced_mono (h : t₁ <= t₂) : t₁.induced g <= t₂.induced g
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
An infimum of complete uniformities is complete,
as long as the whole family is bounded by some common T2 topology.
-/
protected theorem CompleteSpace.iInf {ι X : Type*} {u : ι → UniformSpace X}
    (hu : ∀ i, @CompleteSpace X (u i))
    (ht : ∃ t, @T2Space X t ∧ ∀ i, (u i).toTopologicalSpace ≤ t) :
    @CompleteSpace X (⨅ i, u i) := by
  -- We can assume `X` is nonempty.
  nontriviality X
  rcases ht with ⟨t, ht, hut⟩
  -- The diagonal map `(X, ⨅ i, u i) → ∀ i, (X, u i)` is a uniform embedding.
  have : @IsUniformInducing X (ι → X) (⨅ i, u i) (Pi.uniformSpace (U := u)) (const ι) := by
    simp_rw [isUniformInducing_iff, iInf_uniformity, Pi.uniformity, Filter.comap_iInf,
      Filter.comap_comap, comp_def, const, Prod.eta, comap_id']
  -- Hence, it suffices to show that its range, the diagonal, is closed in `Π i, (X, u i)`.
  simp_rw [@completeSpace_iff_isComplete_range _ _ (_) (_) _ this, range_const_eq_diagonal,
    ofPred_forall]
  -- The separation of `t` ensures that this is the case in `Π i, (X, t)`, hence the result
  -- since the topology associated to each `u i` is finer than `t`.
  have : Pi.topologicalSpace (t₂ := fun i ↦ (u i).toTopologicalSpace) ≤
         Pi.topologicalSpace (t₂ := fun _ ↦ t) :=
    iInf_mono fun i ↦ induced_mono <| hut i
  refine IsClosed.isComplete <| .mono ?_ this
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    isClosed_eq (continuous_apply _) (continuous_apply _)
