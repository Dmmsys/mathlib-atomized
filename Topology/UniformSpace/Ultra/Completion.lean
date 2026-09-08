/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Ultra.Basic
public import Mathlib.Topology.UniformSpace.Ultra.Constructions

/-!
# Completions of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.completion_iff`: a Hausdorff completion has a nonarchimedean uniformity
  iff the underlying space has a nonarchimedean uniformity.

-/

public section

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]

open Filter Set Topology Uniformity

/-
**IsUniformInducing.isUltraUniformity** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.isUltraUniformity [IsUltraUniformity Y] {f : X -> Y} (hf
 : IsUniformInducing f) : IsUltraUniformity X
参数：hf : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.comap`：IsUltraUniformity.comap {u : UniformSpace Y} (h
 : IsUltraUniformity Y) (f : X -> Y) : @IsUltraUniformity _ (u.comap f)
· 使用定理 `IsUniformInducing.comap_uniformSpace`：∀ {α : Type u} {β : Type v} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 UniformSpace.comap f inst…
-/
lemma IsUniformInducing.isUltraUniformity [IsUltraUniformity Y] {f : X → Y}
    (hf : IsUniformInducing f) : IsUltraUniformity X :=
  hf.comap_uniformSpace ▸ .comap inferInstance f
/-
**CauchyFilter.isSymm_gen** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CauchyFilter.isSymm_gen {s : SetRel X X} [s.IsSymm] : (gen s).IsSymm where
 symm _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `SetRel.mem_filter_prod_comm`：SetRel.mem_filter_prod_comm (R : SetRel α α
) {f g : Filter α} [R.IsSymm] : R in f ×ˢ g ↔ R in g ×ˢ f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance CauchyFilter.isSymm_gen {s : SetRel X X} [s.IsSymm] : (gen s).IsSymm where
  symm _ := by simp [CauchyFilter.gen, s.mem_filter_prod_comm]
/-
**CauchyFilter.isTrans_gen** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CauchyFilter.isTrans_gen {s : SetRel X X} [s.IsTrans] : (gen s).IsTrans wh
ere trans _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTransitiveRel.mem_filter_prod_trans`：IsTransitiveRel.mem_filter_prod_t
rans {s : SetRel X X} {f g h : Filter X} [g.NeBot] [s.IsTrans] (hfg : s in f ×ˢ 
g) (hgh : s in g ×ˢ h) : s …
· 使用定理 `CauchyFilter.instNeBotValFilterCauchy`：∀ {α : Type u} [inst : UniformSpa
ce α] (f : CauchyFilter α), (↑f).NeBot
-/
instance CauchyFilter.isTrans_gen {s : SetRel X X} [s.IsTrans] : (gen s).IsTrans where
  trans _ _ _ := IsTransitiveRel.mem_filter_prod_trans
/-
**IsUltraUniformity.cauchyFilter** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.cauchyFilter [IsUltraUniformity X] : IsUltraUniformity (
CauchyFilter X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `CauchyFilter.basis_uniformity`：basis_uniformity {ι : Sort*} {p : ι -> Pr
op} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s) : (𝓤 (CauchyFilter α)).HasBas
is p (gen ∘ s)
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
-/
instance IsUltraUniformity.cauchyFilter [IsUltraUniformity X] :
    IsUltraUniformity (CauchyFilter X) := by
  apply mk_of_hasBasis (CauchyFilter.basis_uniformity IsUltraUniformity.hasBasis)
  · exact fun _ ⟨_, hU, _⟩ ↦ by simpa using CauchyFilter.isSymm_gen
  · exact fun _ ⟨_, _, hU⟩ ↦ by simpa using CauchyFilter.isTrans_gen
/-
**IsUltraUniformity.cauchyFilter_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUltraUniformit
y`。
形式化陈述：∀ {X : Type u_1} [inst : UniformSpace X], IsUltraUniformity (CauchyFilter 
X) ↔ IsUltraUniformity X
参数：CauchyFilter X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isUltraUniformity`：IsUniformInducing.isUltraUniformity
 [IsUltraUniformity Y] {f : X -> Y} (hf : IsUniformInducing f) : IsUltraUniformi
ty X
· 使用定理 `CauchyFilter.isUniformInducing_pureCauchy`：isUniformInducing_pureCauchy 
: IsUniformInducing (pureCauchy : α -> CauchyFilter α)
-/
@[simp] lemma IsUltraUniformity.cauchyFilter_iff :
    IsUltraUniformity (CauchyFilter X) ↔ IsUltraUniformity X :=
  ⟨fun _ ↦ CauchyFilter.isUniformInducing_pureCauchy.isUltraUniformity,
   fun _ ↦ inferInstance⟩
/-
**IsUltraUniformity.separationQuotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.separationQuotient [IsUltraUniformity X] : IsUltraUnifor
mity (SeparationQuotient X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeparationQuotient.uniformity_eq`：uniformity_eq : 𝓤 (SeparationQuotient 
α) = (𝓤 α).map (Prod.map mk mk)
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.mem_ker`：∀ {α : Type u_2} {f : Filter α} {a : α}, a ∈ f.ker ↔ ∀ s
 ∈ f, a ∈ s
· 使用定理 `inseparable_iff_ker_uniformity`：inseparable_iff_ker_uniformity {x y : α}
 : Inseparable x y ↔ (x, y) in (𝓤 α).ker
· 使用定理 `SeparationQuotient.mk_eq_mk`：mk_eq_mk : mk x = mk y ↔ (x ~ᵢ y)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance IsUltraUniformity.separationQuotient [IsUltraUniformity X] :
    IsUltraUniformity (SeparationQuotient X) := by
  have := IsUltraUniformity.hasBasis.map
    (Prod.map SeparationQuotient.mk (SeparationQuotient.mk (X := X)))
  rw [← SeparationQuotient.uniformity_eq] at this
  apply mk_of_hasBasis this
  · exact fun _ ⟨_, hU, _⟩ ↦ by rw [id_eq]; infer_instance
  · rintro U ⟨hU', _, hU⟩
    constructor
    rintro x y z
    simp only [id_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq,
      forall_exists_index, and_imp]
    rintro a b hab rfl rfl c d hcd hc rfl
    have hbc : (b, c) ∈ U := by
      rw [eq_comm, SeparationQuotient.mk_eq_mk, inseparable_iff_ker_uniformity,
          Filter.mem_ker] at hc
      exact hc _ hU'
    exact ⟨a, d, U.trans (U.trans hab hbc) hcd, by simp, by simp⟩
/-
**IsUltraUniformity.separationQuotient_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUltraUni
formity`。
形式化陈述：∀ {X : Type u_1} [inst : UniformSpace X], IsUltraUniformity (SeparationQuo
tient X) ↔ IsUltraUniformity X
参数：SeparationQuotient X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isUltraUniformity`：IsUniformInducing.isUltraUniformity
 [IsUltraUniformity Y] {f : X -> Y} (hf : IsUniformInducing f) : IsUltraUniformi
ty X
· 使用引理 `SeparationQuotient.isUniformInducing_mk`：SeparationQuotient.isUniformInd
ucing_mk : IsUniformInducing (mk : α -> SeparationQuotient α)
-/
@[simp] lemma IsUltraUniformity.separationQuotient_iff :
    IsUltraUniformity (SeparationQuotient X) ↔ IsUltraUniformity X :=
  ⟨fun _ ↦ SeparationQuotient.isUniformInducing_mk.isUltraUniformity,
   fun _ ↦ inferInstance⟩
/-
**IsUltraUniformity.completion_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUltraUniformity`
。
形式化陈述：∀ {X : Type u_1} [inst : UniformSpace X], IsUltraUniformity (UniformSpace.
Completion X) ↔ IsUltraUniformity X
参数：UniformSpace.Completion X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUltraUniformity.cauchyFilter_iff`：∀ {X : Type u_1} [inst : UniformSpac
e X], IsUltraUniformity (CauchyFilter X) ↔ IsUltraUniformity X
· 使用定理 `IsUltraUniformity.separationQuotient_iff`：∀ {X : Type u_1} [inst : Unifo
rmSpace X], IsUltraUniformity (SeparationQuotient X) ↔ IsUltraUniformity X
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma IsUltraUniformity.completion_iff :
    IsUltraUniformity (UniformSpace.Completion X) ↔ IsUltraUniformity X := by
  rw [iff_comm, ← cauchyFilter_iff, ← separationQuotient_iff]
  exact Iff.rfl
/-
**IsUltraUniformity.completion** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.completion [IsUltraUniformity X] : IsUltraUniformity (Un
iformSpace.Completion X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUltraUniformity.completion_iff`：∀ {X : Type u_1} [inst : UniformSpace 
X], IsUltraUniformity (UniformSpace.Completion X) ↔ IsUltraUniformity X
-/
instance IsUltraUniformity.completion [IsUltraUniformity X] :
    IsUltraUniformity (UniformSpace.Completion X) :=
  completion_iff.2 inferInstance
