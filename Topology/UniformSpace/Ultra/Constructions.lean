/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Products of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.prod`: a product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.
* `IsUltraUniformity.pi`: an indexed product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.

## Implementation details

This file can be split to separate imports to have the `Prod` and `Pi` instances separately,
but would be somewhat unnatural since they are closely related.
The `Prod` instance only requires `Mathlib/Topology/UniformSpace/Basic.lean`.

-/

public section

variable {X Y : Type*}

/-
**SetRel.isTrans_entourageProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SetRel.isTrans_entourageProd {s : SetRel X X} {t : SetRel Y Y} [s.IsTrans]
 [t.IsTrans] : (entourageProd s t).IsTrans where trans _ _ _ h h'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.trans`：∀ {α : Type u_1} (R : SetRel α α) {a b c : α} [R.IsTrans],
 (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance SetRel.isTrans_entourageProd {s : SetRel X X} {t : SetRel Y Y} [s.IsTrans] [t.IsTrans] :
    (entourageProd s t).IsTrans where
  trans _ _ _ h h' := ⟨s.trans h.left h'.left, t.trans h.right h'.right⟩
/-
**IsUltraUniformity.comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.comap {u : UniformSpace Y} (h : IsUltraUniformity Y) (f 
: X -> Y) : @IsUltraUniformity _ (u.comap f)
参数：h : IsUltraUniformity Y；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
-/
lemma IsUltraUniformity.comap {u : UniformSpace Y} (h : IsUltraUniformity Y) (f : X → Y) :
    @IsUltraUniformity _ (u.comap f) := by
  let := u.comap f
  refine .mk_of_hasBasis (h.hasBasis.comap (Prod.map f f)) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨_, _, _⟩
    infer_instance
/-
**IsUltraUniformity.inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.inf {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
 (h' : @IsUltraUniformity _ u') : @IsUltraUniformity _ (u ⊓ u')
参数：h : @IsUltraUniformity _ u；h' : @IsUltraUniformity _ u'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `Filter.HasBasis.inf`：∀ {α : Type u_1} {l l' : Filter α} {ι : Type u_6} {
ι' : Type u_7} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
-/
lemma IsUltraUniformity.inf {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
    (h' : @IsUltraUniformity _ u') :
    @IsUltraUniformity _ (u ⊓ u') := by
  let := u ⊓ u'
  refine .mk_of_hasBasis (h.hasBasis.inf h'.hasBasis) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨⟨_, _, _⟩, _, _, _⟩
    infer_instance

/-- The product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
/-
**IsUltraUniformity.prod** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.prod [UniformSpace X] [UniformSpace Y] [IsUltraUniformit
y X] [IsUltraUniformity Y] : IsUltraUniformity (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.inf`：IsUltraUniformity.inf {u u' : UniformSpace X} (h 
: @IsUltraUniformity _ u) (h' : @IsUltraUniformity _ u') : @IsUltraUniformity _ 
(u ⊓ u')
· 使用引理 `IsUltraUniformity.comap`：IsUltraUniformity.comap {u : UniformSpace Y} (h
 : IsUltraUniformity Y) (f : X -> Y) : @IsUltraUniformity _ (u.comap f)

--- 原说明 ---
The product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity.
-/
instance IsUltraUniformity.prod [UniformSpace X] [UniformSpace Y]
    [IsUltraUniformity X] [IsUltraUniformity Y] :
    IsUltraUniformity (X × Y) :=
  .inf (.comap ‹_› _) (.comap ‹_› _)
/-
**IsUltraUniformity.iInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.iInf {ι : Type*} {U : (i : ι) -> UniformSpace X} (hU : f
orall i, @IsUltraUniformity X (U i)) : @IsUltraUniformity _ (⨅ i, U i : UniformS
pace X)
参数：i : ι；hU : forall i, @IsUltraUniformity X (U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `Filter.HasBasis.iInf`：∀ {α : Type u_1} {ι : Type u_6} {ι' : ι → Type u_7
} {l : ι → Filter α} {p : (i : ι) → ι' i → Prop}   {s : (i : ι) → ι' i → Set α},
   (∀ (i :…
· 使用定理 `IsUltraUniformity.hasBasis`：∀ {X : Type u_1} {inst : UniformSpace X} [se
lf : IsUltraUniformity X],   (uniformity X).HasBasis (fun s => s ∈ uniformity X 
∧ s.IsSymm ∧ s.I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
-/
lemma IsUltraUniformity.iInf {ι : Type*} {U : (i : ι) → UniformSpace X}
    (hU : ∀ i, @IsUltraUniformity X (U i)) :
    @IsUltraUniformity _ (⨅ i, U i : UniformSpace X) := by
  let : UniformSpace X := ⨅ i, U i
  refine .mk_of_hasBasis (iInf_uniformity ▸ Filter.HasBasis.iInf fun i ↦ (hU i).hasBasis) ?_ ?_ <;>
  · simp only [forall_and, Subtype.forall, id_eq, Set.iInter_coe_set, and_imp]
    rintro _ _ _ _ _
    infer_instance

/-- The indexed product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
/-
**IsUltraUniformity.pi** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.pi {ι : Type*} {X : ι -> Type*} [U : Π i, UniformSpace (
X i)] [h : forall i, IsUltraUniformity (X i)] : IsUltraUniformity (Π i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltraUniformity.iInf`：IsUltraUniformity.iInf {ι : Type*} {U : (i : ι) 
-> UniformSpace X} (hU : forall i, @IsUltraUniformity X (U i)) : @IsUltraUniform
ity _ (⨅ i, …
· 使用引理 `IsUltraUniformity.comap`：IsUltraUniformity.comap {u : UniformSpace Y} (h
 : IsUltraUniformity Y) (f : X -> Y) : @IsUltraUniformity _ (u.comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.uniformSpace_eq`：Pi.uniformSpace_eq : Pi.uniformSpace α = ⨅ i, Unifor
mSpace.comap (eval i) (U i)

--- 原说明 ---
The indexed product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity.
-/
instance IsUltraUniformity.pi {ι : Type*} {X : ι → Type*} [U : Π i, UniformSpace (X i)]
    [h : ∀ i, IsUltraUniformity (X i)] :
    IsUltraUniformity (Π i, X i) := by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa +instances [Pi.uniformSpace_eq _] using this
  exact .iInf fun i ↦ .comap (h i) (Function.eval i)
/-
**IsUltraUniformity.bot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsUltraUniformity.bot [UniformSpace X] [DiscreteUniformity X] : IsUltraUni
formity X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_principal`：hasBasis_principal (t : Set α) : (𝓟 t).HasBas
is (fun _ : Unit => True) fun _ => t
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteUniformity.eq_principal_setRelId`：eq_principal_setRelId : unifor
mity X = 𝓟 SetRel.id
-/
instance IsUltraUniformity.bot [UniformSpace X] [DiscreteUniformity X] : IsUltraUniformity X := by
  have := Filter.hasBasis_principal (SetRel.id (α := X))
  rw [← DiscreteUniformity.eq_principal_setRelId] at this
  exact mk_of_hasBasis this inferInstance inferInstance
/-
**IsUltraUniformity.top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltraUniformity.top : @IsUltraUniformity X (⊤ : UniformSpace X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.hasBasis_top`：hasBasis_top : (⊤ : Filter α).HasBasis (fun _ : Uni
t => True) (fun _ => Set.univ)
· 使用引理 `IsUltraUniformity.mk_of_hasBasis`：IsUltraUniformity.mk_of_hasBasis {ι : 
Type*} {p : ι -> Prop} {s : ι -> SetRel X X} (h_basis : (𝓤 X).HasBasis p s) (h_s
ymm : forall i, p i ->…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `top_uniformity`：top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤
-/
lemma IsUltraUniformity.top : @IsUltraUniformity X (⊤ : UniformSpace X) := by
  let : UniformSpace X := ⊤
  have := Filter.hasBasis_top (α := (X × X))
  rw [← top_uniformity] at this
  exact mk_of_hasBasis this inferInstance inferInstance
