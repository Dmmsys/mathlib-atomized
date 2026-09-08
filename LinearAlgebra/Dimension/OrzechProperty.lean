/-
Copyright (c) 2018 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Orzech

/-! # Bases of modules and the Orzech property

It is shown in this file that any spanning set of a module over a ring satisfying the Orzech
property of cardinality not exceeding the rank of the module must be linearly independent,
and therefore is a basis.
-/

@[expose] public section

section Basis

open Module Submodule

variable {R M : Type*} [Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M]

/-
**linearIndependent_of_top_le_span_of_card_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：linearIndependent_of_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι
] {b : ι -> M} (spans : ⊤ <= span R (Set.range b)) (card_le : Fintype.card ι <= 
finrank R M) : LinearIndependent R b
参数：spans : ⊤ <= span R (Set.range b)；card_le : Fintype.card ι <= finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用引理 `exists_linearIndependent_of_le_finrank`：exists_linearIndependent_of_le_f
inrank {n : Nat} (hn : n <= finrank R M) : exists f : Fin n -> M, LinearIndepend
ent R f
· 使用定理 `OrzechProperty.injective_of_surjective_of_injective`：injective_of_surjec
tive_of_injective {N : Type w} [AddCommMonoid N] [Module R N] (i f : N ->ₗ[R] M)
 (hi : Injective i) (hf : Surjective f) :…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem linearIndependent_of_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_le : Fintype.card ι ≤ finrank R M) :
    LinearIndependent R b := by
  rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.equivFin _).injective) spans
/-
**linearIndependent_of_top_le_span_of_card_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι
] {b : ι -> M} (spans : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = f
inrank R M) : LinearIndependent R b
参数：spans : ⊤ <= span R (Set.range b)；card_eq : Fintype.card ι = finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_of_top_le_span_of_card_le_finrank`：linearIndependent_o
f_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι] {b : ι -> M} (spans : ⊤
 <= span R (Set.range b)) (card_le : Fint…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι → M}
    (spans : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    LinearIndependent R b :=
  linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
/-
**linearIndependent_iff_card_eq_finrank_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_card_eq_finrank_span [Nontrivial R] {ι} [Fintype ι] 
{b : ι -> M} : LinearIndependent R b ↔ Fintype.card ι = (Set.range b).finrank R 
where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_span_eq_card`：finrank_span_eq_card [Nontrivial R] {ι : Type*} [F
intype ι] {b : ι -> M} (hb : LinearIndependent R b) : finrank R (span R (Set.ran
ge b)) = F…
· 使用定理 `strongRankCondition_of_orzechProperty`：∀ (R : Type u) [inst : Semiring R
] [Nontrivial R] [OrzechProperty R], StrongRankCondition R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `linearIndependent_of_top_le_span_of_card_eq_finrank`：linearIndependent_o
f_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι -> M} (spans : ⊤
 <= span R (Set.range b)) (card_eq : Fint…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span.
-/
theorem linearIndependent_iff_card_eq_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι = (Set.range b).finrank R where
  mp h := (finrank_span_eq_card h).symm
  mpr hc := by
    refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr <|
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i ↦ ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ ↦ (subtype_injective _).mem_set_image.mp ?_) hc
    rwa [← map_coe, ← span_image, ← Set.range_comp]
/-
**linearIndependent_iff_card_le_finrank_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] 
{b : ι -> M} : LinearIndependent R b ↔ Fintype.card ι <= (Set.range b).finrank R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff_card_eq_finrank_span`：linearIndependent_iff_card_e
q_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι -> M} : LinearIndependent R
 b ↔ Fintype.card ι = (Set.range…
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `finrank_range_le_card`：finrank_range_le_card {ι : Type*} [Fintype ι] (b 
: ι -> M) : (Set.range b).finrank R <= Fintype.card ι
· 使用定理 `strongRankCondition_of_orzechProperty`：∀ (R : Type u) [inst : Semiring R
] [Nontrivial R] [OrzechProperty R], StrongRankCondition R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι → M} :
    LinearIndependent R b ↔ Fintype.card ι ≤ (Set.range b).finrank R := by
  rw [linearIndependent_iff_card_eq_finrank_span, (finrank_range_le_card _).ge_iff_eq']

/-- A family of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
/-
**basisOfTopLeSpanOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι -> M) (le_s
pan : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basi
s ι R M
参数：b : ι -> M；le_span : ⊤ <= span R (Set.range b)；card_eq : Fintype.card ι = fin
rank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_of_top_le_span_of_card_eq_finrank`：linearIndependent_o
f_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι -> M} (spans : ⊤
 <= span R (Set.range b)) (card_eq : Fint…

--- 原说明 ---
A family of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property.
-/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basis ι R M :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]
/-
**coe_basisOfTopLeSpanOfCardEqFinrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι -> M) (
le_span : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : 
⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b
参数：b : ι -> M；le_span : ⊤ <= span R (Set.range b)；card_eq : Fintype.card ι = fin
rank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `linearIndependent_of_top_le_span_of_card_eq_finrank`：linearIndependent_o
f_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι -> M} (spans : ⊤
 <= span R (Set.range b)) (card_eq : Fint…
-/
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι → M)
    (le_span : ⊤ ≤ span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
/-
**finsetBasisOfTopLeSpanOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset M} (le_span : ⊤ <= span 
R (s : Set M)) (card_eq : s.card = finrank R M) : Basis {x // x in s} R M
参数：le_span : ⊤ <= span R (s : Set M)；card_eq : s.card = finrank R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finset of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property.
-/
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset M}
    (le_span : ⊤ ≤ span R (s : Set M)) (card_eq : s.card = finrank R M) : Basis {x // x ∈ s} R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) → M)
    ((@Subtype.range_coe_subtype _ fun x => x ∈ s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
/-
**setBasisOfTopLeSpanOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：setBasisOfTopLeSpanOfCardEqFinrank {s : Set M} [Fintype s] (le_span : ⊤ <=
 span R s) (card_eq : s.toFinset.card = finrank R M) : Basis s R M
参数：le_span : ⊤ <= span R s；card_eq : s.toFinset.card = finrank R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property.
-/
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set M} [Fintype s]
    (le_span : ⊤ ≤ span R s) (card_eq : s.toFinset.card = finrank R M) : Basis s R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s → M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

end Basis

