/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex

/-!
# A binary product of finite simplicial sets is finite

If `X₁` and `X₂` are respectively of dimensions `≤ d₁` and `≤ d₂`,
then `X₁ ⊗ X₂` has dimension `≤ d₁ + d₂`.

We also show that if `X₁` and `X₂` are finite, then `X₁ ⊗ X₂` is also finite.

-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Simplicial Opposite

namespace SSet

variable {X₁ X₂ X₃ X₄ : SSet.{u}}

set_option backward.isDefEq.respectTransparency.types false in
variable (X₁ X₂) in
/-
**SSet.iSup_subcomplexOfSimplex_prod_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：iSup_subcomplexOfSimplex_prod_eq_top : ⨆ (x₁ : X₁.N) (x₂ : X₂.N), (Subcomp
lex.ofSimplex x₁.simplex).prod (Subcomplex.ofSimplex x₂.simplex) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `SSet.Subcomplex.prod_obj`：∀ {X Y : _root_.SSet} (A : X.Subcomplex) (B : 
Y.Subcomplex) (Δ : SimplexCategoryᵒᵖ),   (A.prod B).obj Δ = (A.obj Δ).prod (B.ob
j Δ)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma iSup_subcomplexOfSimplex_prod_eq_top :
    ⨆ (x₁ : X₁.N) (x₂ : X₂.N),
      (Subcomplex.ofSimplex x₁.simplex).prod (Subcomplex.ofSimplex x₂.simplex) = ⊤ := by
  ext m ⟨x₁, x₂⟩
  simp only [Subfunctor.iSup_obj, Subcomplex.prod_obj, Set.mem_iUnion, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  have hx₁ : x₁ ∈ (⊤ : X₁.Subcomplex).obj _ := by simp
  have hx₂ : x₂ ∈ (⊤ : X₂.Subcomplex).obj _ := by simp
  simp only [← N.iSup_subcomplex_eq_top, Subfunctor.iSup_obj, Set.mem_iUnion] at hx₁ hx₂
  obtain ⟨s₁, hs₁⟩ := hx₁
  obtain ⟨s₂, hs₂⟩ := hx₂
  exact ⟨s₁, s₂, hs₁, hs₂⟩
/-
**SSet.Subcomplex.ofSimplexProd_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomp
lex`。
形式化陈述：∀ {X₁ X₂ : _root_.SSet} {p q : ℕ} (x₁ : X₁.obj (Opposite.op { len := p }))
 (x₂ : X₂.obj (Opposite.op { len := q })),   (SSet.Subcomplex.ofSimplex x₁).prod
 (SSet.Subcomplex.ofSimplex x₂) =     SSet.Subcomplex.range       (CategoryTheor
y.MonoidalCategoryStruct.tensorHom (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.
symm x₂))
参数：x₁ : X₁.obj (Opposite.op { len := p })；x₂ : X₂.obj (Opposite.op { len := q })
；SSet.Subcomplex.ofSimplex x₁；SSet.Subcomplex.ofSimplex x₂；CategoryTheory.Monoid
alCategoryStruct.tensorHom (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm x₂)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.range_tensorHom`：range_tensorHom {X₁ X₂ Y₁ Y₂ : SSet.{u}
} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) : range (f₁ otimesₘ f₂) = (range f₁).prod (range
 f₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SSet.Subcomplex.range_eq_ofSimplex`：range_eq_ofSimplex {n : Nat} (f : Δ[
n] ⟶ X) : range f = ofSimplex (yonedaEquiv f)
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Subcomplex.ofSimplexProd_eq_range {p q : ℕ} (x₁ : X₁ _⦋p⦌) (x₂ : X₂ _⦋q⦌) :
    (Subcomplex.ofSimplex x₁).prod (Subcomplex.ofSimplex x₂) =
      Subcomplex.range (yonedaEquiv.symm x₁ ⊗ₘ yonedaEquiv.symm x₂) := by
  simp [Subcomplex.range_tensorHom, Subcomplex.range_eq_ofSimplex]

variable (X₁ X₂) in
/-
**SSet.hasDimensionLT_prod** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_prod (d₁ d₂ : Nat) [X₁.HasDimensionLT d₁] [X₂.HasDimensionL
T d₂] (n : Nat) (hn : d₁ + d₂ <= n + 1
参数：d₁ d₂ : Nat；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.hasDimensionLT_subcomplex_top_iff`：hasDimensionLT_subcomplex_top_if
f (X : SSet.{u}) (d : Nat) : HasDimensionLT (⊤ : X.Subcomplex) d ↔ X.HasDimensio
nLT d
· 使用引理 `SSet.iSup_subcomplexOfSimplex_prod_eq_top`：iSup_subcomplexOfSimplex_prod
_eq_top : ⨆ (x₁ : X₁.N) (x₂ : X₂.N), (Subcomplex.ofSimplex x₁.simplex).prod (Sub
complex.ofSimplex x₂.simplex) =…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SSet.Subcomplex.ofSimplexProd_eq_range`：∀ {X₁ X₂ : _root_.SSet} {p q : ℕ
} (x₁ : X₁.obj (Opposite.op { len := p })) (x₂ : X₂.obj (Opposite.op { len := q 
})),   (SSet.Subcomplex.ofSi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SSet.dim_lt_of_nonDegenerate`：dim_lt_of_nonDegenerate {n : Nat} (x : X.n
onDegenerate n) (d : Nat) [X.HasDimensionLT d] : n < d
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用引理 `SSet.hasDimensionLT_of_le`：hasDimensionLT_of_le (hn : d <= n
· 使用定理 `SSet.prodStdSimplex.instHasDimensionLETensorObjObjSimplexCategoryStdSimp
lexMkHAddNat`：∀ {p q : ℕ},   (CategoryTheory.MonoidalCategoryStruct.tensorObj (S
Set.stdSimplex.obj { len := p })         (SSet.stdSimplex.obj { len := q }…
· 使用定理 `SSet.instHasDimensionLTToSSetRange`：∀ {X Y : _root_.SSet} (f : X ⟶ Y) (d
 : ℕ) [X.HasDimensionLT d], (SSet.Subcomplex.range f).toSSet.HasDimensionLT d
-/
lemma hasDimensionLT_prod
    (d₁ d₂ : ℕ) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂]
    (n : ℕ) (hn : d₁ + d₂ ≤ n + 1 := by lia) :
    (X₁ ⊗ X₂).HasDimensionLT n := by
  rw [← hasDimensionLT_subcomplex_top_iff, ← iSup_subcomplexOfSimplex_prod_eq_top]
  simp only [Subcomplex.ofSimplexProd_eq_range, hasDimensionLT_iSup_iff]
  intro x₁ x₂
  have := X₁.dim_lt_of_nonDegenerate ⟨_, x₁.nonDegenerate⟩ d₁
  have := X₂.dim_lt_of_nonDegenerate ⟨_, x₂.nonDegenerate⟩ d₂
  have := (Δ[x₁.dim] ⊗ Δ[x₂.dim]).hasDimensionLT_of_le (x₁.dim + x₂.dim + 1) n
  infer_instance

variable (X₁ X₂) in
/-
**SSet.hasDimensionLE_prod** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLE_prod (d₁ d₂ : Nat) [X₁.HasDimensionLE d₁] [X₂.HasDimensionL
E d₂] (n : Nat) (hn : d₁ + d₂ <= n
参数：d₁ d₂ : Nat；n : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_prod`：hasDimensionLT_prod (d₁ d₂ : Nat) [X₁.HasDimen
sionLT d₁] [X₂.HasDimensionLT d₂] (n : Nat) (hn : d₁ + d₂ <= n + 1
-/
lemma hasDimensionLE_prod
    (d₁ d₂ : ℕ) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂]
    (n : ℕ) (hn : d₁ + d₂ ≤ n := by lia) :
    (X₁ ⊗ X₂).HasDimensionLE n :=
  hasDimensionLT_prod X₁ X₂ (d₁ + 1) (d₂ + 1) (n + 1)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d₁ d₂ : ℕ) [X₁.HasDimensionLT d₁] [X₂.HasDimensionLT d₂] :
    (X₁ ⊗ X₂).HasDimensionLT (d₁ + d₂) :=
  hasDimensionLT_prod _ _ d₁ d₂ (d₁ + d₂)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d₁ d₂ : ℕ) [X₁.HasDimensionLE d₁] [X₂.HasDimensionLE d₂] :
    (X₁ ⊗ X₂).HasDimensionLE (d₁ + d₂) :=
  hasDimensionLE_prod _ _ d₁ d₂ (d₁ + d₂)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X₁.Finite] [X₂.Finite] : (X₁ ⊗ X₂).Finite := by
  obtain ⟨d₁, _⟩ := X₁.hasDimensionLT_of_finite
  obtain ⟨d₂, _⟩ := X₂.hasDimensionLT_of_finite
  exact finite_of_hasDimensionLT _ (d₁ + d₂) (fun _ _ ↦ inferInstance)

open CartesianMonoidalCategory in
/-
**SSet.finite_of_isPullback** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_isPullback {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X
₄} (sq : IsPullback t l r b) [X₂.Finite] [X₃.Finite] : X₁.Finite
参数：sq : IsPullback t l r b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hom_ext`：hom_ext (hP : IsPullback fst snd f g)
 {W : C} {k l : W ⟶ P} (h₀ : k ≫ fst = l ≫ fst) (h₁ : k ≫ snd = l ≫ snd) : k = l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `SSet.finite_of_mono`：finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y
) [hf : Mono f] : X.Finite
· 使用定理 `SSet.instFiniteTensorObj`：∀ {X₁ X₂ : _root_.SSet} [X₁.Finite] [X₂.Finite
], (CategoryTheory.MonoidalCategoryStruct.tensorObj X₁ X₂).Finite
-/
lemma finite_of_isPullback {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (sq : IsPullback t l r b) [X₂.Finite] [X₃.Finite] : X₁.Finite :=
  have : Mono (lift t l) :=
    ⟨fun _ _ h ↦ sq.hom_ext (by simpa using h =≫ fst _ _) (by simpa using h =≫ snd _ _)⟩
  finite_of_mono (lift t l)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X₂.Finite] [X₃.Finite] (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄) :
    (pullback r b).Finite :=
  finite_of_isPullback (IsPullback.of_hasPullback r b)

end SSet

