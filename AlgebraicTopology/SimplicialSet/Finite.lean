/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.Data.Finite.Sigma

/-!
# Finite simplicial sets

A simplicial set is finite (`SSet.Finite`) if it has finitely
many nondegenerate simplices.

-/

public section

universe u

open Simplicial CategoryTheory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set is finite if it has finitely many nondegenerate simplices. -/
/-
**SSet.Finite** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set is finite if it has finitely many nondegenerate simplices.
-/
protected class Finite : Prop where
  finite : _root_.Finite X.N

attribute [instance] Finite.finite
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Finite] (n : ℕ) : Finite (X.nonDegenerate n) :=
  Finite.of_injective (fun x ↦ N.mk _ x.property) (fun x y h ↦ by
    rw [N.ext_iff, S.ext_iff'] at h
    aesop)
/-
**SSet.finite_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_hasDimensionLT (d : Nat) [X.HasDimensionLT d] (h : forall (i : N
at) (_ : i < d), Finite (X.nonDegenerate i)) : X.Finite where finite
参数：d : Nat；h : forall (i : Nat) (_ : i < d), Finite (X.nonDegenerate i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.nonDegenerate_eq_empty_of_hasDimensionLT`：nonDegenerate_eq_empty_of
_hasDimensionLT (hn : d <= n
-/
lemma finite_of_hasDimensionLT (d : ℕ) [X.HasDimensionLT d]
    (h : ∀ (i : ℕ) (_ : i < d), Finite (X.nonDegenerate i)) :
    X.Finite where
  finite := by
    have (i : Fin d) : Finite (X.nonDegenerate i) := h i.1 i.2
    refine Finite.of_surjective (α := Σ (i : Fin d), X.nonDegenerate i)
      (f := fun ⟨i, x⟩ ↦ N.mk _ x.property) (fun x ↦ ?_)
    by_cases hj : x.dim < d
    · exact ⟨⟨⟨_, hj⟩, ⟨_, x.nonDegenerate⟩⟩, rfl⟩
    · have := x.nonDegenerate
      simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d x.dim (by simpa using hj)] at this

set_option backward.defeqAttrib.useBackward true in
/-
**SSet.hasDimensionLT_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_of_finite [X.Finite] : exists (d : Nat), X.HasDimensionLT d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Finite.finite`：∀ {X : _root_.SSet} [self : X.Finite], Finite X.N
· 使用定理 `Finset.max_of_nonempty`：max_of_nonempty {s : Finset α} (h : s.Nonempty) 
: exists a : α, s.max = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty {s : Finset 
α} : ¬s.Nonempty ↔ s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma hasDimensionLT_of_finite [X.Finite] :
    ∃ (d : ℕ), X.HasDimensionLT d := by
  have : Fintype X.N := Fintype.ofFinite _
  let φ (x : X.N) : ℕ := x.dim
  obtain ⟨d, hd⟩ : ∃ (d : ℕ), ∀ (s : ℕ) (_ : s ∈ Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      exact ⟨d + 1, fun _ _ ↦ by grind [WithBot.coe_le_coe, → Finset.le_max]⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [h]
      exact ⟨0, by simp⟩
  refine ⟨d, ⟨fun n hn ↦ ?_⟩⟩
  ext x
  simp only [mem_degenerate_iff_notMem_nonDegenerate, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  intro hx
  have := hd (φ (N.mk _ hx)) (by simp)
  dsimp [φ] at this
  lia
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Finite] (n : SimplexCategoryᵒᵖ) : Finite (X.obj n) := by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
    X.nonDegenerate m.1) → X _⦋n⦌ := fun ⟨m, f, x⟩ ↦ X.map f.op x.1
  have hφ : Function.Surjective φ := fun x ↦ by
    obtain ⟨m, f, hf, y, rfl⟩ := X.exists_nonDegenerate x
    have := SimplexCategory.le_of_epi f
    exact ⟨⟨⟨m, by lia⟩, f, y⟩, rfl⟩
  exact Finite.of_surjective _ hφ
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Finite] (A : X.Subcomplex) : SSet.Finite A := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  refine finite_of_hasDimensionLT _ d (fun i hi ↦ ?_)
  apply Finite.of_injective (f := fun a ↦ a.1.1)
  rintro ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ rfl
  rfl

variable {X}
/-
**SSet.finite_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y) [hf : Mono f] : X.Fin
ite
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_of_finite`：hasDimensionLT_of_finite [X.Finite] : exi
sts (d : Nat), X.HasDimensionLT d
· 使用引理 `SSet.hasDimensionLT_of_mono`：hasDimensionLT_of_mono {X Y : SSet.{u}} (f 
: X ⟶ Y) [Mono f] (d : Nat) [Y.HasDimensionLT d] : X.HasDimensionLT d where dege
nerate_eq_top n h…
· 使用引理 `SSet.finite_of_hasDimensionLT`：finite_of_hasDimensionLT (d : Nat) [X.Has
DimensionLT d] (h : forall (i : Nat) (_ : i < d), Finite (X.nonDegenerate i)) : 
X.Finite where fini…
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `SSet.instFiniteObjOppositeSimplexCategoryOfFinite`：∀ (X : _root_.SSet) [
X.Finite] (n : SimplexCategoryᵒᵖ), Finite (X.obj n)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y) [hf : Mono f] : X.Finite := by
  obtain ⟨d, _⟩ := Y.hasDimensionLT_of_finite
  have := hasDimensionLT_of_mono f d
  exact finite_of_hasDimensionLT _ d
    (fun _ _ ↦ Finite.of_injective _
      ((injective_of_mono (f.app _)).comp Subtype.val_injective))
/-
**SSet.finite_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_epi {Y : SSet.{u}} [X.Finite] (f : X ⟶ Y) [hf : Epi f] : Y.Finit
e
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_of_finite`：hasDimensionLT_of_finite [X.Finite] : exi
sts (d : Nat), X.HasDimensionLT d
· 使用引理 `SSet.hasDimensionLT_of_epi`：hasDimensionLT_of_epi {X Y : SSet.{u}} (f : 
X ⟶ Y) [Epi f] (d : Nat) [X.HasDimensionLT d] : Y.HasDimensionLT d where degener
ate_eq_top n hn
· 使用引理 `SSet.finite_of_hasDimensionLT`：finite_of_hasDimensionLT (d : Nat) [X.Has
DimensionLT d] (h : forall (i : Nat) (_ : i < d), Finite (X.nonDegenerate i)) : 
X.Finite where fini…
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `SSet.instFiniteObjOppositeSimplexCategoryOfFinite`：∀ (X : _root_.SSet) [
X.Finite] (n : SimplexCategoryᵒᵖ), Finite (X.obj n)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.epi_iff_epi_app`：∀ {K : Type u} [inst : Category
Theory.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
-/
lemma finite_of_epi {Y : SSet.{u}} [X.Finite] (f : X ⟶ Y) [hf : Epi f] : Y.Finite := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  have := hasDimensionLT_of_epi f d
  refine finite_of_hasDimensionLT _ d (fun i hi ↦ ?_)
  have : Finite (Y _⦋i⦌) := by
    rw [NatTrans.epi_iff_epi_app] at hf
    simp only [epi_iff_surjective] at hf
    exact Finite.of_surjective _ (hf _)
  infer_instance
/-
**SSet.finite_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_of_iso {Y : SSet.{u}} (e : X ≅ Y) [X.Finite] : Y.Finite
参数：e : X ≅ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.finite_of_mono`：finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y
) [hf : Mono f] : X.Finite
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma finite_of_iso {Y : SSet.{u}} (e : X ≅ Y) [X.Finite] : Y.Finite :=
  finite_of_mono e.inv
/-
**SSet.finite_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) : X.Finite ↔ Y.Finite
参数：e : X ≅ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.finite_of_iso`：finite_of_iso {Y : SSet.{u}} (e : X ≅ Y) [X.Finite] 
: Y.Finite
-/
lemma finite_iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) : X.Finite ↔ Y.Finite :=
  ⟨fun _ ↦ finite_of_iso e, fun _ ↦ finite_of_iso e.symm⟩

variable (X) in
/-
**SSet.finite_subcomplex_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_subcomplex_top_iff : SSet.Finite (⊤ : X.Subcomplex) ↔ X.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.finite_iff_of_iso`：finite_iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) : X
.Finite ↔ Y.Finite
-/
lemma finite_subcomplex_top_iff :
    SSet.Finite (⊤ : X.Subcomplex) ↔ X.Finite :=
  finite_iff_of_iso (Subcomplex.topIso X)
/-
**SSet.finite_range** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
形式化陈述：finite_range {Y : SSet.{u}} (f : Y ⟶ X) [Y.Finite] : SSet.Finite (Subcompl
ex.range f)
参数：f : Y ⟶ X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.finite_of_epi`：finite_of_epi {Y : SSet.{u}} [X.Finite] (f : X ⟶ Y) 
[hf : Epi f] : Y.Finite
· 使用定理 `SSet.Subcomplex.instEpiToRange`：∀ {X Y : _root_.SSet} (f : X ⟶ Y), Categ
oryTheory.Epi (SSet.Subcomplex.toRange f)
-/
instance finite_range {Y : SSet.{u}} (f : Y ⟶ X) [Y.Finite] :
    SSet.Finite (Subcomplex.range f) :=
  finite_of_epi (Subcomplex.toRange f)

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.finite_iSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：finite_iSup_iff {X : SSet.{u}} {ι : Type*} [Finite ι] (A : ι -> X.Subcompl
ex) : SSet.Finite (⨆ i, A i :) ↔ forall i, SSet.Finite (A i)
参数：A : ι -> X.Subcomplex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.finite_of_mono`：finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y
) [hf : Mono f] : X.Finite
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `SSet.Finite.finite`：∀ {X : _root_.SSet} [self : X.Finite], Finite X.N
· 使用定理 `SSet.N.nonDegenerate`：∀ {X : _root_.SSet} (self : X.N), self.simplex ∈ X
.nonDegenerate self.dim
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `SSet.N.mk_surjective`：mk_surjective (x : X.N) : exists (n : Nat) (y : X.
nonDegenerate n), x = N.mk _ y.prop
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用引理 `SSet.Subcomplex.mem_nonDegenerate_iff`：mem_nonDegenerate_iff {n : Nat} (
x : A.obj (op ⦋n⦌)) : dsimp% x in nonDegenerate A n ↔ x.val in X.nonDegenerate n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma finite_iSup_iff {X : SSet.{u}} {ι : Type*} [Finite ι]
    (A : ι → X.Subcomplex) :
    SSet.Finite (⨆ i, A i :) ↔ ∀ i, SSet.Finite (A i) := by
  refine ⟨fun h i ↦ finite_of_mono (Subcomplex.homOfLE (le_iSup A i)), fun h ↦ ⟨?_⟩⟩
  refine Finite.of_surjective (f := fun (⟨i, s⟩ : Σ (i : ι), (A i).toSSet.N) ↦
    N.mk ((Subcomplex.homOfLE (le_iSup A i)).app _ s.simplex)
      (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenerate)) ?_
  intro s
  obtain ⟨d, ⟨⟨s, h₁⟩, h₂⟩, rfl⟩ := s.mk_surjective
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at h₁
  obtain ⟨i, hi⟩ := h₁
  rw [Subcomplex.mem_nonDegenerate_iff] at h₂
  exact ⟨⟨i, N.mk ⟨s, hi⟩ (by rwa [Subcomplex.mem_nonDegenerate_iff])⟩, rfl⟩

end SSet

