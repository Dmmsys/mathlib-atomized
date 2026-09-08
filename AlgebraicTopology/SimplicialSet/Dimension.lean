/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Dimension of a simplicial set

For a simplicial set `X` and `d : ℕ`, we introduce a typeclass
`X.HasDimensionLT d` saying that the dimension of `X` is `< d`,
i.e. all nondegenerate simplices of `X` are of dimension `< d`.

-/

public section

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-- A simplicial set `X` has dimension `< d` iff for any `n : ℕ`
such that `d ≤ n`, all `n`-simplices are degenerate. -/
@[mk_iff]
/-
**SSet.HasDimensionLT** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet`。
形式化陈述：_root_.SSet → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set `X` has dimension `< d` iff for any `n : ℕ`
such that `d ≤ n`, all `n`-simplices are degenerate.
-/
class HasDimensionLT (X : SSet.{u}) (d : ℕ) : Prop where
  degenerate_eq_top (n : ℕ) (hn : d ≤ n) : X.degenerate n = ⊤

/-- A simplicial set has dimension `≤ d` if it has dimension `< d + 1`. -/
/-
**SSet.HasDimensionLE** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：HasDimensionLE (X : SSet.{u}) (d : Nat)
参数：X : SSet.{u}；d : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial set has dimension `≤ d` if it has dimension `< d + 1`.
-/
abbrev HasDimensionLE (X : SSet.{u}) (d : ℕ) := X.HasDimensionLT (d + 1)

section

variable (X : SSet.{u}) (d : ℕ) [X.HasDimensionLT d] (n : ℕ)

/-
**SSet.degenerate_eq_univ_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：degenerate_eq_univ_of_hasDimensionLT (hn : d <= n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.HasDimensionLT.degenerate_eq_top`：∀ {X : _root_.SSet} {d : ℕ} [self
 : X.HasDimensionLT d] (n : ℕ), d ≤ n → X.degenerate n = ⊤
-/
lemma degenerate_eq_univ_of_hasDimensionLT (hn : d ≤ n := by lia) : X.degenerate n = Set.univ :=
  HasDimensionLT.degenerate_eq_top n hn
/-
**SSet.nonDegenerate_eq_empty_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet`
。
形式化陈述：nonDegenerate_eq_empty_of_hasDimensionLT (hn : d <= n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.degenerate_eq_univ_of_hasDimensionLT`：degenerate_eq_univ_of_hasDime
nsionLT (hn : d <= n
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nonDegenerate_eq_empty_of_hasDimensionLT (hn : d ≤ n := by lia) : X.nonDegenerate n = ∅ := by
  simp [nonDegenerate, X.degenerate_eq_univ_of_hasDimensionLT d n hn]

@[deprecated (since := "2026-04-06")]
alias degenerate_eq_top_of_hasDimensionLT := degenerate_eq_univ_of_hasDimensionLT
@[deprecated (since := "2026-04-06")]
alias nonDegenerate_eq_bot_of_hasDimensionLT := nonDegenerate_eq_empty_of_hasDimensionLT
/-
**SSet.dim_lt_of_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：dim_lt_of_nonDegenerate {n : Nat} (x : X.nonDegenerate n) (d : Nat) [X.Has
DimensionLT d] : n < d
参数：x : X.nonDegenerate n；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.nonDegenerate_eq_empty_of_hasDimensionLT`：nonDegenerate_eq_empty_of
_hasDimensionLT (hn : d <= n
-/
lemma dim_lt_of_nonDegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLT d] : n < d := by
  by_contra!
  obtain ⟨x, hx⟩ := x
  simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d n this] at hx
/-
**SSet.dim_le_of_nonDegenerate** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：dim_le_of_nonDegenerate {n : Nat} (x : X.nonDegenerate n) (d : Nat) [X.Has
DimensionLE d] : n <= d
参数：x : X.nonDegenerate n；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用引理 `SSet.dim_lt_of_nonDegenerate`：dim_lt_of_nonDegenerate {n : Nat} (x : X.n
onDegenerate n) (d : Nat) [X.HasDimensionLT d] : n < d
-/
lemma dim_le_of_nonDegenerate {n : ℕ} (x : X.nonDegenerate n) (d : ℕ)
    [X.HasDimensionLE d] : n ≤ d :=
  Nat.le_of_lt_succ (X.dim_lt_of_nonDegenerate x (d + 1))
/-
**SSet.hasDimensionLT_of_le** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_of_le (hn : d <= n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.degenerate_eq_univ_of_hasDimensionLT`：degenerate_eq_univ_of_hasDime
nsionLT (hn : d <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma hasDimensionLT_of_le (hn : d ≤ n := by lia) : HasDimensionLT X n where
  degenerate_eq_top i hi :=
    X.degenerate_eq_univ_of_hasDimensionLT d i (hn.trans hi)
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasDimensionLT X n] (k : ℕ) : HasDimensionLT X (n + k) :=
  X.hasDimensionLT_of_le n _

end

namespace Subcomplex

variable {X : SSet.{u}}

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (d : ℕ) [X.HasDimensionLT d] (A : X.Subcomplex) : HasDimensionLT A d where
  degenerate_eq_top (n : ℕ) (hd : d ≤ n) := by
    ext x
    simp [A.mem_degenerate_iff, X.degenerate_eq_univ_of_hasDimensionLT d n hd]
/-
**SSet.Subcomplex.le_iff_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subco
mplex`。
形式化陈述：le_iff_of_hasDimensionLT (A B : X.Subcomplex) (d : Nat) [X.HasDimensionLT 
d] : A <= B ↔ forall i < d, A.obj _ inter X.nonDegenerate i subseteq B.obj (op ⦋
i⦌)
参数：A B : X.Subcomplex；d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.le_iff_contains_nonDegenerate`：le_iff_contains_nonDegene
rate (B : X.Subcomplex) : A <= B ↔ forall (n : Nat) (x : X.nonDegenerate n), x.v
al in A.obj _ -> x.val in B.obj _
· 使用引理 `SSet.dim_lt_of_nonDegenerate`：dim_lt_of_nonDegenerate {n : Nat} (x : X.n
onDegenerate n) (d : Nat) [X.HasDimensionLT d] : n < d
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma le_iff_of_hasDimensionLT (A B : X.Subcomplex) (d : ℕ) [X.HasDimensionLT d] :
    A ≤ B ↔ ∀ i < d, A.obj _ ∩ X.nonDegenerate i ⊆ B.obj (op ⦋i⦌) := by
  refine ⟨fun h i hi a ⟨ha, _⟩ ↦ h _ ha, fun h ↦ ?_⟩
  rw [le_iff_contains_nonDegenerate]
  rintro n x hx
  exact h _ (X.dim_lt_of_nonDegenerate x d) ⟨hx, x.prop⟩
/-
**SSet.Subcomplex.eq_top_iff_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet.S
ubcomplex`。
形式化陈述：eq_top_iff_of_hasDimensionLT (A : X.Subcomplex) (d : Nat) [X.HasDimensionL
T d] : A = ⊤ ↔ forall i < d, X.nonDegenerate i subseteq A.obj _
参数：A : X.Subcomplex；d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SSet.Subcomplex.le_iff_of_hasDimensionLT`：le_iff_of_hasDimensionLT (A B 
: X.Subcomplex) (d : Nat) [X.HasDimensionLT d] : A <= B ↔ forall i < d, A.obj _ 
inter X.nonDegenerate i subset…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eq_top_iff_of_hasDimensionLT (A : X.Subcomplex) (d : ℕ) [X.HasDimensionLT d] :
    A = ⊤ ↔ ∀ i < d, X.nonDegenerate i ⊆ A.obj _ := by
  simp [← top_le_iff, le_iff_of_hasDimensionLT ⊤ A d]

end Subcomplex

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.hasDimensionLT_of_mono** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : Nat) [Y.
HasDimensionLT d] : X.HasDimensionLT d where degenerate_eq_top n hn
参数：f : X ⟶ Y；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.degenerate_iff_of_isIso`：degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso
 f] {n : Nat} (x : X _⦋n⦌) : f.app _ x in Y.degenerate n ↔ x in X.degenerate n
· 使用定理 `SSet.Subcomplex.instIsIsoToRangeOfMono`：∀ {X Y : _root_.SSet} (f : X ⟶ Y
) [CategoryTheory.Mono f], CategoryTheory.IsIso (SSet.Subcomplex.toRange f)
· 使用引理 `SSet.Subcomplex.mem_degenerate_iff`：mem_degenerate_iff {n : Nat} (x : A.
obj (op ⦋n⦌)) : dsimp% x in degenerate A n ↔ x.val in X.degenerate n
· 使用引理 `SSet.degenerate_eq_univ_of_hasDimensionLT`：degenerate_eq_univ_of_hasDime
nsionLT (hn : d <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasDimensionLT_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (d : ℕ)
    [Y.HasDimensionLT d] : X.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    rw [← degenerate_iff_of_isIso (Subcomplex.toRange f),
      Subcomplex.mem_degenerate_iff, Y.degenerate_eq_univ_of_hasDimensionLT d n hn]
    simp
/-
**SSet.Subcomplex.hasDimensionLT_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomple
x`。
形式化陈述：∀ {X : _root_.SSet} {A B : X.Subcomplex}, A ≤ B → ∀ (d : ℕ) [B.toSSet.HasD
imensionLT d], A.toSSet.HasDimensionLT d
参数：d : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_of_mono`：hasDimensionLT_of_mono {X Y : SSet.{u}} (f 
: X ⟶ Y) [Mono f] (d : Nat) [Y.HasDimensionLT d] : X.HasDimensionLT d where dege
nerate_eq_top n h…
-/
lemma Subcomplex.hasDimensionLT_of_le
    {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) (d : ℕ) [HasDimensionLT B d] :
    HasDimensionLT A d :=
  hasDimensionLT_of_mono (Subcomplex.homOfLE h) d
/-
**SSet.hasDimensionLT_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_of_epi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : Nat) [X.Ha
sDimensionLT d] : Y.HasDimensionLT d where degenerate_eq_top n hn
参数：f : X ⟶ Y；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.instEpiAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheor
y.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F G : CategoryTheory…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用引理 `SSet.degenerate_app_apply`：degenerate_app_apply {n : Nat} {x : X _⦋n⦌} (
hx : x in X.degenerate n) (f : X ⟶ Y) : f.app _ x in Y.degenerate n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SSet.degenerate_eq_univ_of_hasDimensionLT`：degenerate_eq_univ_of_hasDime
nsionLT (hn : d <= n
-/
lemma hasDimensionLT_of_epi {X Y : SSet.{u}} (f : X ⟶ Y) [Epi f] (d : ℕ)
    [X.HasDimensionLT d] : Y.HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext y
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain ⟨x, rfl⟩ := epi_iff_surjective (f := (f.app (op ⦋n⦌))).1 inferInstance y
    apply degenerate_app_apply
    simp [X.degenerate_eq_univ_of_hasDimensionLT d n hn]
/-
**SSet.hasDimensionLT_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (d : Nat) : X.HasDi
mensionLT d ↔ Y.HasDimensionLT d
参数：e : X ≅ Y；d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_of_epi`：hasDimensionLT_of_epi {X Y : SSet.{u}} (f : 
X ⟶ Y) [Epi f] (d : Nat) [X.HasDimensionLT d] : Y.HasDimensionLT d where degener
ate_eq_top n hn
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma hasDimensionLT_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (d : ℕ) :
    X.HasDimensionLT d ↔ Y.HasDimensionLT d :=
  ⟨fun _ ↦ hasDimensionLT_of_epi e.hom d, fun _ ↦ hasDimensionLT_of_epi e.inv d⟩
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : SSet.{u}} (f : X ⟶ Y) (d : ℕ) [X.HasDimensionLT d] :
    HasDimensionLT (Subcomplex.range f) d :=
  hasDimensionLT_of_epi (Subcomplex.toRange f) d
/-
**SSet.hasDimensionLT_iSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_iSup_iff {X : SSet.{u}} {ι : Type*} (A : ι -> X.Subcomplex)
 (d : Nat) : HasDimensionLT (⨆ i, A i :) d ↔ forall i, HasDimensionLT (A i) d
参数：A : ι -> X.Subcomplex；d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma hasDimensionLT_iSup_iff {X : SSet.{u}} {ι : Type*} (A : ι → X.Subcomplex) (d : ℕ) :
    HasDimensionLT (⨆ i, A i :) d ↔ ∀ i, HasDimensionLT (A i) d := by
  simp only [hasDimensionLT_iff, Subcomplex.degenerate_eq_top_iff]
  aesop
/-
**SSet.hasDimensionLT_subcomplex_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：hasDimensionLT_subcomplex_top_iff (X : SSet.{u}) (d : Nat) : HasDimensionL
T (⊤ : X.Subcomplex) d ↔ X.HasDimensionLT d
参数：X : SSet.{u}；d : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.hasDimensionLT_iff_of_iso`：hasDimensionLT_iff_of_iso {X Y : SSet.{u
}} (e : X ≅ Y) (d : Nat) : X.HasDimensionLT d ↔ Y.HasDimensionLT d
-/
lemma hasDimensionLT_subcomplex_top_iff (X : SSet.{u}) (d : ℕ) :
    HasDimensionLT (⊤ : X.Subcomplex) d ↔ X.HasDimensionLT d :=
  hasDimensionLT_iff_of_iso (Subcomplex.topIso X) _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : SSet.{u}} (n : ℕ) : HasDimensionLT (⊥ : X.Subcomplex) n where
  degenerate_eq_top k hk := by
    ext ⟨x, hx⟩
    tauto

end SSet

