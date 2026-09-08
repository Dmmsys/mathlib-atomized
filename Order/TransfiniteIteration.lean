/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Limit

/-!
# Transfinite iteration of a function `I → I`

Given `φ : I → I` where `[SupSet I]`, we define the `j`th transfinite iteration of `φ`
for any `j : J`, with `J` a well-ordered type: this is `transfiniteIterate φ j : I → I`.
If `i₀ : I`, then `transfiniteIterate φ ⊥ i₀ = i₀`; if `j` is a non-maximal element,
then `transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j i₀)`; and
if `j` is a limit element, `transfiniteIterate φ j i₀` is the supremum
of the `transfiniteIterate φ l i₀` for `l < j`.

If `I` is a complete lattice, we show that `j ↦ transfiniteIterate φ j i₀` is
a monotone function if `i ≤ φ i` for all `i`. Moreover, if `i < φ i`
when `i ≠ ⊤`, we show in the lemma `top_mem_range_transfiniteIteration` that
there exists `j : J` such that `transfiniteIteration φ i₀ j = ⊤` if we assume that
`j ↦ transfiniteIterate φ i₀ j : J → I` is not injective (which shall hold
when we know `Cardinal.mk I < Cardinal.mk J`).

## TODO (@joelriou)
* deduce that in a Grothendieck abelian category, there is a *set* `I` of monomorphisms
  such that any monomorphism is a transfinite composition of pushouts of morphisms in `I`,
  and then an object `X` is injective iff `X ⟶ 0` has the right lifting
  property with respect to `I`.

-/

@[expose] public section

universe w u

section

variable {I : Type u} [SupSet I] (φ : I → I)
  {J : Type w} [LinearOrder J] [SuccOrder J] [WellFoundedLT J]

/-- The `j`th-iteration of a function `φ : I → I` when `j : J` belongs to
a well-ordered type. -/
/-
**transfiniteIterate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：transfiniteIterate (j : J) : I -> I
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`th-iteration of a function `φ : I → I` when `j : J` belongs to
a well-ordered type.
-/
noncomputable def transfiniteIterate (j : J) : I → I :=
  SuccOrder.limitRecOn j
    (fun _ _ ↦ id) (fun _ _ g ↦ φ ∘ g) (fun y _ h ↦ ⨆ (x : Set.Iio y), h x.1 x.2)

@[simp]
/-
**transfiniteIterate_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transfiniteIterate_bot [OrderBot J] (i₀ : I) : transfiniteIterate φ (⊥ : J
) i₀ = i₀
参数：i₀ : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SuccOrder.limitRecOn_isMin`：limitRecOn_isMin (hb : IsMin b) : limitRecOn
 b isMin succ isSuccLimit = isMin b hb
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transfiniteIterate_bot [OrderBot J] (i₀ : I) :
    transfiniteIterate φ (⊥ : J) i₀ = i₀ := by
  dsimp [transfiniteIterate]
  simp only [isMin_iff_eq_bot, SuccOrder.limitRecOn_isMin, id_eq]
/-
**transfiniteIterate_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transfiniteIterate_succ (i₀ : I) (j : J) (hj : ¬ IsMax j) : transfiniteIte
rate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j i₀)
参数：i₀ : I；j : J；hj : ¬ IsMax j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.limitRecOn_succ_of_not_isMax`：limitRecOn_succ_of_not_isMax (hb
 : ¬IsMax b) : limitRecOn (Order.succ b) isMin succ isSuccLimit = succ b hb (lim
itRecOn b isMin succ isSuccL…
-/
lemma transfiniteIterate_succ (i₀ : I) (j : J) (hj : ¬ IsMax j) :
    transfiniteIterate φ (Order.succ j) i₀ =
      φ (transfiniteIterate φ j i₀) := by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_succ_of_not_isMax _ _ _ hj]
  rfl
/-
**transfiniteIterate_limit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transfiniteIterate_limit (i₀ : I) (j : J) (hj : Order.IsSuccLimit j) : tra
nsfiniteIterate φ j i₀ = ⨆ (x : Set.Iio j), transfiniteIterate φ x.1 i₀
参数：i₀ : I；j : J；hj : Order.IsSuccLimit j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SuccOrder.limitRecOn_of_isSuccLimit`：limitRecOn_of_isSuccLimit (hb : IsS
uccLimit b) : limitRecOn b isMin succ isSuccLimit = isSuccLimit b hb fun x _ => 
limitRecOn x isMin succ i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transfiniteIterate_limit (i₀ : I) (j : J) (hj : Order.IsSuccLimit j) :
    transfiniteIterate φ j i₀ =
      ⨆ (x : Set.Iio j), transfiniteIterate φ x.1 i₀ := by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hj]
  simp only [iSup_apply]

end

section

variable {I : Type u} [CompleteLattice I] (φ : I → I) (i₀ : I)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-
**monotone_transfiniteIterate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_transfiniteIterate (hφ : forall (i : I), i <= φ i) : Monotone (fu
n (j : J) => transfiniteIterate φ j i₀)
参数：hφ : forall (i : I), i <= φ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMin.eq_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot 
α] {a : α}, IsMin a → a = ⊥
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `transfiniteIterate_succ`：transfiniteIterate_succ (i₀ : I) (j : J) (hj : 
¬ IsMax j) : transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j 
i₀)
· 使用引理 `transfiniteIterate_limit`：transfiniteIterate_limit (i₀ : I) (j : J) (hj 
: Order.IsSuccLimit j) : transfiniteIterate φ j i₀ = ⨆ (x : Set.Iio j), transfin
iteIterate φ x…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma monotone_transfiniteIterate (hφ : ∀ (i : I), i ≤ φ i) :
    Monotone (fun (j : J) ↦ transfiniteIterate φ j i₀) := by
  intro k j hkj
  induction j using SuccOrder.limitRecOn with
  | isMin k hk =>
    obtain rfl := hk.eq_bot
    obtain rfl : k = ⊥ := by simpa using hkj
    rfl
  | succ k' hk' hkk' =>
    obtain hkj | rfl := hkj.lt_or_eq
    · refine (hkk' ((Order.lt_succ_iff_of_not_isMax hk').mp hkj)).trans ?_
      dsimp
      rw [transfiniteIterate_succ _ _ _ hk']
      apply hφ
    · rfl
  | isSuccLimit k' hk' _ =>
    obtain hkj | rfl := hkj.lt_or_eq
    · dsimp
      rw [transfiniteIterate_limit _ _ _ hk']
      exact le_iSup (fun (⟨l, hl⟩ : Set.Iio k') ↦ transfiniteIterate φ l i₀) ⟨k, hkj⟩
    · rfl
/-
**top_mem_range_transfiniteIterate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：top_mem_range_transfiniteIterate (hφ' : forall i != (⊤ : I), i < φ i) (φto
p : φ ⊤ = ⊤) (H : ¬ Function.Injective (fun (j : J) => transfiniteIterate φ j i₀
)) : exists (j : J), transfiniteIterate φ j i₀ = ⊤
参数：hφ' : forall i != (⊤ : I), i < φ i；φtop : φ ⊤ = ⊤；H : ¬ Function.Injective (f
un (j : J) => transfiniteIterate φ j i₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `transfiniteIterate_succ`：transfiniteIterate_succ (i₀ : I) (j : J) (hj : 
¬ IsMax j) : transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j 
i₀)
· 使用引理 `monotone_transfiniteIterate`：monotone_transfiniteIterate (hφ : forall (i
 : I), i <= φ i) : Monotone (fun (j : J) => transfiniteIterate φ j i₀)
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma top_mem_range_transfiniteIterate
    (hφ' : ∀ i ≠ (⊤ : I), i < φ i) (φtop : φ ⊤ = ⊤)
    (H : ¬ Function.Injective (fun (j : J) ↦ transfiniteIterate φ j i₀)) :
    ∃ (j : J), transfiniteIterate φ j i₀ = ⊤ := by
  have hφ (i : I) : i ≤ φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : ∃ (j₁ j₂ : J) (hj : j₁ < j₂),
      transfiniteIterate φ j₁ i₀ = transfiniteIterate φ j₂ i₀ := by
    grind [Function.Injective]
  by_contra!
  suffices transfiniteIterate φ j₁ i₀ < transfiniteIterate φ j₂ i₀ by
    simp only [eq, lt_self_iff_false] at this
  have hj₁ : ¬ IsMax j₁ := by
    simp only [not_isMax_iff]
    exact ⟨_, hj⟩
  refine lt_of_lt_of_le (hφ' _ (this j₁)) ?_
  rw [← transfiniteIterate_succ φ i₀ j₁ hj₁]
  exact monotone_transfiniteIterate _ _ hφ (Order.succ_le_of_lt hj)

end

