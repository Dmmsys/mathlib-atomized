/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homotopy.Path

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies. We show that the products of relative homotopies
are still relative homotopies. Finally, we specialize to the case
of path homotopies, and provide the definition for the product of path classes.
We show various lemmas associated with these products, such as the fact that
path products commute with path composition, and that projection is the inverse
of products.

## Definitions

### General homotopies
- `ContinuousMap.Homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `Homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `ContinuousMap.HomotopyRel.pi homotopies`: Same as `ContinuousMap.Homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `ContinuousMap.Homotopy.prod F G` is the product of homotopies F and G,
  where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
  The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
  Again, all homotopies are done relative to S.

- `ContinuousMap.HomotopyRel.prod F G`: Same as `ContinuousMap.Homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.

### Path products
- `Path.Homotopic.pi` The product of a family of path classes, where a path class is an equivalence
  class of paths up to path homotopy.

- `Path.Homotopic.prod` The product of two path classes.
-/

@[expose] public section


noncomputable section

namespace ContinuousMap

open ContinuousMap

section Pi

variable {I A : Type*} {X : I → Type*} [∀ i, TopologicalSpace (X i)] [TopologicalSpace A]
  {f g : ∀ i, C(A, X i)} {S : Set A}

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps!]
/-
**ContinuousMap.HomotopyRel.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy
Rel`。
形式化陈述：{I : Type u_1} →   {A : Type u_2} →     {X : I → Type u_3} →       [inst :
 (i : I) → TopologicalSpace (X i)] →         [inst_1 : TopologicalSpace A] →    
       {f g : (i : I) → C(A, X i)} →             {S : Set A} →               ((i
 : I) → (f i).HomotopyRel (g i) S) → (ContinuousMap.pi f).HomotopyRel (Continuou
sMap.pi g) S
参数：i : I；X i；i : I；A, X i；(i : I) → (f i).HomotopyRel (g i) S；ContinuousMap.pi f
；ContinuousMap.pi g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative product homotopy of `homotopies` between functions `f` and `g`
-/
def HomotopyRel.pi (homotopies : ∀ i : I, HomotopyRel (f i) (g i) S) :
    HomotopyRel (pi f) (pi g) S :=
  { Homotopy.pi fun i => (homotopies i).toHomotopy with
    prop' := by
      intro t x hx
      dsimp only [coe_mk, pi_eval, toFun_eq_coe, HomotopyWith.coe_toContinuousMap]
      simp only [funext_iff]
      intro i
      exact (homotopies i).prop' t x hx }

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {A : Type*} [TopologicalSpace A]
  {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : Set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps]
/-
**ContinuousMap.Homotopy.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`
。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         {A : Type u_3} →           [inst_2 : T
opologicalSpace A] →             {f₀ f₁ : C(A, α)} →               {g₀ g₁ : C(A,
 β)} → f₀.Homotopy f₁ → g₀.Homotopy g₁ → (f₀.prodMk g₀).Homotopy (f₁.prodMk g₁)
参数：A, α；A, β；f₀.prodMk g₀；f₁.prodMk g₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁`
-/
def Homotopy.prod (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (ContinuousMap.prodMk f₀ g₀) (ContinuousMap.prodMk f₁ g₁) where
  toFun t := (F t, G t)
  map_zero_left x := by simp only [prod_eval, Homotopy.apply_zero]
  map_one_left x := by simp only [prod_eval, Homotopy.apply_one]

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁` -/
@[simps!]
/-
**ContinuousMap.HomotopyRel.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homoto
pyRel`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : TopologicalSpace α] →     
  [inst_1 : TopologicalSpace β] →         {A : Type u_3} →           [inst_2 : T
opologicalSpace A] →             {f₀ f₁ : C(A, α)} →               {g₀ g₁ : C(A,
 β)} →                 {S : Set A} → f₀.HomotopyRel f₁ S → g₀.HomotopyRel g₁ S →
 (f₀.prodMk g₀).HomotopyRel (f₁.prodMk g₁) S
参数：A, α；A, β；f₀.prodMk g₀；f₁.prodMk g₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁` and `G` takes `g₀` to `g₁`
-/
def HomotopyRel.prod (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel g₀ g₁ S) :
    HomotopyRel (prodMk f₀ g₀) (prodMk f₁ g₁) S where
  toHomotopy := Homotopy.prod F.toHomotopy G.toHomotopy
  prop' t x hx := Prod.ext (F.prop' t x hx) (G.prop' t x hx)

end Prod

end ContinuousMap

namespace Path.Homotopic

local infixl:70 " ⬝ " => Quotient.trans

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {as bs cs : ∀ i, X i}

/-- The product of a family of path homotopies. This is just a specialization of `HomotopyRel`. -/
/-
**Path.Homotopic.piHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：piHomotopy (γ₀ γ₁ : forall i, Path (as i) (bs i)) (H : forall i, Path.Homo
topy (γ₀ i) (γ₁ i)) : Path.Homotopy (Path.pi γ₀) (Path.pi γ₁)
参数：γ₀ γ₁ : forall i, Path (as i) (bs i)；H : forall i, Path.Homotopy (γ₀ i) (γ₁ i
)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of path homotopies. This is just a specialization of `Ho
motopyRel`.
-/
def piHomotopy (γ₀ γ₁ : ∀ i, Path (as i) (bs i)) (H : ∀ i, Path.Homotopy (γ₀ i) (γ₁ i)) :
    Path.Homotopy (Path.pi γ₀) (Path.pi γ₁) :=
  ContinuousMap.HomotopyRel.pi H

/-- The product of a family of path homotopy classes. -/
/-
**Path.Homotopic.pi** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：pi (γ : forall i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.
Quotient as bs
参数：γ : forall i, Path.Homotopic.Quotient (as i) (bs i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of path homotopy classes.
-/
def pi (γ : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) : Path.Homotopic.Quotient as bs :=
  (_root_.Quotient.map Path.pi fun x y hxy =>
    Nonempty.map (piHomotopy x y) (Classical.nonempty_pi.mpr hxy)) (Quotient.choice γ)

set_option backward.isDefEq.respectTransparency false in
/-
**Path.Homotopic.pi_lift** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：pi_lift (γ : forall i, Path (as i) (bs i)) : (Path.Homotopic.pi fun i => (
Quotient.mk (γ i))) = Quotient.mk (Path.pi γ)
参数：γ : forall i, Path (as i) (bs i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.map.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} {sa : Setoid α}
 {sb : Setoid β} (f f_1 : α → β) (e_f : f = f_1)   (h : ∀ ⦃a b : α⦄, a ≈ b → f a
 ≈ f b) (a a_…
· 使用定理 `Quotient.choice_eq`：Quotient.choice_eq {ι : Type*} {α : ι -> Type*} {S :
 forall i, Setoid (α i)} (f : forall i, α i) : (Quotient.choice (S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pi_lift (γ : ∀ i, Path (as i) (bs i)) :
    (Path.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ) := by
  simp_rw [← Quotient.mk'_eq_mk, Quotient.mk', pi, Quotient.choice_eq, Quotient.map_mk]

/-- Composition and products commute.
  This is `Path.trans_pi_eq_pi_trans` descended to path homotopy classes. -/
/-
**Path.Homotopic.comp_pi_eq_pi_comp** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：comp_pi_eq_pi_comp (γ₀ : forall i, Path.Homotopic.Quotient (as i) (bs i)) 
(γ₁ : forall i, Path.Homotopic.Quotient (bs i) (cs i)) : pi γ₀ ⬝ pi γ₁ = pi fun 
i => γ₀ i ⬝ γ₁ i
参数：γ₀ : forall i, Path.Homotopic.Quotient (as i) (bs i)；γ₁ : forall i, Path.Homo
topic.Quotient (bs i) (cs i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.induction_on_pi`：Quotient.induction_on_pi {ι : Type*} {α : ι ->
 Sort*} {s : forall i, Setoid (α i)} {p : (forall i, Quotient (s i)) -> Prop} (f
 : forall i, Q…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Path.Homotopic.pi_lift`：pi_lift (γ : forall i, Path (as i) (bs i)) : (Pa
th.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.Homotopic.Quotient.mk_trans`：mk_trans (P₀ : Path x₀ x₁) (P₁ : Path 
x₁ x₂) : mk (P₀.trans P₁) = Quotient.trans (mk P₀) (mk P₁)
· 使用定理 `Path.trans_pi_eq_pi_trans`：trans_pi_eq_pi_trans (γ₀ : forall i, Path (as
 i) (bs i)) (γ₁ : forall i, Path (bs i) (cs i)) : (Path.pi γ₀).trans (Path.pi γ₁
) = Path.pi fun…

--- 原说明 ---
Composition and products commute.
  This is `Path.trans_pi_eq_pi_trans` descended to path homotopy classes.
-/
theorem comp_pi_eq_pi_comp (γ₀ : ∀ i, Path.Homotopic.Quotient (as i) (bs i))
    (γ₁ : ∀ i, Path.Homotopic.Quotient (bs i) (cs i)) : pi γ₀ ⬝ pi γ₁ = pi fun i ↦ γ₀ i ⬝ γ₁ i := by
  induction γ₁ using Quotient.induction_on_pi with | _ a =>
  induction γ₀ using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk, pi_lift]
  rw [← Path.Homotopic.Quotient.mk_trans, Path.trans_pi_eq_pi_trans, ← pi_lift]
  rfl

/-- Abbreviation for projection onto the ith coordinate. -/
/-
**Path.Homotopic.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Path.Homotopic`。
形式化陈述：proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient
 (as i) (bs i)
参数：i : ι；p : Path.Homotopic.Quotient as bs。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
Abbreviation for projection onto the ith coordinate.
-/
abbrev proj (i : ι) (p : Path.Homotopic.Quotient as bs) : Path.Homotopic.Quotient (as i) (bs i) :=
  p.map ⟨_, continuous_apply i⟩

/-- Lemmas showing projection is the inverse of pi. -/
@[simp]
/-
**Path.Homotopic.proj_pi** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：proj_pi (i : ι) (paths : forall i, Path.Homotopic.Quotient (as i) (bs i)) 
: proj i (pi paths) = paths i
参数：i : ι；paths : forall i, Path.Homotopic.Quotient (as i) (bs i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.induction_on_pi`：Quotient.induction_on_pi {ι : Type*} {α : ι ->
 Sort*} {s : forall i, Setoid (α i)} {p : (forall i, Quotient (s i)) -> Prop} (f
 : forall i, Q…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopic.proj.eq_1`：∀ {ι : Type u_1} {X : ι → Type u_2} [inst : (i
 : ι) → TopologicalSpace (X i)] {as bs : (i : ι) → X i} (i : ι)   (p : Path.Homo
topic.Quotient…
· 使用定理 `Path.Homotopic.pi_lift`：pi_lift (γ : forall i, Path (as i) (bs i)) : (Pa
th.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ)

--- 原说明 ---
Lemmas showing projection is the inverse of pi.
-/
theorem proj_pi (i : ι) (paths : ∀ i, Path.Homotopic.Quotient (as i) (bs i)) :
    proj i (pi paths) = paths i := by
  induction paths using Quotient.induction_on_pi
  simp only [Quotient.mk''_eq_mk]
  rw [proj, pi_lift]
  congr

@[simp]
/-
**Path.Homotopic.pi_proj** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p
参数：p : Path.Homotopic.Quotient as bs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopic.pi_lift`：pi_lift (γ : forall i, Path (as i) (bs i)) : (Pa
th.Homotopic.pi fun i => (Quotient.mk (γ i))) = Quotient.mk (Path.pi γ)
-/
theorem pi_proj (p : Path.Homotopic.Quotient as bs) : (pi fun i => proj i p) = p := by
  induction p using Quotient.inductionOn
  simp only [Quotient.mk''_eq_mk, ← Path.Homotopic.Quotient.mk_map, pi_lift]
  congr

end Pi

section Prod

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a₁ a₂ a₃ : α} {b₁ b₂ b₃ : β}
  {p₁ p₁' : Path a₁ a₂} {p₂ p₂' : Path b₁ b₂} (q₁ : Path.Homotopic.Quotient a₁ a₂)
  (q₂ : Path.Homotopic.Quotient b₁ b₂)

/-- The product of homotopies h₁ and h₂.
This is `HomotopyRel.prod` specialized for path homotopies. -/
/-
**Path.Homotopic.prodHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：prodHomotopy (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂') : Pat
h.Homotopy (p₁.prod p₂) (p₁'.prod p₂')
参数：h₁ : Path.Homotopy p₁ p₁'；h₂ : Path.Homotopy p₂ p₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of homotopies h₁ and h₂.
This is `HomotopyRel.prod` specialized for path homotopies.
-/
def prodHomotopy (h₁ : Path.Homotopy p₁ p₁') (h₂ : Path.Homotopy p₂ p₂') :
    Path.Homotopy (p₁.prod p₂) (p₁'.prod p₂') :=
  ContinuousMap.HomotopyRel.prod h₁ h₂

/-- The product of path classes q₁ and q₂. This is `Path.prod` descended to the quotient. -/
/-
**Path.Homotopic.prod** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁
 b₂) : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)
参数：q₁ : Path.Homotopic.Quotient a₁ a₂；q₂ : Path.Homotopic.Quotient b₁ b₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of path classes q₁ and q₂. This is `Path.prod` descended to the quot
ient.
-/
def prod (q₁ : Path.Homotopic.Quotient a₁ a₂) (q₂ : Path.Homotopic.Quotient b₁ b₂) :
    Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂) :=
  Quotient.map₂ Path.prod (fun _ _ h₁ _ _ h₂ => Nonempty.map2 prodHomotopy h₁ h₂) q₁ q₂

variable (p₁ p₁' p₂ p₂')
/-
**Path.Homotopic.prod_lift** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：prod_lift : prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod 
p₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_lift : prod (Quotient.mk p₁) (Quotient.mk p₂) = Quotient.mk (p₁.prod p₂) :=
  rfl

variable (r₁ : Path.Homotopic.Quotient a₂ a₃) (r₂ : Path.Homotopic.Quotient b₂ b₃)

/-- Products commute with path composition.
This is `trans_prod_eq_prod_trans` descended to the quotient. -/
/-
**Path.Homotopic.comp_prod_eq_prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopi
c`。
形式化陈述：comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind₂`：∀ {X : Type u} [inst : TopologicalSpace X]
 {Y : Type u_1} [inst_1 : TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}   {motive 
: Path.Homotopic.Q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.trans_prod_eq_prod_trans`：trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂
) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂) (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁
.prod δ₂) = (γ₁.tra…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Products commute with path composition.
This is `trans_prod_eq_prod_trans` descended to the quotient.
-/
theorem comp_prod_eq_prod_comp : prod q₁ q₂ ⬝ prod r₁ r₂ = prod (q₁ ⬝ r₁) (q₂ ⬝ r₂) := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  induction r₁, r₂ using Path.Homotopic.Quotient.ind₂
  simp only [prod_lift, ← Path.Homotopic.Quotient.mk_trans, Path.trans_prod_eq_prod_trans]

variable {c₁ c₂ : α × β}

/-- Abbreviation for projection onto the left coordinate of a path class. -/
/-
**Path.Homotopic.projLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Path.Homotopic`。
形式化陈述：projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.
1 c₂.1
参数：p : Path.Homotopic.Quotient c₁ c₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Abbreviation for projection onto the left coordinate of a path class.
-/
abbrev projLeft (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.1 c₂.1 :=
  p.map ⟨_, continuous_fst⟩

/-- Abbreviation for projection onto the right coordinate of a path class. -/
/-
**Path.Homotopic.projRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Path.Homotopic`。
形式化陈述：projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁
.2 c₂.2
参数：p : Path.Homotopic.Quotient c₁ c₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)

--- 原说明 ---
Abbreviation for projection onto the right coordinate of a path class.
-/
abbrev projRight (p : Path.Homotopic.Quotient c₁ c₂) : Path.Homotopic.Quotient c₁.2 c₂.2 :=
  p.map ⟨_, continuous_snd⟩

/-- Lemmas showing projection is the inverse of product. -/
@[simp]
/-
**Path.Homotopic.projLeft_prod** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：projLeft_prod : projLeft (prod q₁ q₂) = q₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind₂`：∀ {X : Type u} [inst : TopologicalSpace X]
 {Y : Type u_1} [inst_1 : TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}   {motive 
: Path.Homotopic.Q…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopic.projLeft.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] {c₁ c₂ : α × β}   (p : Path.Homo
topic.Quotient c₁ …
· 使用定理 `Path.Homotopic.prod_lift`：prod_lift : prod (Quotient.mk p₁) (Quotient.mk
 p₂) = Quotient.mk (p₁.prod p₂)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.Homotopic.Quotient.mk_map`：mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) :
 mk (P₀.map f.continuous) = map (mk P₀) f

--- 原说明 ---
Lemmas showing projection is the inverse of product.
-/
theorem projLeft_prod : projLeft (prod q₁ q₂) = q₁ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projLeft, prod_lift, ← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
/-
**Path.Homotopic.projRight_prod** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：projRight_prod : projRight (prod q₁ q₂) = q₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind₂`：∀ {X : Type u} [inst : TopologicalSpace X]
 {Y : Type u_1} [inst_1 : TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}   {motive 
: Path.Homotopic.Q…
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopic.projRight.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : T
opologicalSpace α] [inst_1 : TopologicalSpace β] {c₁ c₂ : α × β}   (p : Path.Hom
otopic.Quotient c₁ …
· 使用定理 `Path.Homotopic.prod_lift`：prod_lift : prod (Quotient.mk p₁) (Quotient.mk
 p₂) = Quotient.mk (p₁.prod p₂)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.Homotopic.Quotient.mk_map`：mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) :
 mk (P₀.map f.continuous) = map (mk P₀) f
-/
theorem projRight_prod : projRight (prod q₁ q₂) = q₂ := by
  induction q₁, q₂ using Path.Homotopic.Quotient.ind₂
  rw [projRight, prod_lift, ← Path.Homotopic.Quotient.mk_map]
  congr

@[simp]
/-
**Path.Homotopic.prod_projLeft_projRight** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotop
ic`。
形式化陈述：prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) : 
prod (projLeft p) (projRight p) = p
参数：p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem prod_projLeft_projRight (p : Path.Homotopic.Quotient (a₁, b₁) (a₂, b₂)) :
    prod (projLeft p) (projRight p) = p := by
  induction p using Path.Homotopic.Quotient.ind
  simp only [projLeft, projRight, ← Path.Homotopic.Quotient.mk_map]
  congr

end Prod

end Path.Homotopic

