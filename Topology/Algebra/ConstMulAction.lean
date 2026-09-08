/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.ULift
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Support

/-!
# Monoid actions continuous in the second variable

In this file we define class `ContinuousConstSMul`. We say `ContinuousConstSMul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`ContinuousSMul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `ContinuousConstSMul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `ProperlyDiscontinuousSMul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `Homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.
* `Homeomorph.smulOfNeZero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `Homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.

## Main results

* `isOpenMap_quotient_mk'_mul` : The quotient map by a group action is open.
* `t2Space_of_properlyDiscontinuousSMul_of_t2Space` : The quotient by a discontinuous group
  action of a locally compact T₂ space is T₂.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/

@[expose] public section

assert_not_exists IsOrderedRing

open Topology Pointwise Filter Set TopologicalSpace

/-- Class `ContinuousConstSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.

Note that both `ContinuousConstSMul α α` and `ContinuousConstSMul αᵐᵒᵖ α` are
weaker versions of `ContinuousMul α`. -/
/-
**ContinuousConstSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Γ : Type u_1) → (T : Type u_2) → [TopologicalSpace T] → [SMul Γ T] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ContinuousConstSMul Γ T` says that the scalar multiplication `(•) : Γ → T
 → T`
is continuous in the second argument. We use the same class for all kinds of mul
tiplicative
actions, including (semi)modules and algebras.

Note that both `ContinuousConstSMul α α` and `ContinuousConstSMul αᵐᵒᵖ α` are
weaker versions of `ContinuousMul α`.
-/
class ContinuousConstSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x

/-- Class `ContinuousConstVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.

Note that both `ContinuousConstVAdd α α` and `ContinuousConstVAdd αᵐᵒᵖ α` are
weaker versions of `ContinuousVAdd α`. -/
/-
**ContinuousConstVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Γ : Type u_1) → (T : Type u_2) → [TopologicalSpace T] → [VAdd Γ T] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ContinuousConstVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of add
itive actions,
including (semi)modules and algebras.

Note that both `ContinuousConstVAdd α α` and `ContinuousConstVAdd αᵐᵒᵖ α` are
weaker versions of `ContinuousVAdd α`.
-/
class ContinuousConstVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] : Prop where
  /-- The additive action `(+ᵥ) : Γ → T → T` is continuous in the second argument. -/
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)
export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type*}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousConstSMul (ULift M) α := ⟨fun γ ↦ continuous_const_smul (ULift.down γ)⟩

@[to_additive]
/-
**Filter.Tendsto.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_smul {f : β -> α} {l : Filter β} {a : α} (hf : Tendst
o f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a))
参数：hf : Tendsto f l (𝓝 a)；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
    (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).tendsto _).comp hf

variable [TopologicalSpace β] {g : β → α} {b : β} {s : Set β}

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (c • g) s b :=
  hg.const_smul c

@[to_fun (attr := to_additive (attr := fun_prop))]
nonrec theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) :
    ContinuousAt (c • g) b :=
  hg.const_smul c

@[to_fun (attr := to_additive (attr := fun_prop))]
/-
**ContinuousOn.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) : ContinuousOn (c 
• g) s
参数：hg : ContinuousOn g s；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type
 u_3} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α] 
  [inst_3 : Topolog…
-/
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) :
    ContinuousOn (c • g) s := fun x hx => (hg x hx).const_smul c

@[to_fun (attr := to_additive (attr := continuity, fun_prop))]
/-
**Continuous.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.const_smul (hg : Continuous g) (c : M) : Continuous (c • g)
参数：hg : Continuous g；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous (c • g) :=
  (continuous_const_smul _).comp hg

/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive /-- If an additive action is central, then its right action is continuous when its
left action is. -/]
/-
**ContinuousConstSMul.op** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : ContinuousCon
stSMul Mᵐᵒᵖ α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] :
    ContinuousConstSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩

@[to_additive]
/-
**MulOpposite.continuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MulOpposite.continuous_op`：continuous_op : Continuous (op : M -> Mᵐᵒᵖ)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `MulOpposite.continuous_unop`：continuous_unop : Continuous (unop : Mᵐᵒᵖ -
> M)
-/
instance MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ :=
  ⟨fun c => MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.const_smul c⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousConstSMul M αᵒᵈ := ‹ContinuousConstSMul M α›

@[to_additive]
/-
**OrderDual.continuousConstSMul'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α :=
  ‹ContinuousConstSMul M α›

@[to_additive]
/-
**Prod.continuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.continuousConstSMul [SMul M β] [ContinuousConstSMul M β] : Continuous
ConstSMul M (α × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
instance Prod.continuousConstSMul [SMul M β] [ContinuousConstSMul M β] :
    ContinuousConstSMul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prodMk (continuous_snd.const_smul _)⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {γ : ι → Type*} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousConstSMul M (γ i)] : ContinuousConstSMul M (∀ i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

@[to_additive]
/-
**IsCompact.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul 
α β] (a : α) {s : Set β} (hs : IsCompact s) : IsCompact (a • s)
参数：a : α；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
    {s : Set β} (hs : IsCompact s) : IsCompact (a • s) :=
  hs.image (continuous_id.const_smul a)

@[to_additive]
/-
**Specializes.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Specializes.const_smul {x y : α} (h : x ⤳ y) (c : M) : (c • x) ⤳ (c • y)
参数：h : x ⤳ y；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem Specializes.const_smul {x y : α} (h : x ⤳ y) (c : M) : (c • x) ⤳ (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
/-
**Inseparable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Inseparable.const_smul {x y : α} (h : Inseparable x y) (c : M) : Inseparab
le (c • x) (c • y)
参数：h : Inseparable x y；c : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.map`：map (h : x ~ᵢ y) (hf : Continuous f) : f x ~ᵢ f y
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem Inseparable.const_smul {x y : α} (h : Inseparable x y) (c : M) :
    Inseparable (c • x) (c • y) :=
  h.map (continuous_const_smul c)

@[to_additive]
/-
**Topology.IsInducing.continuousConstSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousConstSMul {N β : Type*} [SMul N β] [Topologi
calSpace β] {g : β -> α} (hg : IsInducing g) (f : N -> M) (hf : forall {c : N} {
x : β}, g (c • x) = f c • g x) : ContinuousConstSMul N β where continuous_const_
smul c
参数：hg : IsInducing g；f : N -> M；hf : forall {c : N} {x : β}, g (c • x) = f c • g
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem Topology.IsInducing.continuousConstSMul {N β : Type*} [SMul N β] [TopologicalSpace β]
    {g : β → α} (hg : IsInducing g) (f : N → M) (hf : ∀ {c : N} {x : β}, g (c • x) = f c • g x) :
    ContinuousConstSMul N β where
  continuous_const_smul c := by
    simpa only [Function.comp_def, hf, hg.continuous_iff] using hg.continuous.fun_const_smul (f c)

@[to_additive]
/-
**smul_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closure_subset (c : M) (s : Set α) : c • closure s subseteq closure (
c • s)
参数：c : M；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set X}   {t : Set Y}, Set
.MapsTo …
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem smul_closure_subset (c : M) (s : Set α) : c • closure s ⊆ closure (c • s) :=
  ((Set.mapsTo_image _ _).closure <| continuous_const_smul c).image_subset

@[to_additive]
/-
**set_smul_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_smul_closure_subset (s : Set M) (t : Set α) : s • closure t subseteq c
losure (s • t)
参数：s : Set M；t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_closure_subset`：smul_closure_subset (c : M) (s : Set α) : c • closu
re s subseteq closure (c • s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
theorem set_smul_closure_subset (s : Set M) (t : Set α) : s • closure t ⊆ closure (s • t) := by
  simp only [← iUnion_smul_set]
  exact iUnion₂_subset fun c hc ↦ (smul_closure_subset c t).trans <| closure_mono <|
    subset_biUnion_of_mem (u := (· • t)) hc
/-
**isClosed_setOfPred_map_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_map_smul {N : Type*} (α β) [SMul M α] [SMul N β] [Topol
ogicalSpace β] [T2Space β] [ContinuousConstSMul N β] (σ : M -> N) : IsClosed { f
 : α -> β | forall c x, f (c • x) = σ c • f x }
参数：α β；σ : M -> N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
-/
theorem isClosed_setOfPred_map_smul {N : Type*} (α β) [SMul M α] [SMul N β]
    [TopologicalSpace β] [T2Space β] [ContinuousConstSMul N β] (σ : M → N) :
    IsClosed { f : α → β | ∀ c x, f (c • x) = σ c • f x } := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun c => isClosed_iInter fun x =>
    isClosed_eq (continuous_apply _) ((continuous_apply _).const_smul _)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_map_smul := isClosed_setOfPred_map_smul

end SMul

section SMulZeroClass

variable [TopologicalSpace α] [Zero α] [SMulZeroClass M α] [ContinuousConstSMul M α]

/-
**Filter.Tendsto.const_smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : Zero α]   [inst_2 : SMulZeroClass M α] [ContinuousConstSMul M α] {g :
 β → α} {l : Filter β} (c : M),   Filter.Tendsto g l (nhds 0) → Filter.Tendsto (
fun x => c • g x) l (nhds 0)
参数：c : M；nhds 0；fun x => c • g x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
protected theorem Filter.Tendsto.const_smul_zero {g : β → α} {l : Filter β}
    (c : M) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ c • g x) l (𝓝 0) :=
  smul_zero c (A := α) ▸ hg.const_smul c

end SMulZeroClass

section Monoid

variable [TopologicalSpace α]
variable [Monoid M] [MulAction M α] [ContinuousConstSMul M α]

@[to_additive]
/-
**Units.continuousConstSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Units.continuousConstSMul : ContinuousConstSMul Mˣ α where continuous_cons
t_smul m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
instance Units.continuousConstSMul : ContinuousConstSMul Mˣ α where
  continuous_const_smul m := continuous_const_smul (m : M)

@[to_additive]
/-
**smul_closure_orbit_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_closure_orbit_subset (c : M) (x : α) : c • closure (MulAction.orbit M
 x) subseteq closure (MulAction.orbit M x)
参数：c : M；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_closure_subset`：smul_closure_subset (c : M) (s : Set α) : c • closu
re s subseteq closure (c • s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `MulAction.smul_orbit_subset`：smul_orbit_subset (m : M) (a : α) : m • orb
it M a subseteq orbit M a
-/
theorem smul_closure_orbit_subset (c : M) (x : α) :
    c • closure (MulAction.orbit M x) ⊆ closure (MulAction.orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _

end Monoid

section Group

variable {G : Type*} [TopologicalSpace α] [Group G] [MulAction G α] [ContinuousConstSMul G α]

@[to_additive]
/-
**tendsto_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_smul_iff {f : β -> α} {l : Filter β} {a : α} (c : G) : Tends
to (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a)
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
-/
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

@[to_additive]
/-
**continuousWithinAt_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_const_smul_iff (c : G) : ContinuousWithinAt (fun x => c
 • f x) s b ↔ ContinuousWithinAt f s b
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_smul_iff`：tendsto_const_smul_iff {f : β -> α} {l : Filter 
β} {a : α} (c : G) : Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 
a)
-/
theorem continuousWithinAt_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c

@[to_additive]
/-
**continuousOn_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_const_smul_iff (c : G) : ContinuousOn (fun x => c • f x) s ↔ 
ContinuousOn f s
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `continuousWithinAt_const_smul_iff`：continuousWithinAt_const_smul_iff (c 
: G) : ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b
-/
theorem continuousOn_const_smul_iff (c : G) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congr fun _ _ => continuousWithinAt_const_smul_iff c

@[to_additive]
/-
**continuousAt_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_const_smul_iff (c : G) : ContinuousAt (fun x => c • f x) b ↔ 
ContinuousAt f b
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_smul_iff`：tendsto_const_smul_iff {f : β -> α} {l : Filter 
β} {a : α} (c : G) : Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 
a)
-/
theorem continuousAt_const_smul_iff (c : G) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c

@[to_additive]
/-
**continuous_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Contin
uous f
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]

/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive (attr := simps!)]
/-
**Homeomorph.smul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Homeomorph.smul (γ : G) : α ≃ₜ α where toEquiv
参数：γ : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism given by scalar multiplication by a given element of a group `
Γ` acting on
  `T` is a homeomorphism from `T` to itself.
-/
def Homeomorph.smul (γ : G) : α ≃ₜ α where
  toEquiv := MulAction.toPerm γ

@[to_additive]
/-
**Homeomorph.smul_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.smul_symm {g : G} : (Homeomorph.smul (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.ext_iff`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] {h h' : X ≃ₜ Y},   h = h' ↔ ∀ (x : X), h x
 = h' x
· 使用定理 `Homeomorph.smul_symm_apply`：∀ {α : Type u_2} {G : Type u_4} [inst : Topo
logicalSpace α] [inst_1 : Group G] [inst_2 : MulAction G α]   [inst_3 : Continuo
usConstSMul G α]…
-/
lemma Homeomorph.smul_symm {g : G} : (Homeomorph.smul (α := α) g).symm = Homeomorph.smul g⁻¹ :=
  Homeomorph.ext_iff.mpr <| smul_symm_apply g

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

@[to_additive]
/-
**isHomeomorph_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isHomeomorph_smul (c : G) : IsHomeomorph fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem isHomeomorph_smul (c : G) : IsHomeomorph fun x : α ↦ c • x :=
  (Homeomorph.smul c).isHomeomorph

@[to_additive]
/-
**isOpenMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).isOpenMap

@[to_additive]
/-
**IsOpen.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s)
参数：hs : IsOpen s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_smul`：isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x
-/
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  isOpenMap_smul c s hs

@[to_additive]
/-
**isClosedMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
theorem isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).isClosedMap

@[to_additive]
/-
**IsClosed.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s)
参数：hs : IsClosed s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosedMap_smul`：isClosedMap_smul (c : G) : IsClosedMap fun x : α => c 
• x
-/
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  isClosedMap_smul c s hs

@[to_additive]
/-
**closure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s :=
  ((Homeomorph.smul c).image_closure s).symm

@[to_additive]
/-
**Dense.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s)
参数：c : G；hs : Dense s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `closure_smul`：closure_smul (c : G) (s : Set α) : closure (c • s) = c • c
losure s
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
-/
theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
  rw [dense_iff_closure_eq] at hs ⊢; rw [closure_smul, hs, smul_set_univ]

@[to_additive]
/-
**interior_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_interior`：image_interior (h : X ≃ₜ Y) (s : Set X) : h '
' interior s = interior (h '' s)
-/
theorem interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smul c).image_interior s).symm

open scoped Pointwise in
@[to_additive]
/-
**nhds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhds_smul (c : G) (x : α) : 𝓝 (c • x) = c • 𝓝 x
参数：c : G；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
lemma nhds_smul (c : G) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
  (Homeomorph.smul c).map_nhds_eq x |>.symm

open scoped Pointwise in
@[to_additive]
/-
**punctured_nhds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：punctured_nhds_smul (c : G) (x : α) : 𝓝[!=] (c • x) = c • 𝓝[!=] x
参数：c : G；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_punctured_nhds_eq`：map_punctured_nhds_eq (h : X ≃ₜ Y) (x 
: X) : map h (𝓝[!=] x) = 𝓝[!=] (h x)
-/
lemma punctured_nhds_smul (c : G) (x : α) : 𝓝[≠] (c • x) = c • 𝓝[≠] x :=
  (Homeomorph.smul c).map_punctured_nhds_eq x |>.symm

@[to_additive]
/-
**IsOpen.smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen t) : IsOpen (s • t)
参数：ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iUnion_smul_set`：iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s,
 a • t = s • t
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `IsOpen.smul`：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c
 • s)
-/
theorem IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen t) : IsOpen (s • t) := by
  rw [← iUnion_smul_set]
  exact isOpen_biUnion fun a _ => ht.smul _

@[to_additive]
/-
**subset_interior_smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_interior_smul_right {s : Set G} {t : Set α} : s • interior t subset
eq interior (s • t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用引理 `Set.smul_subset_smul_left`：smul_subset_smul_left : t₁ subseteq t₂ -> s •
 t₁ subseteq s • t₂
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `IsOpen.smul_left`：IsOpen.smul_left {s : Set G} {t : Set α} (ht : IsOpen 
t) : IsOpen (s • t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
-/
theorem subset_interior_smul_right {s : Set G} {t : Set α} : s • interior t ⊆ interior (s • t) :=
  interior_maximal (Set.smul_subset_smul_left interior_subset) isOpen_interior.smul_left

@[to_additive (attr := simp)]
/-
**smul_mem_nhds_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : α} : g • t in 𝓝 (g • a) ↔ 
t in 𝓝 a
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topolo
gy.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : α} : g • t ∈ 𝓝 (g • a) ↔ t ∈ 𝓝 a :=
  (Homeomorph.smul g).isOpenEmbedding.image_mem_nhds

@[to_additive] alias ⟨_, smul_mem_nhds_smul⟩ := smul_mem_nhds_smul_iff

@[to_additive (attr := simp)]
/-
**smul_mem_nhds_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mem_nhds_self [TopologicalSpace G] [ContinuousConstSMul G G] {g : G} 
{s : Set G} : g • s in 𝓝 g ↔ s in 𝓝 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_mem_nhds_smul_iff`：smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : 
α} : g • t in 𝓝 (g • a) ↔ t in 𝓝 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_mem_nhds_self [TopologicalSpace G] [ContinuousConstSMul G G] {g : G} {s : Set G} :
    g • s ∈ 𝓝 g ↔ s ∈ 𝓝 1 := by
  rw [← smul_mem_nhds_smul_iff g⁻¹]; simp

namespace MulAction.IsPretransitive

variable (G)

@[to_additive]
/-
**MulAction.IsPretransitive.t1Space_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulAction.IsP
retransitive`。
形式化陈述：t1Space_iff (x : α) [IsPretransitive G α] : T1Space α ↔ IsClosed {x}
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `IsClosed.smul`：IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsC
losed (c • s)
-/
lemma t1Space_iff (x : α) [IsPretransitive G α] :
    T1Space α ↔ IsClosed {x} := by
  refine ⟨fun H ↦ isClosed_singleton, fun hx ↦ ⟨fun y ↦ ?_⟩⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton, image_smul]
  exact hx.smul _

@[to_additive]
/-
**MulAction.IsPretransitive.discreteTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulA
ction.IsPretransitive`。
形式化陈述：discreteTopology_iff (x : α) [IsPretransitive G α] : DiscreteTopology α ↔ 
IsOpen {x}
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.image_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t : S
et β} {a : α}, (fun x => a • x) '' t = a • t
· 使用定理 `IsOpen.smul`：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c
 • s)
-/
lemma discreteTopology_iff (x : α) [IsPretransitive G α] :
    DiscreteTopology α ↔ IsOpen {x} := by
  rw [discreteTopology_iff_isOpen_singleton]
  refine ⟨fun H ↦ H _, fun hx y ↦ ?_⟩
  rcases MulAction.exists_smul_eq G x y with ⟨g, rfl⟩
  rw [← image_singleton, image_smul]
  exact hx.smul _

end MulAction.IsPretransitive

end Group

section GroupWithZero

variable {G₀ : Type*} [TopologicalSpace α] [GroupWithZero G₀] [MulAction G₀ α]
  [ContinuousConstSMul G₀ α]

/-
**tendsto_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_smul_iff {f : β -> α} {l : Filter β} {a : α} (c : G) : Tends
to (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a)
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
-/
theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}
/-
**continuousWithinAt_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_const_smul_iff (c : G) : ContinuousWithinAt (fun x => c
 • f x) s b ↔ ContinuousWithinAt f s b
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_smul_iff`：tendsto_const_smul_iff {f : β -> α} {l : Filter 
β} {a : α} (c : G) : Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 
a)
-/
theorem continuousWithinAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)
/-
**continuousOn_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_const_smul_iff (c : G) : ContinuousOn (fun x => c • f x) s ↔ 
ContinuousOn f s
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `continuousWithinAt_const_smul_iff`：continuousWithinAt_const_smul_iff (c 
: G) : ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b
-/
theorem continuousOn_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff (Units.mk0 c hc)
/-
**continuousAt_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_const_smul_iff (c : G) : ContinuousAt (fun x => c • f x) b ↔ 
ContinuousAt f b
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_smul_iff`：tendsto_const_smul_iff {f : β -> α} {l : Filter 
β} {a : α} (c : G) : Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 
a)
-/
theorem continuousAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff (Units.mk0 c hc)
/-
**continuous_const_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Contin
uous f
参数：c : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
@[simps! -fullyApplied apply]
/-
**Homeomorph.smulOfNeZero** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{α : Type u_2} →   {G₀ : Type u_4} →     [inst : TopologicalSpace α] →    
   [inst_1 : GroupWithZero G₀] → [inst_2 : MulAction G₀ α] → [ContinuousConstSMu
l G₀ α] → (c : G₀) → c ≠ 0 → α ≃ₜ α
参数：c : G₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by a non-zero element of a group with zero acting on `α` i
s a
homeomorphism from `α` onto itself.
-/
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)

@[simp]
/-
**Homeomorph.smulOfNeZero_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.smulOfNeZero_symm_apply {c : G₀} (hc : c != 0) : ⇑(Homeomorph.s
mulOfNeZero c hc).symm = (c⁻¹ • · : α -> α)
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Homeomorph.smulOfNeZero_symm_apply {c : G₀} (hc : c ≠ 0) :
    ⇑(Homeomorph.smulOfNeZero c hc).symm = (c⁻¹ • · : α → α) :=
  rfl
/-
**isHomeomorph_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isHomeomorph_smul (c : G) : IsHomeomorph fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
theorem isHomeomorph_smul₀ {c : G₀} (hc : c ≠ 0) : IsHomeomorph fun x : α ↦ c • x :=
  (Homeomorph.smulOfNeZero c hc).isHomeomorph
/-
**isOpenMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isOpenMap
/-
**IsOpen.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s)
参数：hs : IsOpen s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_smul`：isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x
-/
theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  isOpenMap_smul₀ hc s hs
/-
**interior_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_interior`：image_interior (h : X ≃ₜ Y) (s : Set X) : h '
' interior s = interior (h '' s)
-/
theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm
/-
**closure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem closure_smul₀' {c : G₀} (hc : c ≠ 0) (s : Set α) :
    closure (c • s) = c • closure s :=
  ((Homeomorph.smulOfNeZero c hc).image_closure s).symm
/-
**closure_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s
参数：c : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
    [ContinuousConstSMul G₀ E] (c : G₀) (s : Set E) : closure (c • s) = c • closure s := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact closure_smul₀' hc s

open scoped Pointwise in
/-
**nhds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nhds_smul (c : G) (x : α) : 𝓝 (c • x) = c • 𝓝 x
参数：c : G；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
lemma nhds_smul₀ {c : G₀} (hc : c ≠ 0) (x : α) : 𝓝 (c • x) = c • 𝓝 x :=
  nhds_smul (Units.mk0 c hc) x

open scoped Pointwise in
/-
**punctured_nhds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：punctured_nhds_smul (c : G) (x : α) : 𝓝[!=] (c • x) = c • 𝓝[!=] x
参数：c : G；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_punctured_nhds_eq`：map_punctured_nhds_eq (h : X ≃ₜ Y) (x 
: X) : map h (𝓝[!=] x) = 𝓝[!=] (h x)
-/
lemma punctured_nhds_smul₀ {c : G₀} (hc : c ≠ 0) (x : α) : 𝓝[≠] (c • x) = c • 𝓝[≠] x :=
  punctured_nhds_smul (Units.mk0 c hc) x

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimension`. -/
/-
**isClosedMap_smul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_smul_of_ne_zero {c : G₀} (hc : c != 0) : IsClosedMap fun x : α
 => c • x
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h

--- 原说明 ---
`smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space 
over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimens
ion`.
-/
theorem isClosedMap_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).isClosedMap
/-
**IsClosed.smul_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c !=
 0) : IsClosed (c • s)
参数：hs : IsClosed s；hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosedMap_smul_of_ne_zero`：isClosedMap_smul_of_ne_zero {c : G₀} (hc : 
c != 0) : IsClosedMap fun x : α => c • x
-/
theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c ≠ 0) :
    IsClosed (c • s) :=
  isClosedMap_smul_of_ne_zero hc s hs

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimension`. -/
/-
**isClosedMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h

--- 原说明 ---
`smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space 
over a complete
normed field) is `isClosedMap_smul_left` in `Analysis.Normed.Module.FiniteDimens
ion`.
-/
theorem isClosedMap_smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) : IsClosedMap fun x : E => c • x := by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).isClosedMap
/-
**IsClosed.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s)
参数：hs : IsClosed s；c : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosedMap_smul`：isClosedMap_smul (c : G) : IsClosedMap fun x : α => c 
• x
-/
theorem IsClosed.smul₀ {E : Type*} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E]
    [T1Space E] [ContinuousConstSMul G₀ E] (c : G₀) {s : Set E} (hs : IsClosed s) :
    IsClosed (c • s) :=
  isClosedMap_smul₀ c s hs
/-
**HasCompactMulSupport.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.comp_smul {β : Type*} [One β] {f : α -> β} (h : HasCo
mpactMulSupport f) {c : G₀} (hc : c != 0) : HasCompactMulSupport fun x => f (c •
 x)
参数：h : HasCompactMulSupport f；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.comp_homeomorph`：HasCompactMulSupport.comp_homeomor
ph {M} [One M] {f : Y -> M} (hf : HasCompactMulSupport f) (φ : X ≃ₜ Y) : HasComp
actMulSupport (f ∘ φ)
-/
theorem HasCompactMulSupport.comp_smul {β : Type*} [One β] {f : α → β} (h : HasCompactMulSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactMulSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)
/-
**HasCompactSupport.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.comp_smul {β : Type*} [Zero β] {f : α -> β} (h : HasComp
actSupport f) {c : G₀} (hc : c != 0) : HasCompactSupport fun x => f (c • x)
参数：h : HasCompactSupport f；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.comp_homeomorph`：∀ {X : Type u_9} {Y : Type u_10} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {M : Type u_11}   [inst_2 
: Zero M] {f : Y → M}, …
-/
theorem HasCompactSupport.comp_smul {β : Type*} [Zero β] {f : α → β} (h : HasCompactSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)

end GroupWithZero

namespace IsUnit

variable [Monoid M] [TopologicalSpace α] [MulAction M α] [ContinuousConstSMul M α]

nonrec theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff hc.unit

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

nonrec theorem continuousWithinAt_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  continuousWithinAt_const_smul_iff hc.unit

nonrec theorem continuousOn_const_smul_iff (hc : IsUnit c) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff hc.unit

nonrec theorem continuousAt_const_smul_iff (hc : IsUnit c) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff hc.unit

nonrec theorem continuous_const_smul_iff (hc : IsUnit c) :
    (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff hc.unit

nonrec theorem isHomeomorph_smul (hc : IsUnit c) : IsHomeomorph fun x : α ↦ c • x :=
  isHomeomorph_smul hc.unit

nonrec theorem isOpenMap_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  isOpenMap_smul hc.unit

nonrec theorem isClosedMap_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  isClosedMap_smul hc.unit

nonrec theorem smul_mem_nhds_smul_iff (hc : IsUnit c) {s : Set α} {a : α} :
    c • s ∈ 𝓝 (c • a) ↔ s ∈ 𝓝 a :=
  smul_mem_nhds_smul_iff hc.unit

/-
**IsUnit.isQuotientMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isQuotientMap_smul {S β} [SMul S M] [SMul S α] [IsScalarTower S M α] [SMul
 S β] (f : α ->[S] β) [TopologicalSpace β] (hf : IsQuotientMap f) (c : S) (hc : 
IsUnit (c • 1 : M)) : IsQuotientMap (c • · : β -> β)
参数：f : α ->[S] β；hf : IsQuotientMap f；c : S；hc : IsUnit (c • 1 : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.of_comp_isQuotientMap`：∀ {X : Type u_1} {Y : Type
 u_2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst
_1 : TopologicalSpace Y] [inst_2 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
· 使用引理 `IsHomeomorph.isQuotientMap`：isQuotientMap : IsQuotientMap f
· 使用定理 `IsUnit.isHomeomorph_smul`：∀ {M : Type u_1} {α : Type u_2} [inst : Monoid
 M] [inst_1 : TopologicalSpace α] [inst_2 : MulAction M α]   [ContinuousConstSMu
l M α] {c : M}…
-/
theorem isQuotientMap_smul {S β} [SMul S M] [SMul S α] [IsScalarTower S M α]
    [SMul S β] (f : α →[S] β) [TopologicalSpace β] (hf : IsQuotientMap f)
    (c : S) (hc : IsUnit (c • 1 : M)) : IsQuotientMap (c • · : β → β) :=
  hf.of_comp_isQuotientMap <| by convert! hf.comp hc.isHomeomorph_smul.isQuotientMap; ext; simp
/-
**IsUnit.isQuotientMap_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isQuotientMap_nsmul {M β} [Semiring M] [AddCommMonoid α] [Module M α] [Con
tinuousConstSMul M α] [AddMonoid β] (f : α ->+ β) [TopologicalSpace β] (hf : IsQ
uotientMap f) (n : Nat) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β -> β)
参数：f : α ->+ β；hf : IsQuotientMap f；n : Nat；hc : IsUnit (n : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.isQuotientMap_smul`：isQuotientMap_smul {S β} [SMul S M] [SMul S α
] [IsScalarTower S M α] [SMul S β] (f : α ->[S] β) [TopologicalSpace β] (hf : Is
QuotientMap f) …
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
-/
theorem isQuotientMap_nsmul {M β} [Semiring M] [AddCommMonoid α] [Module M α]
    [ContinuousConstSMul M α] [AddMonoid β] (f : α →+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : ℕ) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β → β) :=
  isQuotientMap_smul (M := M) ⟨f, map_nsmul f⟩ hf _ <| by rwa [nsmul_one]
/-
**IsUnit.isQuotientMap_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isQuotientMap_zsmul {M β} [Ring M] [AddCommGroup α] [Module M α] [Continuo
usConstSMul M α] [AddGroup β] (f : α ->+ β) [TopologicalSpace β] (hf : IsQuotien
tMap f) (n : Int) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β -> β)
参数：f : α ->+ β；hf : IsQuotientMap f；n : Int；hc : IsUnit (n : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.isQuotientMap_smul`：isQuotientMap_smul {S β} [SMul S M] [SMul S α
] [IsScalarTower S M α] [SMul S β] (f : α ->[S] β) [TopologicalSpace β] (hf : Is
QuotientMap f) …
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
-/
theorem isQuotientMap_zsmul {M β} [Ring M] [AddCommGroup α] [Module M α]
    [ContinuousConstSMul M α] [AddGroup β] (f : α →+ β) [TopologicalSpace β]
    (hf : IsQuotientMap f) (n : ℤ) (hc : IsUnit (n : M)) : IsQuotientMap (n • · : β → β) :=
  isQuotientMap_smul (M := M) ⟨f, map_zsmul f⟩ hf _ <| by rwa [zsmul_one n]

end IsUnit

/-- Class `ProperlyDiscontinuousSMul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
/-
**ProperlyDiscontinuousSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Γ : Type u_4) → (T : Type u_5) → [TopologicalSpace T] → [SMul Γ T] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ProperlyDiscontinuousSMul Γ T` says that the scalar multiplication `(•) :
 Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, 
only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSMul (Γ : Type*) (T : Type*) [TopologicalSpace T] [SMul Γ T] :
    Prop where
  /-- Given two compact sets `K` and `L`, `γ • K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | ((γ • ·) '' K ∩ L).Nonempty }

/-- Class `ProperlyDiscontinuousVAdd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
/-
**ProperlyDiscontinuousVAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Γ : Type u_4) → (T : Type u_5) → [TopologicalSpace T] → [VAdd Γ T] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Class `ProperlyDiscontinuousVAdd Γ T` says that the additive action `(+ᵥ) : Γ → 
T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, 
only finitely many
`γ : Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVAdd (Γ : Type*) (T : Type*) [TopologicalSpace T] [VAdd Γ T] :
  Prop where
  /-- Given two compact sets `K` and `L`, `γ +ᵥ K ∩ L` is nonempty for finitely many `γ`. -/
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | ((γ +ᵥ ·) '' K ∩ L).Nonempty }

attribute [to_additive] ProperlyDiscontinuousSMul

export ProperlyDiscontinuousSMul (finite_disjoint_inter_image)
export ProperlyDiscontinuousVAdd (finite_disjoint_inter_image)

@[to_additive]
/-
**properlyDiscontinuousSMul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：properlyDiscontinuousSMul_iff [TopologicalSpace α] [SMul M α] : ProperlyDi
scontinuousSMul M α ↔ forall {K L : Set α}, IsCompact K -> IsCompact L -> {m : M
 | (m • K inter L).Nonempty}.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperlyDiscontinuousSMul.finite_disjoint_inter_image`：∀ {Γ : Type u_4} 
{T : Type u_5} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ProperlyD
iscontinuousSMul Γ T]   {K L : Set T}, IsCo…
-/
lemma properlyDiscontinuousSMul_iff [TopologicalSpace α] [SMul M α] :
    ProperlyDiscontinuousSMul M α ↔
      ∀ {K L : Set α}, IsCompact K → IsCompact L → {m : M | (m • K ∩ L).Nonempty}.Finite :=
  ⟨fun _ _ _ ↦ ProperlyDiscontinuousSMul.finite_disjoint_inter_image, .mk⟩

section

variable (Γ : Type*) {T : Type*}
variable [TopologicalSpace T] [SMul Γ T] [ProperlyDiscontinuousSMul Γ T] (x : T)

/-
**ProperlyDiscontinuousSMul.finite_stabilizer'** 是 Mathlib 中的一个定理，位于命名空间 `Proper
lyDiscontinuousSMul`。
形式化陈述：∀ (Γ : Type u_4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul
 Γ T] [ProperlyDiscontinuousSMul Γ T] (x : T),   {γ | γ • x = x}.Finite
参数：Γ : Type u_4；x : T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProperlyDiscontinuousSMul.finite_disjoint_inter_image`：∀ {Γ : Type u_4} 
{T : Type u_5} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ProperlyD
iscontinuousSMul Γ T]   {K L : Set T}, IsCo…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer' : {γ : Γ | γ • x = x}.Finite := by
  simp_rw [← mem_singleton_iff, ← singleton_inter_nonempty, ← image_singleton]
  exact finite_disjoint_inter_image isCompact_singleton isCompact_singleton

variable [T2Space T] [LocallyCompactSpace T] [ContinuousConstSMul Γ T] (x : T)
/-
**ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self** 是 Mathlib 中的一个定理，位于
命名空间 `ProperlyDiscontinuousSMul`。
形式化陈述：∀ (Γ : Type u_4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul
 Γ T] [ProperlyDiscontinuousSMul Γ T]   [T2Space T] [LocallyCompactSpace T] [Con
tinuousConstSMul Γ T] (x : T),   ∃ U ∈ nhds x, ∀ (γ : Γ), ((fun x => γ • x) '' U
 ∩ U).Nonempty → γ • x = x
参数：Γ : Type u_4；x : T；γ : Γ；(fun x => γ • x) '' U ∩ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `ProperlyDiscontinuousSMul.finite_disjoint_inter_image`：∀ {Γ : Type u_4} 
{T : Type u_5} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ProperlyD
iscontinuousSMul Γ T]   {K L : Set T}, IsCo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.iInter_mem`：iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] :
 (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `t2_separation_nhds`：t2_separation_nhds [T2Space X] {x y : X} (h : x != y
) : exists u v, u in 𝓝 x ∧ v in 𝓝 y ∧ Disjoint u v
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self :
    ∃ U ∈ 𝓝 x, ∀ γ : Γ, ((γ • ·) '' U ∩ U).Nonempty → γ • x = x := by
  obtain ⟨V, V_cpt, V_nhd⟩ := exists_compact_mem_nhds x
  let Γ₀ := {γ : Γ | ((γ • ·) '' V ∩ V).Nonempty ∧ γ • x ≠ x}
  have : Finite Γ₀ := (finite_disjoint_inter_image V_cpt V_cpt).subset fun _ ↦ And.left
  choose u v hu hv u_v_disjoint using fun γ : Γ₀ ↦ t2_separation_nhds γ.2.2
  refine ⟨V ∩ ⋂ γ : Γ₀, (γ.1 • ·) ⁻¹' u γ ∩ v γ, inter_mem V_nhd (iInter_mem.mpr fun γ ↦
    inter_mem ((continuous_const_smul _).continuousAt <| hu γ) (hv γ)), fun γ hγ ↦ ?_⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hγz⟩ := hγ
  by_contra h
  rw [mem_inter_iff, mem_iInter] at hz hγz
  let γ : Γ₀ := ⟨γ, ⟨_, ⟨z, hz.1, rfl⟩, hγz.1⟩, h⟩
  exact (u_v_disjoint γ).le_bot ⟨(hz.2 γ).1, (hγz.2 γ).2⟩
/-
**ProperlyDiscontinuousSMul.exists_nhds_disjoint_image** 是 Mathlib 中的一个定理，位于命名空间
 `ProperlyDiscontinuousSMul`。
形式化陈述：∀ (Γ : Type u_4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul
 Γ T] [ProperlyDiscontinuousSMul Γ T]   [T2Space T] [LocallyCompactSpace T] [Con
tinuousConstSMul Γ T] (x : T),   ∃ U ∈ nhds x, ∀ (γ : Γ), γ • x ≠ x → Disjoint (
(fun x => γ • x) '' U) U
参数：Γ : Type u_4；x : T；γ : Γ；(fun x => γ • x) '' U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self`：∀ (Γ : Type u_
4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul Γ T] [ProperlyDisco
ntinuousSMul Γ T]   [T2Space T] [LocallyCompac…
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.exists_nhds_disjoint_image :
    ∃ U ∈ 𝓝 x, ∀ γ : Γ, γ • x ≠ x → Disjoint ((γ • ·) '' U) U := by
  convert! exists_nhds_image_smul_eq_self Γ x using 4
  rw [← not_imp_not]
  simp [Set.not_disjoint_iff_nonempty_inter]

end

variable {Γ : Type*} [Group Γ] {T : Type*} [TopologicalSpace T] [MulAction Γ T]

/-- A finite group action is always properly discontinuous. -/
@[to_additive /-- A finite group action is always properly discontinuous. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite group action is always properly discontinuous.
-/
instance (priority := 100) Finite.to_properlyDiscontinuousSMul [Finite Γ] :
    ProperlyDiscontinuousSMul Γ T where finite_disjoint_inter_image _ _ := Set.toFinite _
/-
**ProperlyDiscontinuousSMul.finite_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `Properl
yDiscontinuousSMul`。
形式化陈述：∀ {Γ : Type u_4} [inst : Group Γ] {T : Type u_5} [inst_1 : TopologicalSpac
e T] [inst_2 : MulAction Γ T]   [ProperlyDiscontinuousSMul Γ T] (x : T), (↑(MulA
ction.stabilizer Γ x)).Finite
参数：x : T；↑(MulAction.stabilizer Γ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperlyDiscontinuousSMul.finite_stabilizer'`：∀ (Γ : Type u_4) {T : Type
 u_5} [inst : TopologicalSpace T] [inst_1 : SMul Γ T] [ProperlyDiscontinuousSMul
 Γ T] (x : T),   {γ | γ • x = x}.F…
-/
@[to_additive] lemma ProperlyDiscontinuousSMul.finite_stabilizer [ProperlyDiscontinuousSMul Γ T]
    (x : T) : (MulAction.stabilizer Γ x : Set Γ).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer' Γ x

/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive /-- The quotient map by a group action is open, i.e. the quotient by a group
action is an open quotient. -/]
/-
**isOpenMap_quotient_mk'_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {Γ : Type u_4} [inst : Group Γ] {T : Type u_5} [inst_1 : TopologicalSpac
e T] [inst_2 : MulAction Γ T]   [ContinuousConstSMul Γ T], IsOpenMap Quotient.mk
'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_coinduced`：isOpen_coinduced {t : TopologicalSpace α} {s : Set β} 
{f : α -> β} : IsOpen[t.coinduced f] s ↔ IsOpen (f ⁻¹' s)
· 使用定理 `MulAction.quotient_preimage_image_eq_union_mul`：quotient_preimage_image_
eq_union_mul (U : Set α) : letI
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `isOpenMap_smul`：isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x
-/
theorem isOpenMap_quotient_mk'_mul [ContinuousConstSMul Γ T] :
    letI := MulAction.orbitRel Γ T
    IsOpenMap (Quotient.mk' : T → Quotient (MulAction.orbitRel Γ T)) := fun U hU => by
  rw [isOpen_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_iUnion fun γ => isOpenMap_smul γ U hU

@[to_additive]
/-
**MulAction.isOpenQuotientMap_quotientMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.isOpenQuotientMap_quotientMk [ContinuousConstSMul Γ T] : IsOpenQ
uotientMap (Quotient.mk (MulAction.orbitRel Γ T))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `continuous_quot_mk`：continuous_quot_mk : Continuous (@Quot.mk X r)
· 使用定理 `isOpenMap_quotient_mk'_mul`：∀ {Γ : Type u_4} [inst : Group Γ] {T : Type 
u_5} [inst_1 : TopologicalSpace T] [inst_2 : MulAction Γ T]   [ContinuousConstSM
ul Γ T], IsOpenM…
-/
theorem MulAction.isOpenQuotientMap_quotientMk [ContinuousConstSMul Γ T] :
    IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel Γ T)) :=
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_quotient_mk'_mul⟩

/-- The quotient by a discontinuous group action of a locally compact T₂ space is T₂. -/
@[to_additive /-- The quotient by a discontinuous group action of a locally compact T₂
space is T₂. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) t2Space_of_properlyDiscontinuousSMul_of_t2Space [T2Space T]
    [LocallyCompactSpace T] [ContinuousConstSMul Γ T] [ProperlyDiscontinuousSMul Γ T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) := by
  let := MulAction.orbitRel Γ T
  set Q := Quotient (MulAction.orbitRel Γ T)
  rw [t2Space_iff_nhds]
  let f : T → Q := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  change ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), _
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotient.sound hxy.symm :)
  obtain ⟨K₀, hK₀, K₀_in⟩ := exists_compact_mem_nhds x₀
  obtain ⟨L₀, hL₀, L₀_in⟩ := exists_compact_mem_nhds y₀
  let bad_Γ_set := { γ : Γ | ((γ • ·) '' K₀ ∩ L₀).Nonempty }
  have bad_Γ_finite : bad_Γ_set.Finite := finite_disjoint_inter_image (Γ := Γ) hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, (γ • ·) ⁻¹' u γ
  let U₀ := U₀₀ ∩ K₀
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ
  let V₀ := V₀₀ ∩ L₀
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀) := by
    refine f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => ?_) K₀_in)
    exact (continuous_const_smul _).continuousAt (hu γ)
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((biInter_mem bad_Γ_finite).mpr fun γ _ => hv γ) L₀_in)
  refine ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 ?_⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases H : γ ∈ bad_Γ_set
  · exact fun h => (u_v_disjoint γ).le_bot ⟨mem_iInter₂.mp x_in_U₀₀ γ H, mem_iInter₂.mp h.1 γ H⟩
  · rintro ⟨-, h'⟩
    simp only [bad_Γ_set, image_smul, not_nonempty_iff_eq_empty, mem_ofPred_eq] at H
    exact eq_empty_iff_forall_notMem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩

/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive /-- The quotient of a second countable space by an additive group action is second
countable. -/]
/-
**ContinuousConstSMul.secondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T] [C
ontinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel 
Γ T))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Quotient.secondCountableTopology`：∀ {X : Type u_1} [ins
t : TopologicalSpace X] {S : Setoid X} [SecondCountableTopology X],   IsOpenMap 
Quotient.mk' → SecondCountableTopology …
· 使用定理 `isOpenMap_quotient_mk'_mul`：∀ {Γ : Type u_4} [inst : Group Γ] {T : Type 
u_5} [inst_1 : TopologicalSpace T] [inst_2 : MulAction Γ T]   [ContinuousConstSM
ul Γ T], IsOpenM…
-/
theorem ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T]
    [ContinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel Γ T)) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

section nhds

section MulAction

variable {G₀ : Type*} [GroupWithZero G₀] [MulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/-- Scalar multiplication by a nonzero scalar preserves neighborhoods. -/
/-
**smul_mem_nhds_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mem_nhds_smul_iff {t : Set α} (g : G) {a : α} : g • t in 𝓝 (g • a) ↔ 
t in 𝓝 a
参数：g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.image_mem_nhds`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topolo
gy.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h

--- 原说明 ---
Scalar multiplication by a nonzero scalar preserves neighborhoods.
-/
theorem smul_mem_nhds_smul_iff₀ {c : G₀} {s : Set α} {x : α} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x :=
  smul_mem_nhds_smul_iff (Units.mk0 c hc)

alias ⟨_, smul_mem_nhds_smul₀⟩ := smul_mem_nhds_smul_iff₀

end MulAction

section DistribMulAction

variable {G₀ : Type*} [GroupWithZero G₀] [AddMonoid α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/-
**set_smul_mem_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c != 0) : c • s in 𝓝
 (0 : α) ↔ s in 𝓝 (0 : α)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `smul_mem_nhds_smul_iff₀`：smul_mem_nhds_smul_iff₀ {c : G₀} {s : Set α} {x
 : α} (hc : c != 0) : c • s in 𝓝 (c • x : α) ↔ s in 𝓝 x
-/
theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) := by
  refine Iff.trans ?_ (smul_mem_nhds_smul_iff₀ hc)
  rw [smul_zero]

end DistribMulAction

end nhds

