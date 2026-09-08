/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# TendstoUniformlyOn on ordered spaces

We gather some results about `TendstoUniformlyOn f g K` on ordered spaces,
in particular bounding the values of `f` in terms of bounds on the limit `g`.

-/

public section

open Filter Function Finset Topology

variable {α ι : Type*}

section order

variable {β : Type*} [UniformSpace β] [AddGroup β] [IsUniformAddGroup β] [PartialOrder β]
  [OrderTopology β] [AddLeftMono β] [AddRightMono β]

variable {f : ι → α → β} {g : α → β} {K : Set α} {p : Filter ι}

/-- If a sequence of functions converges uniformly on a set to a function `g` which is bounded above
by a value `u`, then the sequence is strictly bounded by any `v` such that `u < v`. -/
/-
**TendstoUniformlyOn.eventually_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.eventually_forall_lt {u v : β} (huv : u < v) (hf : Tend
stoUniformlyOn f g p K) (hg : forall x in K, g x <= u) : forallᶠ i in p, forall 
x in K, f i x < v
参数：huv : u < v；hf : TendstoUniformlyOn f g p K；hg : forall x in K, g x <= u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_exists_mem`：eventually_iff_exists_mem {p : α -> Pr
op} {f : Filter α} : (forallᶠ x in f, p x) ↔ exists v in f, forall y in v, p y
· 使用定理 `uniformity_eq_comap_neg_add_nhds_zero`：∀ (Gₗ : Type u_2) [inst : Uniform
Space Gₗ] [inst_1 : AddGroup Gₗ] [IsLeftUniformAddGroup Gₗ],   uniformity Gₗ = F
ilter.comap (fun x => -x.1 …
· 使用定理 `IsUniformAddGroup.isLeftUniformAddGroup`：∀ (α : Type u_1) [inst : Unifor
mSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsLeftUniformAddGroup α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_gt'`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α]
 [OrderTopology α] (a : α), IsOpen {b | b < a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_neg_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a +
 (-a + b) = b
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d

--- 原说明 ---
If a sequence of functions converges uniformly on a set to a function `g` which 
is bounded above
by a value `u`, then the sequence is strictly bounded by any `v` such that `u < 
v`.
-/
lemma TendstoUniformlyOn.eventually_forall_lt {u v : β} (huv : u < v)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x < v := by
  simp only [tendstoUniformlyOn_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
    tendsto_iff_eventually, eventually_comap, Prod.forall] at *
  conv at hf => enter [2]; rw [eventually_iff_exists_mem]
  have hf2 := hf (fun x ↦ -x.1 + x.2 < -u + v) ⟨_, (isOpen_gt' (-u + v)).mem_nhds (by simp [huv]),
    fun y hy a b hab ↦ (hab.symm ▸ hy :)⟩
  filter_upwards [eventually_prod_principal_iff.mp hf2] with i hi x hx
  simpa using add_lt_add_of_le_of_lt (hg x hx) (hi x hx)
/-
**TendstoUniformlyOn.eventually_forall_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.eventually_forall_le {u v : β} (huv : u < v) (hf : Tend
stoUniformlyOn f g p K) (hg : forall x in K, g x <= u) : forallᶠ i in p, forall 
x in K, f i x <= v
参数：huv : u < v；hf : TendstoUniformlyOn f g p K；hg : forall x in K, g x <= u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `TendstoUniformlyOn.eventually_forall_lt`：TendstoUniformlyOn.eventually_f
orall_lt {u v : β} (huv : u < v) (hf : TendstoUniformlyOn f g p K) (hg : forall 
x in K, g x <= u) : forallᶠ i…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma TendstoUniformlyOn.eventually_forall_le {u v : β} (huv : u < v)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x ≤ v := by
  filter_upwards [hf.eventually_forall_lt huv hg] with i hi x hx using (hi x hx).le

end order

