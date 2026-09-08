/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Group.Torsor

/-!
# Asymptotic cone of a set

This file defines the asymptotic cone of a set in a topological affine space.

## Implementation details

The asymptotic cone of a set $A$ is usually defined as the set of points $v$ for which there exist
sequences $t_n > 0$ and $x_n \in A$ such that $t_n \to 0$ and $t_n x_n \to v$. We take a different
approach here using filters: we define the asymptotic cone of `s` as the set of vectors `v` such
that `∃ᶠ p in Filter.atTop • 𝓝 v, p ∈ s` holds.

## Main definitions

* `AffineSpace.asymptoticNhds`: the filter of neighborhoods at infinity in some direction.
* `asymptoticCone`: the asymptotic cone of a subset of a topological affine space.

## Main statements

* `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  closed convex set `s`, then every ray of direction `v` starting from `s` is contained in `s`.
* `Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone`: if `v` is in the asymptotic cone of a
  convex set `s`, then every ray of direction `v` starting from the interior of `s` is contained in
  `s`.
-/

@[expose] public section

open scoped Pointwise Topology
open Filter

section General

variable
  {k V P : Type*}
  [Field k] [LinearOrder k] [AddCommGroup V] [Module k V] [AddTorsor V P] [TopologicalSpace V]

namespace AffineSpace

variable (k P) in
/-- In a topological affine space `P` over `k`, `AffineSpace.asymptoticNhds k P v` is the filter of
neighborhoods at infinity in directions near `v`. In a topological vector space, this is the filter
`Filter.atTop • 𝓝 v`. To support affine spaces, the actual definition is different and should be
considered an implementation detail. Use `AffineSpace.asymptoticNhds_eq_smul` or
`AffineSpace.asymptoticNhds_eq_smul_vadd` for unfolding. -/
@[irreducible]
/-
**AffineSpace.asymptoticNhds** 是 Mathlib 中的一个定义，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds (v : V) : Filter P
参数：v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a topological affine space `P` over `k`, `AffineSpace.asymptoticNhds k P v` i
s the filter of
neighborhoods at infinity in directions near `v`. In a topological vector space,
 this is the filter
`Filter.atTop • 𝓝 v`. To support affine spaces, the actual definition is differe
nt and should be
considered an implementation detail. Use `AffineSpace.asymptoticNhds_eq_smul` or
`AffineSpace.asymptoticNhds_eq_smul_vadd` for unfolding.
-/
def asymptoticNhds (v : V) : Filter P := ⨆ p, atTop (α := k) • 𝓝 v +ᵥ pure p
/-
**AffineSpace.asymptoticNhds_vadd_pure** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds_vadd_pure (v : V) (p : P) : asymptoticNhds k V v +ᵥ pure p 
= asymptoticNhds k P v
参数：v : V；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSpace.asymptoticNhds.eq_1`：∀ (k : Type u_1) {V : Type u_2} (P : Ty
pe u_3) [inst : Field k] [inst_1 : LinearOrder k] [inst_2 : AddCommGroup V]   [i
nst_3 : _root_.Module…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `Filter.map_iSup`：map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, 
map m (f i)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSemigroupAction.add_vadd`：∀ {G : Type u_9} {P : Type u_10} {inst : Ad
dSemigroup G} [self : AddSemigroupAction G P] (g₁ g₂ : G) (p : P),   (g₁ + g₂) +
ᵥ p = g₁ +ᵥ g₂ +ᵥ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asymptoticNhds_vadd_pure (v : V) (p : P) :
    asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v := by
  simp_rw [asymptoticNhds, vadd_pure, map_iSup, map_map, Function.comp_def]
  refine (Equiv.vaddConst p).iSup_congr fun _ => ?_
  simp [add_vadd]
/-
**AffineSpace.vadd_asymptoticNhds** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：vadd_asymptoticNhds (u v : V) : u +ᵥ asymptoticNhds k P v = asymptoticNhds
 k P v
参数：u v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSpace.asymptoticNhds_vadd_pure`：asymptoticNhds_vadd_pure (v : V) (
p : P) : asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `VAddCommClass.vadd_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : VAdd M α} {inst_1 : VAdd N α} [self : VAddCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `vaddCommClass_self`：∀ (M : Type u_9) (α : Type u_10) [inst : AddCommMono
id M] [inst_1 : AddAction M α], VAddCommClass M M α
-/
theorem vadd_asymptoticNhds (u v : V) : u +ᵥ asymptoticNhds k P v = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  nth_rw 1 [← asymptoticNhds_vadd_pure v p]
  simp_rw [← asymptoticNhds_vadd_pure v (u +ᵥ p), vadd_pure, ← Filter.map_vadd, map_map]
  congr with v
  exact vadd_comm u v p

variable {α : Type*} {l : Filter α}
/-
**AffineSpace._root_.Filter.Tendsto.asymptoticNhds_vadd_const** 是 Mathlib 中的一个定理
，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.asymptoticNhds_vadd_const {f : α → V} {v : V} (p : P)
    (hf : Tendsto f l (asymptoticNhds k V v)) :
    Tendsto (fun x => f x +ᵥ p) l (asymptoticNhds k P v) := by
  rw [← asymptoticNhds_vadd_pure, vadd_pure]
  exact tendsto_map.comp hf
/-
**AffineSpace._root_.Filter.Tendsto.const_vadd_asymptoticNhds** 是 Mathlib 中的一个定理
，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.const_vadd_asymptoticNhds {f : α → P} {v : V} (u : V)
    (hf : Tendsto f l (asymptoticNhds k P v)) :
    Tendsto (fun x => u +ᵥ f x) l (asymptoticNhds k P v) := by
  rw [← vadd_asymptoticNhds u, ← Filter.map_vadd]
  exact tendsto_map.comp hf

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]
/-
**AffineSpace.asymptoticNhds_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds_eq_smul (v : V) : asymptoticNhds k V v = atTop (α
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.add_pure`：∀ {α : Type u_2} [inst : Add α] {f : Filter α} {b : α},
 f + pure b = Filter.map (fun x => x + b) f
· 使用定理 `Filter.map_map₂`：map_map₂ (m : α -> β -> γ) (n : γ -> δ) : (map₂ m f g).
map n = map₂ (fun a b => n (m a b)) f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 37 条，此处仅展示前 30 条）
-/
theorem asymptoticNhds_eq_smul (v : V) : asymptoticNhds k V v = atTop (α := k) • 𝓝 v := by
  unfold asymptoticNhds
  apply le_antisymm
  · refine iSup_le fun u => ?_
    simp_rw [vadd_eq_add, add_pure, ← map₂_smul, map_map₂, ← map_prod_eq_map₂]
    have : (fun x : k × V => x.1 • x.2 + u) =ᶠ[atTop ×ˢ 𝓝 v]
        (Function.uncurry (· • ·)) ∘ (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) := by
      filter_upwards [tendsto_fst.eventually (eventually_ne_atTop 0)] with _ h
      simp [h]
    rw [map_congr this, ← map_map]
    apply map_mono
    have : Tendsto (fun x : k × V => (x.1, x.2 + x.1⁻¹ • u)) (atTop ×ˢ 𝓝 v) _ :=
      tendsto_fst.prodMk <| tendsto_snd.add <| tendsto_fst.inv_tendsto_atTop.smul_const u
    simpa
  · apply (le_iSup _ 0).trans'
    simp
/-
**AffineSpace.asymptoticNhds_eq_smul_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace
`。
形式化陈述：asymptoticNhds_eq_smul_vadd (v : V) (p : P) : asymptoticNhds k P v = atTop
 (α
参数：v : V；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul`：asymptoticNhds_eq_smul (v : V) : asy
mptoticNhds k V v = atTop (α
· 使用定理 `AffineSpace.asymptoticNhds_vadd_pure`：asymptoticNhds_vadd_pure (v : V) (
p : P) : asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v
-/
theorem asymptoticNhds_eq_smul_vadd (v : V) (p : P) :
    asymptoticNhds k P v = atTop (α := k) • 𝓝 v +ᵥ pure p := by
  rw [← asymptoticNhds_eq_smul, asymptoticNhds_vadd_pure]
/-
**AffineSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {v : V} : (asymptoticNhds k P v).NeBot := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd v p]
  infer_instance
/-
**AffineSpace.asymptoticNhds_zero'** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem asymptoticNhds_zero' : asymptoticNhds k V (0 : V) = ⊤ := by
  rw [← top_le_iff, ← iSup_pure_eq_top, iSup_le_iff]
  intro v
  rw [← map_const (f := atTop (α := k))]
  have : (fun _ => v) =ᶠ[atTop (α := k)]
      (Function.uncurry (· • ·)) ∘ (fun c => (c, c⁻¹ • v)) := by
    filter_upwards [eventually_ne_atTop 0] with _ h
    simp [h]
  rw [map_congr this, ← map_map, asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂]
  apply map_mono
  have : Tendsto (fun c => (c, c⁻¹ • v)) (atTop (α := k)) _ :=
    tendsto_id.prodMk <| tendsto_inv_atTop_zero.smul_const v
  simpa

@[simp]
/-
**AffineSpace.asymptoticNhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds_zero : asymptoticNhds k P (0 : V) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSpace.asymptoticNhds_vadd_pure`：asymptoticNhds_vadd_pure (v : V) (
p : P) : asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v
· 使用定理 `_private.Mathlib.Topology.Algebra.AsymptoticCone.0.AffineSpace.asymptoti
cNhds_zero'`：∀ {k : Type u_1} {V : Type u_2} [inst : Field k] [inst_1 : LinearOr
der k] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Module k V] [inst_4 :…
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `Function.Surjective.filter_map_top`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → Filter.map f ⊤ = ⊤
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem asymptoticNhds_zero : asymptoticNhds k P (0 : V) = ⊤ := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [← asymptoticNhds_vadd_pure 0 p, asymptoticNhds_zero', vadd_pure]
  exact (Equiv.vaddConst p).surjective.filter_map_top
/-
**AffineSpace._root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds** 是 M
athlib 中的一个定理，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds {f : α → k} {g : α → V} {v : V}
    (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 v)) :
    Tendsto (fun x => f x • g x) l (asymptoticNhds k V v) := by
  rw [asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂]
  exact tendsto_map.comp (hf.prodMk hg)
/-
**AffineSpace._root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds** 是 
Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds {f : α → k} (v : V)
    (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • v) l (asymptoticNhds k V v) :=
  hf.atTop_smul_nhds_tendsto_asymptoticNhds tendsto_const_nhds
/-
**AffineSpace.asymptoticNhds_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds_smul (v : V) {c : k} (hc : 0 < c) : asymptoticNhds k P (c •
 v) = asymptoticNhds k P v
参数：v : V；hc : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.map₂_map_right`：map₂_map_right (m : α -> γ -> δ) (n : β -> γ) : m
ap₂ m f (g.map n) = map₂ (fun a b => m a (n b)) f g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem asymptoticNhds_smul (v : V) {c : k} (hc : 0 < c) :
    asymptoticNhds k P (c • v) = asymptoticNhds k P v := by
  have ⟨p⟩ : Nonempty P := inferInstance
  simp_rw [asymptoticNhds_eq_smul_vadd _ p,
    ← show map (c • ·) (𝓝 v) = 𝓝 (c • v) from
      (Homeomorph.smulOfNeZero c hc.ne').map_nhds_eq v,
    ← map₂_smul, map₂_map_right, smul_smul, ← map₂_map_left,
    show map (· * c) atTop = atTop from (OrderIso.mulRight₀ _ hc).map_atTop]

@[simp]
/-
**AffineSpace.nhds_bind_asymptoticNhds** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：nhds_bind_asymptoticNhds (v : V) : (𝓝 v).bind (asymptoticNhds k P) = asymp
toticNhds k P v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_bind_nhds`：nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.pure_bind`：pure_bind (a : α) (m : α -> Filter β) : bind (pure a) 
m = m a
· 使用定理 `Filter.bind_mono`：bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α -> Filter β} (
hf : f₁ <= f₂) (hg : g₁ <=ᶠ[f₁] g₂) : bind f₁ g₁ <= bind f₂ g₂
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `Filter.EventuallyLE.rfl`：∀ {α : Type u} {β : Type v} [inst : Preorder β]
 {l : Filter α} {f : α → β}, f ≤ᶠ[l] f
-/
theorem nhds_bind_asymptoticNhds (v : V) :
    (𝓝 v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  apply le_antisymm
  · have ⟨p⟩ : Nonempty P := inferInstance
    eta_expand
    simp_rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure]
    nth_rw 2 [← nhds_bind_nhds]
    simp only [le_def, mem_map, ← map₂_smul, mem_map₂_iff, mem_bind]
    grind
  · rw [← pure_bind v (asymptoticNhds k P)]
    exact bind_mono (pure_le_nhds v) .rfl

@[simp]
/-
**AffineSpace.asymptoticNhds_bind_nhds** 是 Mathlib 中的一个定理，位于命名空间 `AffineSpace`。
形式化陈述：asymptoticNhds_bind_nhds [TopologicalSpace P] [IsTopologicalAddTorsor P] (
v : V) : (asymptoticNhds k P v).bind 𝓝 = asymptoticNhds k P v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_bind_nhds`：nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x
· 使用定理 `Filter.mem_bind`：mem_bind {s : Set β} {f : Filter α} {m : α -> Filter β}
 : s in bind f m ↔ exists t in f, forall x in t, s in m x
· 使用定理 `Filter.bind_map`：bind_map {α β} (m : α -> β) (f : Filter α) (g : β -> Fi
lter γ) : (bind (map m f) g) = bind f (g ∘ m)
· 使用定理 `Filter.smul_mem_smul`：smul_mem_smul : s in f -> t in g -> s • t in f • g
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.vsub`：∀ {V : Type u_1} {P : Type u_2} {α : Type u_3} [ins
t : AddGroup V] [inst_1 : TopologicalSpace V]   [inst_2 : AddTorsor V P] [inst_3
 : Topolo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 41 条，此处仅展示前 30 条）
-/
theorem asymptoticNhds_bind_nhds [TopologicalSpace P] [IsTopologicalAddTorsor P] (v : V) :
    (asymptoticNhds k P v).bind 𝓝 = asymptoticNhds k P v := by
  refine le_antisymm (fun s h => ?_) (bind_mono le_rfl (.of_forall pure_le_nhds))
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [asymptoticNhds_eq_smul_vadd _ p, vadd_pure] at h ⊢
  rw [← nhds_bind_nhds] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, hs⟩ := h
  rw [mem_bind] at ht₂
  obtain ⟨t₃, ht₃, ht₂⟩ := ht₂
  rw [bind_map, mem_bind]
  refine ⟨(t₁ ∩ Set.Ioi 0) • t₃, smul_mem_smul (inter_mem ht₁ (Ioi_mem_atTop _)) ht₃,
    Set.forall_mem_image2.mpr fun c ⟨hc₁, hc₂⟩ u hu => ?_⟩
  rw [show s = (· -ᵥ p) ⁻¹' ((· +ᵥ p) ⁻¹' s) by simp [Set.preimage_preimage]]
  apply tendsto_id.vsub tendsto_const_nhds
  rw [vadd_vsub]
  filter_upwards [smul_mem_nhds_smul₀ hc₂.ne' (ht₂ u hu)]
  rw [← Set.image_smul, Set.forall_mem_image]
  exact fun w hw => hs (Set.smul_mem_smul hc₁ hw)

@[simp]
/-
**AffineSpace.asymptoticNhds_bind_asymptoticNhds** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neSpace`。
形式化陈述：asymptoticNhds_bind_asymptoticNhds (v : V) : (asymptoticNhds k V v).bind (
asymptoticNhds k P) = asymptoticNhds k P v
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext'`：∀ {α : Type u} {f₁ f₂ : Filter α}, (∀ (p : α → Prop), (∀ᶠ (
x : α) in f₁, p x) ↔ ∀ᶠ (x : α) in f₂, p x) → f₁ = f₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul`：asymptoticNhds_eq_smul (v : V) : asy
mptoticNhds k V v = atTop (α
· 使用定理 `Filter.eventually_bind`：eventually_bind {f : Filter α} {m : α -> Filter 
β} {p : β -> Prop} : (forallᶠ y in bind f m, p y) ↔ forallᶠ x in f, forallᶠ y in
 m x, p y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `AffineSpace.nhds_bind_asymptoticNhds`：nhds_bind_asymptoticNhds (v : V) :
 (𝓝 v).bind (asymptoticNhds k P) = asymptoticNhds k P v
· 使用定理 `Filter.map_snd_prod`：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f
] : map Prod.snd (f ×ˢ g) = g
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSpace.asymptoticNhds_smul`：asymptoticNhds_smul (v : V) {c : k} (hc
 : 0 < c) : asymptoticNhds k P (c • v) = asymptoticNhds k P v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asymptoticNhds_bind_asymptoticNhds (v : V) :
    (asymptoticNhds k V v).bind (asymptoticNhds k P) = asymptoticNhds k P v := by
  refine Filter.ext' fun p => ?_
  rw [asymptoticNhds_eq_smul, eventually_bind, ← map₂_smul, ← map_prod_eq_map₂, eventually_map,
    ← nhds_bind_asymptoticNhds, eventually_bind]
  nth_rw 2 [← map_snd_prod (atTop (α := k)) (𝓝 v)]
  rw [eventually_map]
  apply eventually_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ (hc : 0 < c)
  simp only [asymptoticNhds_smul _ hc]

end AffineSpace

open AffineSpace

variable (k) in
/-- The set of directions `v` for which the set has points arbitrarily far in directions near `v`.
-/
/-
**asymptoticCone** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：asymptoticCone (s : Set P) : Set V
参数：s : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of directions `v` for which the set has points arbitrarily far in direct
ions near `v`.
-/
def asymptoticCone (s : Set P) : Set V := {v | ∃ᶠ p in asymptoticNhds k P v, p ∈ s}
/-
**mem_asymptoticCone_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_asymptoticCone_iff {v : V} {s : Set P} : v in asymptoticCone k s ↔ exi
stsᶠ p in asymptoticNhds k P v, p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_asymptoticCone_iff {v : V} {s : Set P} :
    v ∈ asymptoticCone k s ↔ ∃ᶠ p in asymptoticNhds k P v, p ∈ s :=
  Iff.rfl

@[simp]
/-
**asymptoticCone_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_empty : asymptoticCone k (∅ : Set P) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Filter.frequently_false`：frequently_false (f : Filter α) : ¬existsᶠ _ in
 f, False
-/
theorem asymptoticCone_empty : asymptoticCone k (∅ : Set P) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun _ => frequently_false _

@[gcongr]
/-
**asymptoticCone_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_mono {s t : Set P} (h : s subseteq t) : asymptoticCone k s 
subseteq asymptoticCone k t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
-/
theorem asymptoticCone_mono {s t : Set P} (h : s ⊆ t) : asymptoticCone k s ⊆ asymptoticCone k t :=
  fun _ h' => h'.mono h
/-
**asymptoticCone_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_union {s t : Set P} : asymptoticCone k (s union t) = asympt
oticCone k s union asymptoticCone k t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asymptoticCone_union {s t : Set P} :
    asymptoticCone k (s ∪ t) = asymptoticCone k s ∪ asymptoticCone k t := by
  ext
  simp only [Set.mem_union, mem_asymptoticCone_iff, Filter.frequently_or_distrib]
/-
**asymptoticCone_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι -> S
et P) : asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, asymptoticCone k (f i)
参数：hs : s.Finite；f : ι -> Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `asymptoticCone_empty`：asymptoticCone_empty : asymptoticCone k (∅ : Set P
) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `asymptoticCone_union`：asymptoticCone_union {s t : Set P} : asymptoticCon
e k (s union t) = asymptoticCone k s union asymptoticCone k t
-/
theorem asymptoticCone_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set P) :
    asymptoticCone k (⋃ i ∈ s, f i) = ⋃ i ∈ s, asymptoticCone k (f i) := by
  induction s, hs using Set.Finite.induction_on <;>
    simp [asymptoticCone_union, *]
/-
**asymptoticCone_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_sUnion {S : Set (Set P)} (hS : S.Finite) : asymptoticCone k
 (⋃₀ S) = ⋃ s in S, asymptoticCone k s
参数：Set P；hS : S.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `asymptoticCone_biUnion`：asymptoticCone_biUnion {ι : Type*} {s : Set ι} (
hs : s.Finite) (f : ι -> Set P) : asymptoticCone k (⋃ i in s, f i) = ⋃ i in s, a
symptoticCon…
-/
theorem asymptoticCone_sUnion {S : Set (Set P)} (hS : S.Finite) :
    asymptoticCone k (⋃₀ S) = ⋃ s ∈ S, asymptoticCone k s := by
  rw [Set.sUnion_eq_biUnion, asymptoticCone_biUnion hS]

nonrec theorem Finset.asymptoticCone_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set P) :
    asymptoticCone k (⋃ i ∈ s, f i) = ⋃ i ∈ s, asymptoticCone k (f i) :=
  asymptoticCone_biUnion s.finite_toSet f
/-
**asymptoticCone_iUnion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_iUnion_of_finite {ι : Type*} [Finite ι] (f : ι -> Set P) : 
asymptoticCone k (⋃ i, f i) = ⋃ i, asymptoticCone k (f i)
参数：f : ι -> Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_range`：sUnion_range (f : ι -> Set β) : ⋃₀ range f = ⋃ x, f x
· 使用定理 `asymptoticCone_sUnion`：asymptoticCone_sUnion {S : Set (Set P)} (hS : S.F
inite) : asymptoticCone k (⋃₀ S) = ⋃ s in S, asymptoticCone k s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
-/
theorem asymptoticCone_iUnion_of_finite {ι : Type*} [Finite ι] (f : ι → Set P) :
    asymptoticCone k (⋃ i, f i) = ⋃ i, asymptoticCone k (f i) := by
  rw [← Set.sUnion_range, asymptoticCone_sUnion (Set.finite_range f), Set.biUnion_range]

variable [TopologicalSpace k] [OrderTopology k] [IsStrictOrderedRing k]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]
/-
**zero_mem_asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_asymptoticCone {s : Set P} : 0 in asymptoticCone k s ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `asymptoticCone_empty`：asymptoticCone_empty : asymptoticCone k (∅ : Set P
) = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `AffineSpace.asymptoticNhds_zero`：asymptoticNhds_zero : asymptoticNhds k 
P (0 : V) = ⊤
-/
theorem zero_mem_asymptoticCone {s : Set P} : 0 ∈ asymptoticCone k s ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun _ => ?_⟩
  · simp +contextual [Set.not_nonempty_iff_eq_empty]
  · simpa [mem_asymptoticCone_iff]
/-
**asymptoticCone_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_nonempty {s : Set P} : (asymptoticCone k s).Nonempty ↔ s.No
nempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `asymptoticCone_empty`：asymptoticCone_empty : asymptoticCone k (∅ : Set P
) = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_mem_asymptoticCone`：zero_mem_asymptoticCone {s : Set P} : 0 in asym
ptoticCone k s ↔ s.Nonempty
-/
theorem asymptoticCone_nonempty {s : Set P} : (asymptoticCone k s).Nonempty ↔ s.Nonempty := by
  refine ⟨Function.mtr ?_, fun h => ⟨0, zero_mem_asymptoticCone.mpr h⟩⟩
  simp +contextual [Set.not_nonempty_iff_eq_empty]

@[simp]
/-
**smul_mem_asymptoticCone_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mem_asymptoticCone_iff {s : Set P} {c : k} {v : V} (hc : 0 < c) : c •
 v in asymptoticCone k s ↔ v in asymptoticCone k s
参数：hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineSpace.asymptoticNhds_smul`：asymptoticNhds_smul (v : V) {c : k} (hc
 : 0 < c) : asymptoticNhds k P (c • v) = asymptoticNhds k P v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_mem_asymptoticCone_iff {s : Set P} {c : k} {v : V} (hc : 0 < c) :
    c • v ∈ asymptoticCone k s ↔ v ∈ asymptoticCone k s := by
  simp_rw [mem_asymptoticCone_iff, asymptoticNhds_smul v hc]
/-
**smul_mem_asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_mem_asymptoticCone {s : Set P} {c : k} {v : V} (hc : 0 <= c) (h : v i
n asymptoticCone k s) : c • v in asymptoticCone k s
参数：hc : 0 <= c；h : v in asymptoticCone k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_mem_asymptoticCone`：zero_mem_asymptoticCone {s : Set P} : 0 in asym
ptoticCone k s ↔ s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `asymptoticCone_nonempty`：asymptoticCone_nonempty {s : Set P} : (asymptot
icCone k s).Nonempty ↔ s.Nonempty
· 使用定理 `smul_mem_asymptoticCone_iff`：smul_mem_asymptoticCone_iff {s : Set P} {c 
: k} {v : V} (hc : 0 < c) : c • v in asymptoticCone k s ↔ v in asymptoticCone k 
s
-/
theorem smul_mem_asymptoticCone {s : Set P} {c : k} {v : V} (hc : 0 ≤ c)
    (h : v ∈ asymptoticCone k s) : c • v ∈ asymptoticCone k s := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mem_asymptoticCone, ← asymptoticCone_nonempty (k := k)]; exact ⟨v, h⟩
  · rwa [smul_mem_asymptoticCone_iff hc]
/-
**asymptoticCone_eq_closure_of_forall_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_eq_closure_of_forall_smul_mem {s : Set V} (hs : forall c : 
k, 0 < c -> forall x in s, c • x in s) : asymptoticCone k s = closure s
参数：hs : forall c : k, 0 < c -> forall x in s, c • x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_snd_prod`：map_snd_prod (f : Filter α) (g : Filter β) [NeBot f
] : map Prod.snd (f ×ˢ g) = g
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `mem_asymptoticCone_iff`：mem_asymptoticCone_iff {v : V} {s : Set P} : v i
n asymptoticCone k s ↔ existsᶠ p in asymptoticNhds k P v, p in s
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul`：asymptoticNhds_eq_smul (v : V) : asy
mptoticNhds k V v = atTop (α
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用引理 `Filter.frequently_congr`：frequently_congr {p q : α -> Prop} {f : Filter 
α} (h : forallᶠ x in f, p x ↔ q x) : (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem asymptoticCone_eq_closure_of_forall_smul_mem {s : Set V}
    (hs : ∀ c : k, 0 < c → ∀ x ∈ s, c • x ∈ s) : asymptoticCone k s = closure s := by
  ext v
  rw [mem_closure_iff_frequently, ← map_snd_prod (atTop (α := k)) (𝓝 v), frequently_map,
    mem_asymptoticCone_iff, asymptoticNhds_eq_smul, ← map₂_smul, ← map_prod_eq_map₂, frequently_map]
  apply frequently_congr
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with ⟨c, u⟩ hc
  refine ⟨fun hu => ?_, hs c hc u⟩
  specialize hs c⁻¹ (inv_pos_of_pos hc) (c • u) hu
  rwa [inv_smul_smul₀ hc.ne'] at hs
/-
**asymptoticCone_submodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_submodule {s : Submodule k V} : asymptoticCone k (s : Set V
) = closure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `asymptoticCone_eq_closure_of_forall_smul_mem`：asymptoticCone_eq_closure_
of_forall_smul_mem {s : Set V} (hs : forall c : k, 0 < c -> forall x in s, c • x
 in s) : asymptoticCone k s = clos…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem asymptoticCone_submodule {s : Submodule k V} : asymptoticCone k (s : Set V) = closure s :=
  asymptoticCone_eq_closure_of_forall_smul_mem fun _ _ _ h => s.smul_mem _ h
/-
**asymptoticCone_affineSubspace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_affineSubspace {s : AffineSubspace k P} (hs : (s : Set P).N
onempty) : asymptoticCone k (s : Set P) = closure s.direction
参数：hs : (s : Set P).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSpace.asymptoticNhds_vadd_pure`：asymptoticNhds_vadd_pure (v : V) (
p : P) : asymptoticNhds k V v +ᵥ pure p = asymptoticNhds k P v
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asymptoticCone_affineSubspace {s : AffineSubspace k P} (hs : (s : Set P).Nonempty) :
    asymptoticCone k (s : Set P) = closure s.direction := by
  have ⟨p, hp⟩ := hs
  ext v
  simp_rw [← asymptoticCone_submodule, mem_asymptoticCone_iff, ← asymptoticNhds_vadd_pure v p,
    vadd_pure, frequently_map, SetLike.mem_coe, s.vadd_mem_iff_mem_direction _ hp]

@[simp]
/-
**asymptoticCone_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_univ : asymptoticCone k (Set.univ : Set P) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineSubspace.top_coe`：top_coe : ((⊤ : AffineSubspace k P) : Set P) = S
et.univ
· 使用定理 `asymptoticCone_affineSubspace`：asymptoticCone_affineSubspace {s : Affine
Subspace k P} (hs : (s : Set P).Nonempty) : asymptoticCone k (s : Set P) = closu
re s.direction
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `AffineSubspace.direction_top`：direction_top : (⊤ : AffineSubspace k P).d
irection = ⊤
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `closure_univ`：closure_univ : closure (univ : Set X) = univ
-/
theorem asymptoticCone_univ : asymptoticCone k (Set.univ : Set P) = Set.univ := by
  rw [← AffineSubspace.top_coe k, asymptoticCone_affineSubspace Set.univ_nonempty,
    AffineSubspace.direction_top, Submodule.top_coe, closure_univ]
/-
**asymptoticCone_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_closure [TopologicalSpace P] [IsTopologicalAddTorsor P] (s 
: Set P) : asymptoticCone k (closure s) = asymptoticCone k s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineSpace.asymptoticNhds_bind_nhds`：asymptoticNhds_bind_nhds [Topologi
calSpace P] [IsTopologicalAddTorsor P] (v : V) : (asymptoticNhds k P v).bind 𝓝 =
 asymptoticNhds k P v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asymptoticCone_closure [TopologicalSpace P] [IsTopologicalAddTorsor P] (s : Set P) :
    asymptoticCone k (closure s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, mem_closure_iff_frequently, ← frequently_bind,
    asymptoticNhds_bind_nhds]
/-
**isClosed_asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_asymptoticCone {s : Set P} : IsClosed (asymptoticCone k s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosed_iff_frequently`：isClosed_iff_frequently : IsClosed s ↔ forall x
, (existsᶠ y in 𝓝 x, y in s) -> x in s
· 使用定理 `AffineSpace.nhds_bind_asymptoticNhds`：nhds_bind_asymptoticNhds (v : V) :
 (𝓝 v).bind (asymptoticNhds k P) = asymptoticNhds k P v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isClosed_asymptoticCone {s : Set P} : IsClosed (asymptoticCone k s) := by
  have ⟨p⟩ : Nonempty P := inferInstance
  rw [isClosed_iff_frequently]
  intro v h
  simp_rw [mem_asymptoticCone_iff, ← frequently_bind, nhds_bind_asymptoticNhds] at h
  exact h

@[simp]
/-
**asymptoticCone_asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：asymptoticCone_asymptoticCone (s : Set P) : asymptoticCone k (asymptoticCo
ne k s) = asymptoticCone k s
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineSpace.asymptoticNhds_bind_asymptoticNhds`：asymptoticNhds_bind_asym
ptoticNhds (v : V) : (asymptoticNhds k V v).bind (asymptoticNhds k P) = asymptot
icNhds k P v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asymptoticCone_asymptoticCone (s : Set P) :
    asymptoticCone k (asymptoticCone k s) = asymptoticCone k s := by
  ext
  simp_rw [mem_asymptoticCone_iff, ← Filter.frequently_bind, asymptoticNhds_bind_asymptoticNhds]

end General

section Convex

open AffineSpace

variable
  {k V : Type*}
  [Field k] [LinearOrder k] [IsStrictOrderedRing k] [TopologicalSpace k] [OrderTopology k]
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V]
  {s : Set V}

/-- If a closed set `s` is star-convex at `p` and `v` is in the asymptotic cone of `s`, then the ray
of direction `v` starting from `p` is contained in `s`. -/
/-
**StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : 
V} (hs₁ : StarConvex k p s) (hs₂ : IsClosed s) (hc : 0 <= c) (hv : v in asymptot
icCone k s) : c • v +ᵥ p in s
参数：hs₁ : StarConvex k p s；hs₂ : IsClosed s；hc : 0 <= c；hv : v in asymptoticCone 
k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_iff_frequently`：isClosed_iff_frequently : IsClosed s ↔ forall x
, (existsᶠ y in 𝓝 x, y in s) -> x in s
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.vadd_const`：∀ {M : Type u_1} {X : Type u_2} {α : Type u_4
} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : VAdd M X
] [ContinuousVA…
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `mem_asymptoticCone_iff`：mem_asymptoticCone_iff {v : V} {s : Set P} : v i
n asymptoticCone k s ↔ existsᶠ p in asymptoticNhds k P v, p in s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `StarConvex.segment_subset`：StarConvex.segment_subset (h : StarConvex 𝕜 x
 s) {y : E} (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用引理 `SameRay.nonneg_smul_right`：nonneg_smul_right (h : SameRay R x y) (ha : 0
 <= a) : SameRay R x (a • y)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If a closed set `s` is star-convex at `p` and `v` is in the asymptotic cone of `
s`, then the ray
of direction `v` starting from `p` is contained in `s`.
-/
theorem StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : StarConvex k p s) (hs₂ : IsClosed s) (hc : 0 ≤ c) (hv : v ∈ asymptoticCone k s) :
    c • v +ᵥ p ∈ s := by
  refine isClosed_iff_frequently.mp hs₂ _ <|
    tendsto_snd (f := atTop (α := k)) |>.const_smul _ |>.vadd_const _ |>.frequently ?_
  rw [mem_asymptoticCone_iff, asymptoticNhds_eq_smul_vadd v p, vadd_pure, frequently_map,
    ← map₂_smul, ← map_prod_eq_map₂, frequently_map] at hv
  apply hv.mp
  filter_upwards [tendsto_fst.eventually (eventually_ge_atTop c)]
    with ⟨t, u⟩ (ht : c ≤ t) (h : t • u +ᵥ p ∈ s)
  change c • u +ᵥ p ∈ s
  apply hs₁.segment_subset h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub, vadd_vsub, vadd_vsub_vadd_cancel_right,
    ← sub_smul]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).nonneg_smul_right (sub_nonneg.mpr ht)

/-- If `v` is in the asymptotic cone of a closed convex set `s`, then for every `p ∈ s`, the ray of
direction `v` starting from `p` is contained in `s`. -/
/-
**Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V} (
hs₁ : Convex k s) (hs₂ : IsClosed s) (hc : 0 <= c) (hv : v in asymptoticCone k s
) (hp : p in s) : c • v +ᵥ p in s
参数：hs₁ : Convex k s；hs₂ : IsClosed s；hc : 0 <= c；hv : v in asymptoticCone k s；hp
 : p in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarConvex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`：StarConvex.s
mul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V} (hs₁ : StarConv
ex k p s) (hs₂ : IsClosed s) (hc : 0 <= c) (hv :…

--- 原说明 ---
If `v` is in the asymptotic cone of a closed convex set `s`, then for every `p ∈
 s`, the ray of
direction `v` starting from `p` is contained in `s`.
-/
theorem Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V}
    (hs₁ : Convex k s) (hs₂ : IsClosed s) (hc : 0 ≤ c) (hv : v ∈ asymptoticCone k s) (hp : p ∈ s) :
    c • v +ᵥ p ∈ s :=
  (hs₁ hp).smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs₂ hc hv
/-
**Convex.asymptoticCone** 是 Mathlib 中的一个定理，位于命名空间 `Convex`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} [inst : Field k] [inst_1 : LinearOrder k] 
[IsStrictOrderedRing k]   [inst_3 : TopologicalSpace k] [OrderTopology k] [inst_
5 : AddCommGroup V] [inst_6 : _root_.Module k V]   [inst_7 : TopologicalSpace V]
 [IsTopologicalAddGroup V] [ContinuousSMul k V] {s : Set V},   Convex k s → Conv
ex k (asymptoticCone k s)
参数：asymptoticCone k s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `asymptoticCone_empty`：asymptoticCone_empty : asymptoticCone k (∅ : Set P
) = ∅
· 使用定理 `convex_empty`：convex_empty : Convex 𝕜 (∅ : Set E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_asymptoticCone_iff`：mem_asymptoticCone_iff {v : V} {s : Set P} : v i
n asymptoticCone k s ↔ existsᶠ p in asymptoticNhds k P v, p in s
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Tendsto.asymptoticNhds_vadd_const`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_3} [inst : Field k] [inst_1 : LinearOrder k] [inst_2 : AddCommGrou
p V]   [inst_3 : _root_.Module…
· 使用定理 `Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds`：∀ {k : Type u_1}
 {V : Type u_2} [inst : Field k] [inst_1 : LinearOrder k] [inst_2 : AddCommGroup
 V]   [inst_3 : _root_.Module k V] [inst_4 :…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`：Convex.smul_vadd
_mem_of_isClosed_of_mem_asymptoticCone {c : k} {v p : V} (hs₁ : Convex k s) (hs₂
 : IsClosed s) (hc : 0 <= c) (hv : v in asym…
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `affineSegment_eq_segment`：affineSegment_eq_segment (x y : V) : affineSeg
ment R x y = segment R x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mem_vadd_const_affineSegment`：mem_vadd_const_affineSegment {x y z : V} (
p : P) : z +ᵥ p in affineSegment R (x +ᵥ p) (y +ᵥ p) ↔ z in affineSegment R x y
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
（共 58 条，此处仅展示前 30 条）
-/
protected theorem Convex.asymptoticCone (hs : Convex k s) : Convex k (asymptoticCone k s) := by
  wlog hs' : IsClosed s generalizing s
  · rw [← asymptoticCone_closure]; exact this hs.closure isClosed_closure
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [asymptoticCone_empty]; exact convex_empty
  intro v hv u hu a b ha hb hab
  rw [mem_asymptoticCone_iff]
  refine tendsto_id.atTop_smul_const_tendsto_asymptoticNhds _ |>.asymptoticNhds_vadd_const p
    |>.frequently (Eventually.frequently ?_)
  filter_upwards [eventually_ge_atTop 0] with c hc
  simp_rw [id, smul_add, smul_smul]
  have h₁ : c • v +ᵥ p ∈ s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hv hp
  have h₂ : c • u +ᵥ p ∈ s := hs.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hs' hc hu hp
  apply hs.segment_subset h₁ h₂
  rw [← affineSegment_eq_segment, mem_vadd_const_affineSegment, affineSegment_eq_segment]
  exists a, b, ha, hb, hab
  module

/-- If `v` is in the asymptotic cone of a convex set `s`, then for every interior point `p`, the ray
of direction `v` starting from `p` is contained in `s`. -/
/-
**Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone {c : k} {v p : V} (
hs : Convex k s) (hc : 0 <= c) (hp : s in 𝓝 p) (hv : v in asymptoticCone k s) : 
c • v +ᵥ p in s
参数：hs : Convex k s；hc : 0 <= c；hp : s in 𝓝 p；hv : v in asymptoticCone k s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.frequently_const`：frequently_const {f : Filter α} [NeBot f] {p : 
Prop} : (existsᶠ _ in f, p) ↔ p
· 使用定理 `Filter.prod.instNeBot`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α} {g
 : Filter β} [hf : f.NeBot] [hg : g.NeBot], (f ×ˢ g).NeBot
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_map`：frequently_map {P : β -> Prop} : (existsᶠ b in ma
p m f, P b) ↔ existsᶠ a in f, P (m a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_prod_eq_map₂`：map_prod_eq_map₂ (m : α -> β -> γ) (f : Filter 
α) (g : Filter β) : Filter.map (fun p : α × β => m p.1 p.2) (f ×ˢ g) = map₂ m f 
g
· 使用定理 `Filter.map₂_smul`：map₂_smul : map₂ (· • ·) f g = f • g
· 使用定理 `Filter.vadd_pure`：∀ {α : Type u_2} {β : Type u_3} [inst : VAdd α β] {f :
 Filter α} {b : β}, f +ᵥ pure b = Filter.map (fun x => x +ᵥ b) f
· 使用定理 `AffineSpace.asymptoticNhds_eq_smul_vadd`：asymptoticNhds_eq_smul_vadd (v 
: V) (p : P) : asymptoticNhds k P v = atTop (α
· 使用定理 `mem_asymptoticCone_iff`：mem_asymptoticCone_iff {v : V} {s : Set P} : v i
n asymptoticCone k s ↔ existsᶠ p in asymptoticNhds k P v, p in s
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.fun_vadd`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
If `v` is in the asymptotic cone of a convex set `s`, then for every interior po
int `p`, the ray
of direction `v` starting from `p` is contained in `s`.
-/
theorem Convex.smul_vadd_mem_of_mem_nhds_of_mem_asymptoticCone {c : k} {v p : V}
    (hs : Convex k s) (hc : 0 ≤ c) (hp : s ∈ 𝓝 p) (hv : v ∈ asymptoticCone k s) :
    c • v +ᵥ p ∈ s := by
  rw [mem_asymptoticCone_iff, asymptoticNhds_eq_smul_vadd v (c • v +ᵥ p), vadd_pure,
    frequently_map, ← map₂_smul, ← map_prod_eq_map₂, frequently_map] at hv
  refine frequently_const.mp (hv.mp ?_)
  have : Tendsto (fun u => -(c • u : V) +ᵥ c • v +ᵥ p) (𝓝 v) (𝓝 p) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [tendsto_fst.eventually <| eventually_gt_atTop 0, this.comp tendsto_snd hp]
    with ⟨t, u⟩ (ht : 0 < t) (hu : -(c • u) +ᵥ c • v +ᵥ p ∈ s) (h : t • u +ᵥ c • v +ᵥ p ∈ s)
  apply hs.segment_subset hu h
  simp_rw [mem_segment_iff_sameRay, ← vsub_eq_sub]
  rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_neg, vadd_vsub]
  exact (SameRay.sameRay_nonneg_smul_left _ hc).pos_smul_right ht

end Convex

