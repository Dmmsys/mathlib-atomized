/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Spectral.Basic

/-!
# Pushforward of functions with locally finite support

In this file we define the notion of the pushforward of a function with locally finite support
between prespectral spaces along a spectral map. This is used for defining the (proper) pushforward
of algebraic cycles in algebraic geometry.

## Main declarations

- `Function.locallyFinsupp.map`: If `f : X → Y` is a spectral map between spectral spaces and
  `c : X → R` is locally of finite support, the pushforward of `c` along `f` at `y : Y` is
  `∑ᶠ x ∈ f ⁻¹' {y}, c x * w x`, where `w : X → R` is a weight function.

## Notes

In the case of algebraic cycles, the weight function used in `Function.locallyFinsupp.map` will be
specialized to the degree of the residue field extension
(see https://stacks.math.columbia.edu/tag/02R4).
-/

@[expose] public section

open Set Order Topology TopologicalSpace

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} (hf : IsSpectralMap f) (w : X → R)

namespace Function.locallyFinsupp

variable [Semiring R] {W : Set Y} (hW : IsOpen W) (c : Function.locallyFinsupp X R)
  [PrespectralSpace Y]

variable (f) in
/--
The pushforward of a function `c` of locally finite support by a spectral map with respect to a
weight function `w`.
-/
noncomputable
/-
**Function.locallyFinsupp.map** 是 Mathlib 中的一个定义，位于命名空间 `Function.locallyFinsupp
`。
形式化陈述：map (hf : IsSpectralMap f) (c : locallyFinsupp X R) : Function.locallyFins
upp Y R where toFun z
参数：hf : IsSpectralMap f；c : locallyFinsupp X R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (hf : IsSpectralMap f) (c : locallyFinsupp X R) : Function.locallyFinsupp Y R where
  toFun z := ∑ᶠ x ∈ f ⁻¹' {z}, c x * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
      (by simp : y ∈ ⊤) (by simp)
    refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
    suffices h : (U ∩ {z | (f ⁻¹' {z} ∩ support ⇑c).Nonempty}).Finite by
      refine h.subset (inter_subset_inter_right U fun y hy ↦ ?_)
      obtain ⟨x, (hx : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
      use x
      grind [mem_support]
    suffices (f ⁻¹' (U ∩ {z | (f ⁻¹' {z} ∩ c.support).Nonempty}) ∩ c.support).Finite from
      (this.image f).subset (fun a ha ↦ by grind [Set.Nonempty])
    exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf.2 hU.1.1 hU.1.2).subset
      (by simp; grind)

@[simp]
/-
**Function.locallyFinsupp.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Function.locallyF
insupp`。
形式化陈述：map_apply (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y) : map f 
w hf c y = ∑ᶠ x in f ⁻¹' {y}, c x * w x
参数：hf : IsSpectralMap f；c : locallyFinsupp X R；y : Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y) :
    map f w hf c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * w x := rfl
/-
**Function.locallyFinsupp.support_map_subset_of_forall_mem** 是 Mathlib 中的一个引理，位于
命名空间 `Function.locallyFinsupp`。
形式化陈述：support_map_subset_of_forall_mem (s : Set X) (t : Set Y) (hc : c.support s
ubseteq s) (h : forall x : X, x in s -> w x != 0 -> f x in t) : (map f w hf c).s
upport subseteq t
参数：s : Set X；t : Set Y；hc : c.support subseteq s；h : forall x : X, x in s -> w x
 != 0 -> f x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne_zero_of_finsum_mem_ne_zero`：∀ {α : Type u_1} {M : Type u_5} [i
nst : AddCommMonoid M] {f : α → M} {s : Set α},   ∑ᶠ (i : α) (_ : i ∈ s), f i ≠ 
0 → ∃ x ∈ s, f x ≠ 0
-/
lemma support_map_subset_of_forall_mem (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) : (map f w hf c).support ⊆ t := by
  intro y hy
  obtain ⟨x, (rfl : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  grind [mem_support]

@[simp]
/-
**Function.locallyFinsupp.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Function.locallyFins
upp`。
形式化陈述：map_id [PrespectralSpace X] (hw : forall z : X, w z = 1) : map id w isSpec
tralMap_id c = c
参数：hw : forall z : X, w z = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.ext`：ext [Zero Y] {D₁ D₂ : locallyFinsuppW
ithin U Y} (h : forall a, D₁ a = D₂ a) : D₁ = D₂
· 使用定理 `isSpectralMap_id`：isSpectralMap_id : IsSpectralMap (@id α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `finsum_congr_Prop`：∀ {M : Type u_2} [inst : AddCommMonoid M] {p q : Prop
} {f : p → M} {g : q → M} (hpq : p = q),   (∀ (h : q), f ⋯ = g h) → finsum f = f
insum g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `finsum_cond_eq_left`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMono
id M] {f : α → M} {a : α}, ∑ᶠ (i : α) (_ : i = a), f i = f a
· 使用定理 `Function.locallyFinsuppWithin.mk.congr_simp`：∀ {X : Type u_1} [inst : To
pologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : Zero Y] (toFun toFun_1 : 
X → Y)   (e_toFun : toFun = toFun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id [PrespectralSpace X] (hw : ∀ z : X, w z = 1) :
    map id w isSpectralMap_id c = c := by
  ext
  simp [map, hw]

end Function.locallyFinsupp

