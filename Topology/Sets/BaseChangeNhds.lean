/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Sets.Compacts

/-!
# Base changes among different families of neighbourhoods

This file builds base changes for `.compactsInside`, `openNhds`.

It also contains the evidences that `openRcNhds_to_openNhds`and
 `openRcNhds_to_compactNhds` are initials functors.

-/

@[expose] public section

namespace TopologicalSpace

open Set CategoryTheory Limits

variable {α : Type*} [TopologicalSpace α]

namespace Opens

/-- For `U` an open subset included in a open subset `V`, there is
a map sending compacts inside `U` to the ones inside `V` -/
/-
**TopologicalSpace.Opens.baseChangeCompactsInside** 是 Mathlib 中的一个定义，位于命名空间 `Top
ologicalSpace.Opens`。
形式化陈述：baseChangeCompactsInside {U V : Opens α} (h : U ⟶ V) : U.compactsInside ->
 V.compactsInside
参数：h : U ⟶ V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `U` an open subset included in a open subset `V`, there is
a map sending compacts inside `U` to the ones inside `V`
-/
def baseChangeCompactsInside {U V : Opens α} (h : U ⟶ V) : U.compactsInside → V.compactsInside :=
  fun ⟨K, hK⟩ ↦ ⟨K, fun _ hx ↦ Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩
/-
**TopologicalSpace.Opens.baseChangeCompactsInside_mono** 是 Mathlib 中的一个引理，位于命名空间
 `TopologicalSpace.Opens`。
形式化陈述：baseChangeCompactsInside_mono {U V : Opens α} (h : U ⟶ V) : Monotone baseC
hangeCompactsInside h
参数：h : U ⟶ V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
-/
lemma baseChangeCompactsInside_mono {U V : Opens α} (h : U ⟶ V) :
    Monotone <| baseChangeCompactsInside h :=
  fun _ _ hKL _ hx ↦ SetLike.mem_coe.mpr (hKL hx)

@[simp]
/-
**TopologicalSpace.Opens.baseChangeCompactsInside_comp** 是 Mathlib 中的一个引理，位于命名空间
 `TopologicalSpace.Opens`。
形式化陈述：baseChangeCompactsInside_comp {U V W : Opens α} (h : U ⟶ V) (k : V ⟶ W) (K
 : U.compactsInside) : baseChangeCompactsInside (h ≫ k) K = baseChangeCompactsIn
side k (baseChangeCompactsInside h K)
参数：h : U ⟶ V；k : V ⟶ W；K : U.compactsInside。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma baseChangeCompactsInside_comp {U V W : Opens α} (h : U ⟶ V) (k : V ⟶ W)
    (K : U.compactsInside) :
    baseChangeCompactsInside (h ≫ k) K = baseChangeCompactsInside k (baseChangeCompactsInside h K)
  := by rfl

@[simp]
/-
**TopologicalSpace.Opens.baseChangeOpenNhds_id** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gicalSpace.Opens`。
形式化陈述：baseChangeOpenNhds_id {U : Opens α} (K : U.compactsInside) : baseChangeCom
pactsInside (𝟙 U) K = K
参数：K : U.compactsInside。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma baseChangeOpenNhds_id {U : Opens α} (K : U.compactsInside) :
  baseChangeCompactsInside (𝟙 U) K = K := by rfl

end Opens

namespace Compacts

/-- For `K` a compact subset included in a compact subset `L`, there
is a map sending open neighbourhoods of `L` to the ones of `K` -/
/-
**TopologicalSpace.Compacts.baseChangeOpenNhds** 是 Mathlib 中的一个定义，位于命名空间 `Topolo
gicalSpace.Compacts`。
形式化陈述：baseChangeOpenNhds {K L : Compacts α} (h : K ⟶ L) : L.openNhds -> K.openNh
ds
参数：h : K ⟶ L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `K` a compact subset included in a compact subset `L`, there
is a map sending open neighbourhoods of `L` to the ones of `K`
-/
def baseChangeOpenNhds {K L : Compacts α} (h : K ⟶ L) : L.openNhds → K.openNhds :=
  fun ⟨U, hU⟩ ↦ ⟨U, fun _ hx ↦ Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩
/-
**TopologicalSpace.Compacts.baseChangeOpenNhds_mono** 是 Mathlib 中的一个引理，位于命名空间 `T
opologicalSpace.Compacts`。
形式化陈述：baseChangeOpenNhds_mono {K L : Compacts α} (h : K ⟶ L) : Monotone baseChan
geOpenNhds h
参数：h : K ⟶ L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
-/
lemma baseChangeOpenNhds_mono {K L : Compacts α} (h : K ⟶ L) : Monotone <| baseChangeOpenNhds h :=
  fun _ _ hUV _ hx ↦ SetLike.mem_coe.mpr (hUV hx)

@[simp]
/-
**TopologicalSpace.Compacts.baseChangeOpenNhds_comp** 是 Mathlib 中的一个引理，位于命名空间 `T
opologicalSpace.Compacts`。
形式化陈述：baseChangeOpenNhds_comp {K L M : Compacts α} (h : K ⟶ L) (k : L ⟶ M) (U : 
M.openNhds) : baseChangeOpenNhds (h ≫ k) U = baseChangeOpenNhds h (baseChangeOpe
nNhds k U)
参数：h : K ⟶ L；k : L ⟶ M；U : M.openNhds。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma baseChangeOpenNhds_comp {K L M : Compacts α} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds) :
  baseChangeOpenNhds (h ≫ k) U = baseChangeOpenNhds h (baseChangeOpenNhds k U) := by rfl

@[simp]
/-
**TopologicalSpace.Compacts.baseChangeOpenNhds_id** 是 Mathlib 中的一个引理，位于命名空间 `Top
ologicalSpace.Compacts`。
形式化陈述：baseChangeOpenNhds_id {K : Compacts α} (U : K.openNhds) : baseChangeOpenNh
ds (𝟙 K) U = U
参数：U : K.openNhds。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma baseChangeOpenNhds_id {K : Compacts α} (U : K.openNhds) :
  baseChangeOpenNhds (𝟙 K) U = U := by rfl

/-- The evidence that `⊥` is initial among the compact open neighbourhoods of `⊥` -/
/-
**TopologicalSpace.Compacts.isInitialBotOpensOpenNhdsBot** 是 Mathlib 中的一个定义，位于命名
空间 `TopologicalSpace.Compacts`。
形式化陈述：isInitialBotOpensOpenNhdsBot : IsInitial (⊥ : (⊥ : Compacts α).openNhds)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evidence that `⊥` is initial among the compact open neighbourhoods of `⊥`
-/
def isInitialBotOpensOpenNhdsBot : IsInitial (⊥ : (⊥ : Compacts α).openNhds) := .ofUniqueHom
  (fun _ ↦ homOfLE <| by tauto)
  (fun _ _ ↦ eq_of_comp_right_eq <| by tauto)
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Compacts α} [T2Space α] [LocallyCompactSpace α] :
    K.openRcNhdsToOpenNhds_mono.functor.Initial := by
  rw [Monotone.initial_functor_iff]
  intro U
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_between K.isCompact U.val.isOpen U.property
  use ⟨⟨interior L, isOpen_interior⟩,
    ⟨IsCompact.of_isClosed_subset h1 isClosed_closure
      (closure_minimal interior_subset (IsCompact.isClosed h1)),
    h2⟩⟩
  exact Subset.trans interior_subset h3
/-
**TopologicalSpace.Compacts.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Compact
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Compacts α} [T2Space α] : K.openRcNhdsToCompactNhds_mono.functor.Initial := by
  rw [Monotone.initial_functor_iff]
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_set_nhds_of_compactsNhds L
  have h3 : closure (U : Set α) ⊆ L := (IsClosed.closure_subset_iff
    (IsCompact.isClosed L.1.isCompact') ).2 h2
  exact ⟨⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩, h3⟩

end Compacts

end TopologicalSpace

