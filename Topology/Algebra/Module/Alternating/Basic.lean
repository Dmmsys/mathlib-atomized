/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous alternating multilinear maps

In this file we define bundled continuous alternating maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and alternating maps.

## Notation

`M [⋀^ι]→L[R] N`: notation for `R`-linear continuous alternating maps from `M` to `N`; the arguments
are indexed by `i : ι`.

## Keywords

multilinear map, alternating map, continuous
-/

@[expose] public section

open Function Matrix

/-- A continuous alternating map from `ι → M` to `N`, denoted `M [⋀^ι]→L[R] N`,
is a continuous map that is

- multilinear : `f (update m i (c • x)) = c • f (update m i x)` and
  `f (update m i (x + y)) = f (update m i x) + f (update m i y)`;
- alternating : `f v = 0` whenever `v` has two equal coordinates.
-/
/-
**ContinuousAlternatingMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (M : Type u_2) →     (N : Type u_3) →       Type u_4 → 
        [inst : Semiring R] →           [inst_1 : AddCommMonoid M] →            
 [_root_.Module R M] →               [TopologicalSpace M] →                 [ins
t_4 : AddCommMonoid N] → [_root_.Module R N] → [TopologicalSpace N] → Type (max 
(max u_2 u_3) u_4)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous alternating map from `ι → M` to `N`, denoted `M [⋀^ι]→L[R] N`,
is a continuous map that is

- multilinear : `f (update m i (c • x)) = c • f (update m i x)` and
  `f (update m i (x + y)) = f (update m i x) + f (update m i y)`;
- alternating : `f v = 0` whenever `v` has two equal coordinates.
-/
structure ContinuousAlternatingMap (R M N ι : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι => M) N, M [⋀^ι]→ₗ[R] N where

/-- Projection to `ContinuousMultilinearMap`s. -/
add_decl_doc ContinuousAlternatingMap.toContinuousMultilinearMap

/-- Projection to `AlternatingMap`s. -/
add_decl_doc ContinuousAlternatingMap.toAlternatingMap

@[inherit_doc]
notation M " [⋀^" ι "]→L[" R "] " N:100 => ContinuousAlternatingMap R M N ι

namespace ContinuousAlternatingMap

section Semiring

variable {R M M' N N' ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : M [⋀^ι]→L[R] N)

/-
**ContinuousAlternatingMap.toContinuousMultilinearMap_injective** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} {ι : Type u_6} [inst : Semi
ring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Topo
logicalSpace M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R N]   [inst_
6 : TopologicalSpace N], Function.Injective ContinuousAlternatingMap.toContinuou
sMultilinearMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousMultilinearMap_injective :
    Injective (ContinuousAlternatingMap.toContinuousMultilinearMap :
      M [⋀^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι => M) N)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**ContinuousAlternatingMap.range_toContinuousMultilinearMap** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousAlternatingMap`。
形式化陈述：range_toContinuousMultilinearMap : Set.range (toContinuousMultilinearMap :
 M [⋀^ι]->L[R] N -> ContinuousMultilinearMap R (fun _ : ι => M) N) = {f | forall
 (v : ι -> M) (i j : ι), v i = v j -> i != j -> f v = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ContinuousAlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} {M : Type 
u_2} {N : Type u_3} {ι : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M
]   [inst_2 : _root_.Module R M] …
-/
theorem range_toContinuousMultilinearMap :
    Set.range
        (toContinuousMultilinearMap :
          M [⋀^ι]→L[R] N → ContinuousMultilinearMap R (fun _ : ι => M) N) =
      {f | ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → f v = 0} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩
/-
**ContinuousAlternatingMap.funLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：funLike : FunLike (M [⋀^ι]->L[R] N) (ι -> M) N where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (M [⋀^ι]→L[R] N) (ι → M) N where
  coe f := f.toFun
  coe_injective _ _ h := toContinuousMultilinearMap_injective <| DFunLike.ext' h
/-
**ContinuousAlternatingMap.continuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：continuousMapClass : ContinuousMapClass (M [⋀^ι]->L[R] N) (ι -> M) N where
 map_continuous f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
instance continuousMapClass : ContinuousMapClass (M [⋀^ι]→L[R] N) (ι → M) N where
  map_continuous f := f.cont

initialize_simps_projections ContinuousAlternatingMap (toFun → apply)

@[continuity]
/-
**ContinuousAlternatingMap.coe_continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：coe_continuous : Continuous f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
-/
theorem coe_continuous : Continuous f := f.cont

@[simp]
/-
**ContinuousAlternatingMap.coe_toContinuousMultilinearMap** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternati
ngMap`。
形式化陈述：coe_mk (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h) : ⇑(mk f h)
 = f
参数：f : ContinuousMultilinearMap R (fun _ : ι => M) N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h) : ⇑(mk f h) = f :=
  rfl

-- not a `simp` lemma because this projection is a reducible call to `mk`, so `simp` can prove
-- this lemma
/-
**ContinuousAlternatingMap.coe_toAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAlternatingMap`。
形式化陈述：coe_toAlternatingMap : ⇑f.toAlternatingMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlternatingMap : ⇑f.toAlternatingMap = f := rfl

@[ext]
/-
**ContinuousAlternatingMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingM
ap`。
形式化陈述：ext {f g : M [⋀^ι]->L[R] N} (H : forall x, f x = g x) : f = g
参数：H : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : M [⋀^ι]→L[R] N} (H : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ H
/-
**ContinuousAlternatingMap.toAlternatingMap_injective** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：toAlternatingMap_injective : Injective (toAlternatingMap : (M [⋀^ι]->L[R] 
N) -> (M [⋀^ι]->ₗ[R] N))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem toAlternatingMap_injective :
    Injective (toAlternatingMap : (M [⋀^ι]→L[R] N) → (M [⋀^ι]→ₗ[R] N)) := fun f g h =>
  DFunLike.ext' <| by convert! DFunLike.ext'_iff.1 h

@[simp]
/-
**ContinuousAlternatingMap.range_toAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAlternatingMap`。
形式化陈述：range_toAlternatingMap : Set.range (toAlternatingMap : M [⋀^ι]->L[R] N -> 
(M [⋀^ι]->ₗ[R] N)) = {f : M [⋀^ι]->ₗ[R] N | Continuous f}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ContinuousMultilinearMap.cont`：∀ {R : Type u} {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid (M₁
 i)] [inst_2 : AddC…
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem range_toAlternatingMap :
    Set.range (toAlternatingMap : M [⋀^ι]→L[R] N → (M [⋀^ι]→ₗ[R] N)) =
      {f : M [⋀^ι]→ₗ[R] N | Continuous f} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, DFunLike.ext' rfl⟩⟩

@[simp]
/-
**ContinuousAlternatingMap.map_update_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：map_update_add [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M) : f (update 
m i (x + y)) = f (update m i x) + f (update m i y)
参数：m : ι -> M；i : ι；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_add'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
-/
theorem map_update_add [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_update_add' m i x y

@[simp]
/-
**ContinuousAlternatingMap.map_update_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：map_update_smul [DecidableEq ι] (m : ι -> M) (i : ι) (c : R) (x : M) : f (
update m i (c • x)) = c • f (update m i x)
参数：m : ι -> M；i : ι；c : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_smul'`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι →
 Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid
 (M₁ i)] [inst_2 : Ad…
-/
theorem map_update_smul [DecidableEq ι] (m : ι → M) (i : ι) (c : R) (x : M) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_update_smul' m i c x
/-
**ContinuousAlternatingMap.map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：map_coord_zero {m : ι -> M} (i : ι) (h : m i = 0) : f m = 0
参数：i : ι；h : m i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
-/
theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h

@[simp]
/-
**ContinuousAlternatingMap.map_update_zero** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：map_update_zero [DecidableEq ι] (m : ι -> M) (i : ι) : f (update m i 0) = 
0
参数：m : ι -> M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_zero`：map_update_zero [DecidableEq ι] (m : for
all i, M₁ i) (i : ι) : f (update m i 0) = 0
-/
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i

@[simp]
/-
**ContinuousAlternatingMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：map_zero [Nonempty ι] : f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
-/
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
/-
**ContinuousAlternatingMap.map_eq_zero_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：map_eq_zero_of_eq (v : ι -> M) {i j : ι} (h : v i = v j) (hij : i != j) : 
f v = 0
参数：v : ι -> M；h : v i = v j；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} {M : Type 
u_2} {N : Type u_3} {ι : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M
]   [inst_2 : _root_.Module R M] …
-/
theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij
/-
**ContinuousAlternatingMap.map_eq_zero_of_not_injective** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAlternatingMap`。
形式化陈述：map_eq_zero_of_not_injective (v : ι -> M) (hv : ¬Function.Injective v) : f
 v = 0
参数：v : ι -> M；hv : ¬Function.Injective v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_not_injective`：map_eq_zero_of_not_injectiv
e (v : ι -> M) (hv : ¬Function.Injective v) : f v = 0
-/
theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
  f.toAlternatingMap.map_eq_zero_of_not_injective v hv

/-- Restrict the codomain of a continuous alternating map to a submodule. -/
@[simps!]
/-
**ContinuousAlternatingMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：codRestrict (f : M [⋀^ι]->L[R] N) (p : Submodule R N) (h : forall v, f v i
n p) : M [⋀^ι]->L[R] p
参数：f : M [⋀^ι]->L[R] N；p : Submodule R N；h : forall v, f v in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a continuous alternating map to a submodule.
-/
def codRestrict (f : M [⋀^ι]→L[R] N) (p : Submodule R N) (h : ∀ v, f v ∈ p) : M [⋀^ι]→L[R] p :=
  { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M [⋀^ι]→L[R] N) :=
  ⟨⟨0, (0 : M [⋀^ι]→ₗ[R] N).map_eq_zero_of_eq⟩⟩
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M [⋀^ι]→L[R] N) :=
  ⟨0⟩

@[simp]
/-
**ContinuousAlternatingMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：coe_zero : ⇑(0 : M [⋀^ι]->L[R] N) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : M [⋀^ι]→L[R] N) = 0 :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMap_zero** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMap_zero : (0 : M [⋀^ι]->L[R] N).toContinuousMultil
inearMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousMultilinearMap_zero : (0 : M [⋀^ι]→L[R] N).toContinuousMultilinearMap = 0 :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toAlternatingMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：toAlternatingMap_zero : (0 : M [⋀^ι]->L[R] N).toAlternatingMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlternatingMap_zero : (0 : M [⋀^ι]→L[R] N).toAlternatingMap = 0 :=
  rfl

section SMul

variable {R' R'' A : Type*} [Monoid R'] [Monoid R''] [Semiring A] [Module A M] [Module A N]
  [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N] [DistribMulAction R'' N]
  [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R' (M [⋀^ι]→L[A] N) :=
  ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
/-
**ContinuousAlternatingMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：coe_smul (f : M [⋀^ι]->L[A] N) (c : R') : ⇑(c • f) = c • ⇑f
参数：f : M [⋀^ι]->L[A] N；c : R'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (f : M [⋀^ι]→L[A] N) (c : R') : ⇑(c • f) = c • ⇑f :=
  rfl
/-
**ContinuousAlternatingMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlter
natingMap`。
形式化陈述：smul_apply (f : M [⋀^ι]->L[A] N) (c : R') (v : ι -> M) : (c • f) v = c • f
 v
参数：f : M [⋀^ι]->L[A] N；c : R'；v : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (f : M [⋀^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMap_smul** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMap_smul (c : R') (f : M [⋀^ι]->L[A] N) : (c • f).t
oContinuousMultilinearMap = c • f.toContinuousMultilinearMap
参数：c : R'；f : M [⋀^ι]->L[A] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousMultilinearMap_smul (c : R') (f : M [⋀^ι]→L[A] N) :
    (c • f).toContinuousMultilinearMap = c • f.toContinuousMultilinearMap :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toAlternatingMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：toAlternatingMap_smul (c : R') (f : M [⋀^ι]->L[A] N) : (c • f).toAlternati
ngMap = c • f.toAlternatingMap
参数：c : R'；f : M [⋀^ι]->L[A] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlternatingMap_smul (c : R') (f : M [⋀^ι]→L[A] N) :
    (c • f).toAlternatingMap = c • f.toAlternatingMap :=
  rfl
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' (M [⋀^ι]→L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' (M [⋀^ι]→L[A] N) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] : IsCentralScalar R' (M [⋀^ι]→L[A] N) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction R' (M [⋀^ι]→L[A] N) := fast_instance%
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M [⋀^ι]→L[R] N) :=
  ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
/-
**ContinuousAlternatingMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：coe_add : ⇑(f + g) = ⇑f + ⇑g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add : ⇑(f + g) = ⇑f + ⇑g :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：add_apply (v : ι -> M) : (f + g) v = f v + g v
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMap_add** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMap_add (f g : M [⋀^ι]->L[R] N) : (f + g).1 = f.1 +
 g.1
参数：f g : M [⋀^ι]->L[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousMultilinearMap_add (f g : M [⋀^ι]→L[R] N) : (f + g).1 = f.1 + g.1 :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.toAlternatingMap_add** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAlternatingMap`。
形式化陈述：toAlternatingMap_add (f g : M [⋀^ι]->L[R] N) : (f + g).toAlternatingMap = 
f.toAlternatingMap + g.toAlternatingMap
参数：f g : M [⋀^ι]->L[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlternatingMap_add (f g : M [⋀^ι]→L[R] N) :
    (f + g).toAlternatingMap = f.toAlternatingMap + g.toAlternatingMap :=
  rfl
/-
**ContinuousAlternatingMap.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：addCommMonoid : AddCommMonoid (M [⋀^ι]->L[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (M [⋀^ι]→L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/-- Evaluation of a `ContinuousAlternatingMap` at a vector as an `AddMonoidHom`. -/
/-
**ContinuousAlternatingMap.applyAddHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：applyAddHom (v : ι -> M) : M [⋀^ι]->L[R] N ->+ N
参数：v : ι -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of a `ContinuousAlternatingMap` at a vector as an `AddMonoidHom`.
-/
def applyAddHom (v : ι → M) : M [⋀^ι]→L[R] N →+ N :=
  ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩

@[simp]
/-
**ContinuousAlternatingMap.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：sum_apply {α : Type*} (f : α -> M [⋀^ι]->L[R] N) (m : ι -> M) {s : Finset 
α} : (∑ a in s, f a) m = ∑ a in s, f a m
参数：f : α -> M [⋀^ι]->L[R] N；m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_apply {α : Type*} (f : α → M [⋀^ι]→L[R] N) (m : ι → M) {s : Finset α} :
    (∑ a ∈ s, f a) m = ∑ a ∈ s, f a m :=
  map_sum (applyAddHom m) f s

/-- Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`. -/
@[simps]
/-
**ContinuousAlternatingMap.toMultilinearAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousAlternatingMap`。
形式化陈述：toMultilinearAddHom : M [⋀^ι]->L[R] N ->+ ContinuousMultilinearMap R (fun 
_ : ι => M) N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`.
-/
def toMultilinearAddHom : M [⋀^ι]→L[R] N →+ ContinuousMultilinearMap R (fun _ : ι => M) N :=
  ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩

end ContinuousAdd

/-- If `f` is a continuous alternating map, then `f.toContinuousLinearMap m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
@[simps! apply]
/-
**ContinuousAlternatingMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：toContinuousLinearMap [DecidableEq ι] (m : ι -> M) (i : ι) : M ->L[R] N
参数：m : ι -> M；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a continuous alternating map, then `f.toContinuousLinearMap m i` is th
e continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and
 varying the
`i`-th coordinate.
-/
def toContinuousLinearMap [DecidableEq ι] (m : ι → M) (i : ι) : M →L[R] N :=
  f.1.toContinuousLinearMap m i

/-- The Cartesian product of two continuous alternating maps, as a continuous alternating map. -/
@[simps!]
/-
**ContinuousAlternatingMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternating
Map`。
形式化陈述：prod (f : M [⋀^ι]->L[R] N) (g : M [⋀^ι]->L[R] N') : M [⋀^ι]->L[R] (N × N')
参数：f : M [⋀^ι]->L[R] N；g : M [⋀^ι]->L[R] N'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two continuous alternating maps, as a continuous altern
ating map.
-/
def prod (f : M [⋀^ι]→L[R] N) (g : M [⋀^ι]→L[R] N') : M [⋀^ι]→L[R] (N × N') :=
  ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩

/-- Combine a family of continuous alternating maps with the same domain and codomains `M' i` into a
continuous alternating map taking values in the space of functions `Π i, M' i`. -/
/-
**ContinuousAlternatingMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMa
p`。
形式化陈述：pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [foral
l i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, M [⋀^ι]
->L[R] M' i) : M [⋀^ι]->L[R] forall i, M' i
参数：M' i；M' i；M' i；f : forall i, M [⋀^ι]->L[R] M' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of continuous alternating maps with the same domain and codomai
ns `M' i` into a
continuous alternating map taking values in the space of functions `Π i, M' i`.
-/
def pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, M [⋀^ι]→L[R] M' i) : M [⋀^ι]→L[R] ∀ i, M' i :=
  ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩

@[simp]
/-
**ContinuousAlternatingMap.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternati
ngMap`。
形式化陈述：coe_pi {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] [f
orall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, M [
⋀^ι]->L[R] M' i) : ⇑(pi f) = fun m j => f j m
参数：M' i；M' i；M' i；f : forall i, M [⋀^ι]->L[R] M' i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [⋀^ι]→L[R] M' i) :
    ⇑(pi f) = fun m j => f j m :=
  rfl
/-
**ContinuousAlternatingMap.pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：pi_apply {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M' i)] 
[forall i, TopologicalSpace (M' i)] [forall i, Module R (M' i)] (f : forall i, M
 [⋀^ι]->L[R] M' i) (m : ι -> M) (j : ι') : pi f m j = f j m
参数：M' i；M' i；M' i；f : forall i, M [⋀^ι]->L[R] M' i；m : ι -> M；j : ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_apply {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M [⋀^ι]→L[R] M' i) (m : ι → M)
    (j : ι') : pi f m j = f j m :=
  rfl

section

variable (R M N)

/-- The natural equivalence between continuous linear maps from `M` to `N`
and continuous 1-multilinear alternating maps from `M` to `N`. -/
@[simps! apply_apply symm_apply_apply apply_toContinuousMultilinearMap]
/-
**ContinuousAlternatingMap.ofSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：ofSubsingleton [Subsingleton ι] (i : ι) : (M ->L[R] N) ≃ M [⋀^ι]->L[R] N w
here toFun f
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural equivalence between continuous linear maps from `M` to `N`
and continuous 1-multilinear alternating maps from `M` to `N`.
-/
def ofSubsingleton [Subsingleton ι] (i : ι) :
    (M →L[R] N) ≃ M [⋀^ι]→L[R] N where
  toFun f :=
    { AlternatingMap.ofSubsingleton R M N i f with
      toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R M N i f }
  invFun f := (ContinuousMultilinearMap.ofSubsingleton R M N i).symm f.1
  right_inv _ := toContinuousMultilinearMap_injective <|
    (ContinuousMultilinearMap.ofSubsingleton R M N i).apply_symm_apply _

@[simp]
/-
**ContinuousAlternatingMap.ofSubsingleton_toAlternatingMap** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：ofSubsingleton_toAlternatingMap [Subsingleton ι] (i : ι) (f : M ->L[R] N) 
: (ofSubsingleton R M N i f).toAlternatingMap = AlternatingMap.ofSubsingleton R 
M N i f
参数：i : ι；f : M ->L[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubsingleton_toAlternatingMap [Subsingleton ι] (i : ι) (f : M →L[R] N) :
    (ofSubsingleton R M N i f).toAlternatingMap = AlternatingMap.ofSubsingleton R M N i f :=
  rfl

variable (ι) {N}

/-- The constant map is alternating when `ι` is empty. -/
@[simps! toContinuousMultilinearMap apply]
/-
**ContinuousAlternatingMap.constOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]->L[R] N
参数：m : N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…

--- 原说明 ---
The constant map is alternating when `ι` is empty.
-/
def constOfIsEmpty [IsEmpty ι] (m : N) : M [⋀^ι]→L[R] N :=
  { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }

@[simp]
/-
**ContinuousAlternatingMap.constOfIsEmpty_toAlternatingMap** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：constOfIsEmpty_toAlternatingMap [IsEmpty ι] (m : N) : (constOfIsEmpty R M 
ι m).toAlternatingMap = AlternatingMap.constOfIsEmpty R M ι m
参数：m : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constOfIsEmpty_toAlternatingMap [IsEmpty ι] (m : N) :
    (constOfIsEmpty R M ι m).toAlternatingMap = AlternatingMap.constOfIsEmpty R M ι m :=
  rfl

end

/-- If `g` is continuous alternating and `f` is a continuous linear map, then `g (f m₁, ..., f mₙ)`
is again a continuous alternating map, that we call `g.compContinuousLinearMap f`. -/
/-
**ContinuousAlternatingMap.compContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousAlternatingMap`。
形式化陈述：compContinuousLinearMap (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) : M' [⋀^ι]
->L[R] N
参数：g : M [⋀^ι]->L[R] N；f : M' ->L[R] M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…

--- 原说明 ---
If `g` is continuous alternating and `f` is a continuous linear map, then `g (f 
m₁, ..., f mₙ)`
is again a continuous alternating map, that we call `g.compContinuousLinearMap f
`.
-/
def compContinuousLinearMap (g : M [⋀^ι]→L[R] N) (f : M' →L[R] M) : M' [⋀^ι]→L[R] N :=
  { g.toAlternatingMap.compLinearMap (f : M' →ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }

@[simp]
/-
**ContinuousAlternatingMap.compContinuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousAlternatingMap`。
形式化陈述：compContinuousLinearMap_apply (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) (m :
 ι -> M') : g.compContinuousLinearMap f m = g (f ∘ m)
参数：g : M [⋀^ι]->L[R] N；f : M' ->L[R] M；m : ι -> M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compContinuousLinearMap_apply (g : M [⋀^ι]→L[R] N) (f : M' →L[R] M) (m : ι → M') :
    g.compContinuousLinearMap f m = g (f ∘ m) :=
  rfl

/-- Composing a continuous alternating map with a continuous linear map gives again a
continuous alternating map. -/
/-
**ContinuousAlternatingMap._root_.ContinuousLinearMap.compContinuousAlternatingM
ap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a continuous alternating map with a continuous linear map gives again 
a
continuous alternating map.
-/
def _root_.ContinuousLinearMap.compContinuousAlternatingMap (g : N →L[R] N') (f : M [⋀^ι]→L[R] N) :
    M [⋀^ι]→L[R] N' :=
  { (g : N →ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }

@[simp]
/-
**ContinuousAlternatingMap._root_.ContinuousLinearMap.compContinuousAlternatingM
ap_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe (g : N →L[R] N')
    (f : M [⋀^ι]→L[R] N) : ⇑(g.compContinuousAlternatingMap f) = g ∘ f :=
  rfl

/-- A continuous linear equivalence of domains
defines an equivalence between continuous alternating maps.

This is available as a continuous linear isomorphism at
`ContinuousLinearEquiv.continuousAlternatingMapCongrLeft`.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence. -/
@[simps -fullyApplied apply]
/-
**ContinuousAlternatingMap._root_.ContinuousLinearEquiv.continuousAlternatingMap
CongrLeftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence of domains
defines an equivalence between continuous alternating maps.

This is available as a continuous linear isomorphism at
`ContinuousLinearEquiv.continuousAlternatingMapCongrLeft`.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence.
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrLeftEquiv (e : M ≃L[R] M') :
    M [⋀^ι]→L[R] N ≃ M' [⋀^ι]→L[R] N where
  toFun f := f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [Function.comp_def]
  right_inv f := by ext; simp [Function.comp_def]

/-- A continuous linear equivalence of codomains
defines an equivalence between continuous alternating maps. -/
@[simps -fullyApplied apply]
/-
**ContinuousAlternatingMap._root_.ContinuousLinearEquiv.continuousAlternatingMap
CongrRightEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous linear equivalence of codomains
defines an equivalence between continuous alternating maps.
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRightEquiv (e : N ≃L[R] N') :
    M [⋀^ι]→L[R] N ≃ M [⋀^ι]→L[R] N' where
  toFun := (e : N →L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' →L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]

@[simp]
/-
**ContinuousAlternatingMap._root_.ContinuousLinearEquiv.compContinuousAlternatin
gMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe
    (e : N ≃L[R] N') (f : M [⋀^ι]→L[R] N) :
    ⇑(e.continuousAlternatingMapCongrRightEquiv f) = e ∘ f :=
  rfl

/-- Continuous linear equivalences between domains and codomains
define an equivalence between the spaces of continuous alternating maps. -/
/-
**ContinuousAlternatingMap._root_.ContinuousLinearEquiv.continuousAlternatingMap
CongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous linear equivalences between domains and codomains
define an equivalence between the spaces of continuous alternating maps.
-/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrEquiv
    (e : M ≃L[R] M') (e' : N ≃L[R] N') : M [⋀^ι]→L[R] N ≃ M' [⋀^ι]→L[R] N' :=
  e.continuousAlternatingMapCongrLeftEquiv.trans e'.continuousAlternatingMapCongrRightEquiv

/-- `ContinuousAlternatingMap.pi` as an `Equiv`. -/
@[simps]
/-
**ContinuousAlternatingMap.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：piEquiv {ι' : Type*} {N : ι' -> Type*} [forall i, AddCommMonoid (N i)] [fo
rall i, TopologicalSpace (N i)] [forall i, Module R (N i)] : (forall i, M [⋀^ι]-
>L[R] N i) ≃ M [⋀^ι]->L[R] forall i, N i where toFun
参数：N i；N i；N i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlternatingMap.pi` as an `Equiv`.
-/
def piEquiv {ι' : Type*} {N : ι' → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, TopologicalSpace (N i)]
    [∀ i, Module R (N i)] : (∀ i, M [⋀^ι]→L[R] N i) ≃ M [⋀^ι]→L[R] ∀ i, N i where
  toFun := pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] N i).compContinuousAlternatingMap f

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of an alternating map along the first variable. -/
/-
**ContinuousAlternatingMap.cons_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：cons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n -> 
M) (x y : M) : f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m)
参数：f : ContinuousAlternatingMap R M N (Fin (n + 1))；m : Fin n -> M；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_add`：cons_add (f : MultilinearMap R M M₂) (m : foral
l i : Fin n, M i.succ) (x y : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons
 y m)

--- 原说明 ---
In the specific case of continuous alternating maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express di
rectly the
additivity of an alternating map along the first variable.
-/
theorem cons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of an alternating map along the first variable. -/
/-
**ContinuousAlternatingMap.vecCons_add** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：vecCons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n 
-> M) (x y : M) : f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m)
参数：f : ContinuousAlternatingMap R M N (Fin (n + 1))；m : Fin n -> M；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_add`：cons_add (f : MultilinearMap R M M₂) (m : foral
l i : Fin n, M i.succ) (x y : M 0) : f (cons (x + y) m) = f (cons x m) + f (cons
 y m)

--- 原说明 ---
In the specific case of continuous alternating maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express di
rectly the
additivity of an alternating map along the first variable.
-/
theorem vecCons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m) :=
  f.toMultilinearMap.cons_add m x y

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of an alternating map along the first variable. -/
/-
**ContinuousAlternatingMap.cons_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：cons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n ->
 M) (c : R) (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m)
参数：f : ContinuousAlternatingMap R M N (Fin (n + 1))；m : Fin n -> M；c : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_smul`：cons_smul (f : MultilinearMap R M M₂) (m : for
all i : Fin n, M i.succ) (c : R) (x : M 0) : f (cons (c • x) m) = c • f (cons x 
m)

--- 原说明 ---
In the specific case of continuous alternating maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express di
rectly the
multiplicativity of an alternating map along the first variable.
-/
theorem cons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m) :=
  f.toMultilinearMap.cons_smul m c x

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of an alternating map along the first variable. -/
/-
**ContinuousAlternatingMap.vecCons_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlt
ernatingMap`。
形式化陈述：vecCons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n
 -> M) (c : R) (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m)
参数：f : ContinuousAlternatingMap R M N (Fin (n + 1))；m : Fin n -> M；c : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.cons_smul`：cons_smul (f : MultilinearMap R M M₂) (m : for
all i : Fin n, M i.succ) (c : R) (x : M 0) : f (cons (c • x) m) = c • f (cons x 
m)

--- 原说明 ---
In the specific case of continuous alternating maps on spaces indexed by `Fin (n
+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express di
rectly the
multiplicativity of an alternating map along the first variable.
-/
theorem vecCons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m) :=
  f.toMultilinearMap.cons_smul m c x
/-
**ContinuousAlternatingMap.map_piecewise_add** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：map_piecewise_add [DecidableEq ι] (m m' : ι -> M) (t : Finset ι) : f (t.pi
ecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m')
参数：m m' : ι -> M；t : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_piecewise_add`：map_piecewise_add [DecidableEq ι] (m m
' : forall i, M₁ i) (t : Finset ι) : f (t.piecewise (m + m') m') = ∑ s in t.powe
rset, f (s.piecewise m…
-/
theorem map_piecewise_add [DecidableEq ι] (m m' : ι → M) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _

/-- Additivity of a continuous alternating map along all coordinates at the same time,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`. -/
/-
**ContinuousAlternatingMap.map_add_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlt
ernatingMap`。
形式化陈述：map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι -> M) : f (m + m') = ∑ 
s : Finset ι, f (s.piecewise m m')
参数：m m' : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_add_univ`：map_add_univ [DecidableEq ι] [Fintype ι] (m
 m' : forall i, M₁ i) : f (m + m') = ∑ s : Finset ι, f (s.piecewise m m')

--- 原说明 ---
Additivity of a continuous alternating map along all coordinates at the same tim
e,
writing `f (m + m')` as the sum of `f (s.piecewise m m')` over all sets `s`.
-/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _

section ApplySum

open Fintype Finset

variable {α : ι → Type*} [Fintype ι] [DecidableEq ι] (g' : ∀ i, α i → M) (A : ∀ i, Finset (α i))

/-- If `f` is continuous alternating, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
/-
**ContinuousAlternatingMap.map_sum_finset** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：map_sum_finset : (f fun i => ∑ j in A i, g' i j) = ∑ r in piFinset A, f fu
n i => g' i (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum_finset`：map_sum_finset [DecidableEq ι] [Fintype ι
] : (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i)

--- 原说明 ---
If `f` is continuous alternating, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} g
ₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r
 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with resp
ect to each
coordinate.
-/
theorem map_sum_finset :
    (f fun i => ∑ j ∈ A i, g' i j) = ∑ r ∈ piFinset A, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _

/-- If `f` is continuous alternating, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
/-
**ContinuousAlternatingMap.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：map_sum [forall i, Fintype (α i)] : (f fun i => ∑ j, g' i j) = ∑ r : foral
l i, α i, f fun i => g' i (r i)
参数：α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_sum`：map_sum [DecidableEq ι] [Fintype ι] [forall i, F
intype (α i)] : (f fun i => ∑ j, g i j) = ∑ r : forall i, α i, f fun i => g i (r
 i)

--- 原说明 ---
If `f` is continuous alternating, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is 
the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This foll
ows from
multilinearity by expanding successively with respect to each coordinate.
-/
theorem map_sum [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g' i j) = ∑ r : ∀ i, α i, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum _

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type*} [Semiring A] [SMul R A] [Module A M] [Module A N] [IsScalarTower R A M]
  [IsScalarTower R A N]

/-- Reinterpret a continuous `A`-alternating map as a continuous `R`-alternating map, if `A` is an
algebra over `R` and their actions on all involved modules agree with the action of `R` on `A`. -/
/-
**ContinuousAlternatingMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：restrictScalars (f : M [⋀^ι]->L[A] N) : M [⋀^ι]->L[R] N
参数：f : M [⋀^ι]->L[A] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} {M : Type 
u_2} {N : Type u_3} {ι : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M
]   [inst_2 : _root_.Module R M] …

--- 原说明 ---
Reinterpret a continuous `A`-alternating map as a continuous `R`-alternating map
, if `A` is an
algebra over `R` and their actions on all involved modules agree with the action
 of `R` on `A`.
-/
def restrictScalars (f : M [⋀^ι]→L[A] N) : M [⋀^ι]→L[R] N :=
  { f with toContinuousMultilinearMap := f.1.restrictScalars R }

@[simp]
/-
**ContinuousAlternatingMap.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAlternatingMap`。
形式化陈述：coe_restrictScalars (f : M [⋀^ι]->L[A] N) : ⇑(f.restrictScalars R) = f
参数：f : M [⋀^ι]->L[A] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (f : M [⋀^ι]→L[A] N) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalar

end Semiring

section Ring

variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]
  (f g : M [⋀^ι]→L[R] N)

@[simp]
/-
**ContinuousAlternatingMap.map_update_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：map_update_sub [DecidableEq ι] (m : ι -> M) (i : ι) (x y : M) : f (update 
m i (x - y)) = f (update m i x) - f (update m i y)
参数：m : ι -> M；i : ι；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_update_sub`：map_update_sub [DecidableEq ι] (m : foral
l i, M₁ i) (i : ι) (x y : M₁ i) : f (update m i (x - y)) = f (update m i x) - f 
(update m i y)
-/
theorem map_update_sub [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_update_sub _ _ _ _

@[simp]
/-
**ContinuousAlternatingMap.map_vecCons_sub** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：map_vecCons_sub {n} (f : M [⋀^Fin (n + 1)]->L[R] N) (x y : M) (v : Fin n -
> M) : f (Matrix.vecCons (x - y) v) = f (Matrix.vecCons x v) - f (Matrix.vecCons
 y v)
参数：f : M [⋀^Fin (n + 1)]->L[R] N；x y : M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecCons.eq_1`：∀ {α : Type u} {n : ℕ} (h : α) (t : Fin n → α), Mat
rix.vecCons h t = Fin.cons h t
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.update_cons_zero`：update_cons_zero : update (cons x p) 0 z = cons z 
p
· 使用定理 `ContinuousAlternatingMap.map_update_sub`：map_update_sub [DecidableEq ι] 
(m : ι -> M) (i : ι) (x y : M) : f (update m i (x - y)) = f (update m i x) - f (
update m i y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_vecCons_sub {n} (f : M [⋀^Fin (n + 1)]→L[R] N) (x y : M) (v : Fin n → M) :
    f (Matrix.vecCons (x - y) v) = f (Matrix.vecCons x v) - f (Matrix.vecCons y v) := by
  rw [vecCons, ← Fin.update_cons_zero 0, map_update_sub]
  simp [vecCons]

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup N]

/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M [⋀^ι]→L[R] N) :=
  ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]
/-
**ContinuousAlternatingMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：coe_neg : ⇑(-f) = -f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(-f) = -f :=
  rfl
/-
**ContinuousAlternatingMap.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：neg_apply (m : ι -> M) : (-f) m = -f m
参数：m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (m : ι → M) : (-f) m = -f m :=
  rfl
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (M [⋀^ι]→L[R] N) :=
  ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩
/-
**ContinuousAlternatingMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} {ι : Type u_4} [inst : Ring
 R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : Topologic
alSpace M] [inst_4 : AddCommGroup N] [inst_5 : _root_.Module R N]   [inst_6 : To
pologicalSpace N] (f g : M [⋀^ι]→L[R] N) [inst_7 : IsTopologicalAddGroup N], ⇑(f
 - g) = ⇑f - ⇑g
参数：f g : M [⋀^ι]→L[R] N；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_sub : ⇑(f - g) = ⇑f - ⇑g := rfl
/-
**ContinuousAlternatingMap.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：sub_apply (m : ι -> M) : (f - g) m = f m - g m
参数：m : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (M [⋀^ι]→L[R] N) := fast_instance%
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end IsTopologicalAddGroup

end Ring

section CommSemiring

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
  (f : M [⋀^ι]→L[R] N)

/-
**ContinuousAlternatingMap.map_piecewise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：map_piecewise_smul [DecidableEq ι] (c : ι -> R) (m : ι -> M) (s : Finset ι
) : f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m
参数：c : ι -> R；m : ι -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_piecewise_smul`：map_piecewise_smul [DecidableEq ι] (c
 : ι -> R) (m : forall i, M₁ i) (s : Finset ι) : f (s.piecewise (fun i => c i • 
m i) m) = (∏ i in s, c …
-/
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ι → M) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i ∈ s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous alternating map along all coordinates at the same time,
writing `f (fun i ↦ c i • m i)` as `(∏ i, c i) • f m`. -/
/-
**ContinuousAlternatingMap.map_smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：map_smul_univ [Fintype ι] (c : ι -> R) (m : ι -> M) : (f fun i => c i • m 
i) = (∏ i, c i) • f m
参数：c : ι -> R；m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι -> R) (m 
: forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m

--- 原说明 ---
Multiplicativity of a continuous alternating map along all coordinates at the sa
me time,
writing `f (fun i ↦ c i • m i)` as `(∏ i, c i) • f m`.
-/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ι → M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _

/-- If two continuous `R`-alternating maps from `R` are equal on 1, then they are equal.

This is the alternating version of `ContinuousLinearMap.ext_ring`. -/
@[ext]
/-
**ContinuousAlternatingMap.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：ext_ring [Finite ι] [TopologicalSpace R] ⦃f g : R [⋀^ι]->L[R] M⦄ (h : f (f
un _ => 1) = g (fun _ => 1)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.toAlternatingMap_injective`：toAlternatingMap_in
jective : Injective (toAlternatingMap : (M [⋀^ι]->L[R] N) -> (M [⋀^ι]->ₗ[R] N))
· 使用定理 `AlternatingMap.ext_ring`：ext_ring {R} [CommSemiring R] [Module R N] [Fin
ite ι] ⦃f g : R [⋀^ι]->ₗ[R] N⦄ (h : f (fun _ => 1) = g (fun _ => 1)) : f = g

--- 原说明 ---
If two continuous `R`-alternating maps from `R` are equal on 1, then they are eq
ual.

This is the alternating version of `ContinuousLinearMap.ext_ring`.
-/
theorem ext_ring [Finite ι] [TopologicalSpace R] ⦃f g : R [⋀^ι]→L[R] M⦄
    (h : f (fun _ ↦ 1) = g (fun _ ↦ 1)) : f = g :=
  toAlternatingMap_injective <| AlternatingMap.ext_ring h

/-- The only continuous `R`-alternating map from two or more copies of `R` is the zero map. -/
/-
**ContinuousAlternatingMap.uniqueOfCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Continuou
sAlternatingMap`。
形式化陈述：uniqueOfCommRing [Finite ι] [Nontrivial ι] [TopologicalSpace R] : Unique (
R [⋀^ι]->L[R] N) where uniq _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The only continuous `R`-alternating map from two or more copies of `R` is the ze
ro map.
-/
instance uniqueOfCommRing [Finite ι] [Nontrivial ι] [TopologicalSpace R] :
    Unique (R [⋀^ι]→L[R] N) where
  uniq _ := toAlternatingMap_injective <| Subsingleton.elim _ _

end CommSemiring

section DistribMulAction

variable {R A M N ι : Type*} [Monoid R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [Module A M] [Module A N] [DistribMulAction R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ContinuousAdd N] : DistribMulAction R (M [⋀^ι]→L[A] N) := fast_instance%
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

end DistribMulAction

section Module

variable {R A M N ι : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-- The space of continuous alternating maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
/-
**ContinuousAlternatingMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlternatingMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of continuous alternating maps over an algebra over `R` is a module ov
er `R`, for the
pointwise addition and scalar multiplication.
-/
instance : Module R (M [⋀^ι]→L[A] N) := fast_instance%
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

/-- Linear map version of the map `toMultilinearMap` associating to a continuous alternating map
the corresponding multilinear map. -/
@[simps]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMapLinear** 是 Mathlib 中的一个定义，位
于命名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMapLinear : M [⋀^ι]->L[A] N ->ₗ[R] ContinuousMultil
inearMap A (fun _ : ι => M) N where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear map version of the map `toMultilinearMap` associating to a continuous alt
ernating map
the corresponding multilinear map.
-/
def toContinuousMultilinearMapLinear :
    M [⋀^ι]→L[A] N →ₗ[R] ContinuousMultilinearMap A (fun _ : ι => M) N where
  toFun := toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear map version of the map `toAlternatingMap`
associating to a continuous alternating map the corresponding alternating map. -/
@[simps -fullyApplied apply]
/-
**ContinuousAlternatingMap.toAlternatingMapLinear** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousAlternatingMap`。
形式化陈述：toAlternatingMapLinear : (M [⋀^ι]->L[A] N) ->ₗ[R] (M [⋀^ι]->ₗ[A] N) where 
toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear map version of the map `toAlternatingMap`
associating to a continuous alternating map the corresponding alternating map.
-/
def toAlternatingMapLinear : (M [⋀^ι]→L[A] N) →ₗ[R] (M [⋀^ι]→ₗ[A] N) where
  toFun := toAlternatingMap
  map_add' := by simp
  map_smul' := by simp

/-- `ContinuousAlternatingMap.pi` as a `LinearEquiv`. -/
@[simps +simpRhs]
/-
**ContinuousAlternatingMap.piLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：piLinearEquiv {ι' : Type*} {M' : ι' -> Type*} [forall i, AddCommMonoid (M'
 i)] [forall i, TopologicalSpace (M' i)] [forall i, ContinuousAdd (M' i)] [foral
l i, Module R (M' i)] [forall i, Module A (M' i)] [forall i, SMulCommClass A R (
M' i)] [forall i, ContinuousConstSMul R (M' i)] : (forall i, M [⋀^ι]->L[A] M' i)
 ≃ₗ[R] M [⋀^ι]->L[A] forall i, M' i
参数：M' i；M' i；M' i；M' i；M' i；M' i；M' i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlternatingMap.pi` as a `LinearEquiv`.
-/
def piLinearEquiv {ι' : Type*} {M' : ι' → Type*} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R (M' i)] [∀ i, ContinuousConstSMul R (M' i)] :
    (∀ i, M [⋀^ι]→L[A] M' i) ≃ₗ[R] M [⋀^ι]→L[A] ∀ i, M' i :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end Module

section SMulRight

variable {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N] [ContinuousSMul R N]
  (f : M [⋀^ι]→L[R] R) (z : N)

/-- Given a continuous `R`-alternating map `f` taking values in `R`, `f.smulRight z` is the
continuous alternating map sending `m` to `f m • z`. -/
@[simps! toContinuousMultilinearMap apply]
/-
**ContinuousAlternatingMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：smulRight : M [⋀^ι]->L[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous `R`-alternating map `f` taking values in `R`, `f.smulRight z`
 is the
continuous alternating map sending `m` to `f m • z`.
-/
def smulRight : M [⋀^ι]→L[R] N :=
  { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }

end SMulRight

section Semiring

variable {R M M' N N' ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul R N] [AddCommMonoid N']
  [Module R N'] [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul R N']

/-- `ContinuousAlternatingMap.compContinuousLinearMap` as a bundled `LinearMap`. -/
@[simps]
/-
**ContinuousAlternatingMap.compContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Co
ntinuousAlternatingMap`。
形式化陈述：compContinuousLinearMap (g : M [⋀^ι]->L[R] N) (f : M' ->L[R] M) : M' [⋀^ι]
->L[R] N
参数：g : M [⋀^ι]->L[R] N；f : M' ->L[R] M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.map_eq_zero_of_eq'`：∀ {R : Type u_1} [inst : Semiring R] 
{M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Ty
pe u_3} [inst_3 : AddCo…

--- 原说明 ---
`ContinuousAlternatingMap.compContinuousLinearMap` as a bundled `LinearMap`.
-/
def compContinuousLinearMapₗ (f : M →L[R] M') : (M' [⋀^ι]→L[R] N) →ₗ[R] (M [⋀^ι]→L[R] N) where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

variable (R M N N')

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled bilinear map. -/
/-
**ContinuousAlternatingMap._root_.ContinuousLinearMap.compContinuousAlternatingM
ap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatingMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousLinearMap.compContinuousAlternatingMap` as a bundled bilinear map.
-/
def _root_.ContinuousLinearMap.compContinuousAlternatingMapₗ :
    (N →L[R] N') →ₗ[R] (M [⋀^ι]→L[R] N) →ₗ[R] (M [⋀^ι]→L[R] N') :=
  LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp

end Semiring

end ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [Fintype ι]
  [DecidableEq ι] (f : ContinuousMultilinearMap R (fun _ : ι => M) N)

/-- Alternatization of a continuous multilinear map. -/
@[simps -isSimp apply_toContinuousMultilinearMap]
/-
**ContinuousMultilinearMap.alternatization** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
MultilinearMap`。
形式化陈述：alternatization : ContinuousMultilinearMap R (fun _ : ι => M) N ->+ M [⋀^ι
]->L[R] N where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternatization of a continuous multilinear map.
-/
def alternatization : ContinuousMultilinearMap R (fun _ : ι => M) N →+ M [⋀^ι]→L[R] N where
  toFun f :=
    { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]
/-
**ContinuousMultilinearMap.alternatization_apply_apply** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousMultilinearMap`。
形式化陈述：alternatization_apply_apply (v : ι -> M) : alternatization f v = ∑ σ : Equ
iv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ)
参数：v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousMultilinearMap.instIsSMulApplyForall`：∀ {ι : Type v} {M₁ : ι →
 Type w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCo
mmMonoid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousMultilinearMap.domDomCongr_apply`：∀ {R : Type u} {ι : Type v} 
{M₂ : Type w₂} {M₃ : Type w₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   
[inst_2 : AddCommMonoid M₃] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatization_apply_apply (v : ι → M) :
    alternatization f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) := by
  simp [alternatization, Function.comp_def]

@[simp]
/-
**ContinuousMultilinearMap.alternatization_apply_toAlternatingMap** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousMultilinearMap`。
形式化陈述：alternatization_apply_toAlternatingMap : (alternatization f).toAlternating
Map = MultilinearMap.alternatization f.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMultilinearMap.alternatization_apply_apply`：alternatization_ap
ply_apply (v : ι -> M) : alternatization f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.si
gn σ • f (v ∘ σ)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MultilinearMap.alternatization_apply`：alternatization_apply (m : Multili
nearMap R (fun _ : ι => M) N') (v : ι -> M) : alternatization m v = ∑ σ : Perm ι
, Equiv.Perm.sign σ • m.do…
· 使用定理 `MultilinearMap.domDomCongr_apply`：∀ {R : Type uR} {M₂ : Type v₂} {M₃ : T
ype v₃} [inst : Semiring R] [inst_1 : AddCommMonoid M₂]   [inst_2 : AddCommMonoi
d M₃] [inst_3 : _root_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem alternatization_apply_toAlternatingMap :
    (alternatization f).toAlternatingMap = MultilinearMap.alternatization f.1 := by
  ext v
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, Function.comp_def]

end ContinuousMultilinearMap

