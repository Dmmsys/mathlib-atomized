/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit

/-!
# Simply connected spaces

This file defines simply connected spaces.
A topological space is simply connected if its fundamental groupoid is equivalent to `Unit`.

We also define the corresponding predicate for sets.

## Main theorems
  - `simply_connected_iff_unique_homotopic` - A space is simply connected if and only if it is
    nonempty and there is a unique path up to homotopy between any two points

  - `SimplyConnectedSpace.ofContractible` - A contractible space is simply connected
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A simply connected space is one whose fundamental groupoid is equivalent to `Discrete Unit` -/
@[mk_iff]
/-
**SimplyConnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_3) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simply connected space is one whose fundamental groupoid is equivalent to `Dis
crete Unit`
-/
class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)

@[deprecated (since := "2026-01-08")]
alias simply_connected_def := simplyConnectedSpace_iff
/-
**simply_connected_iff_unique_homotopic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simply_connected_iff_unique_homotopic (X : Type*) [TopologicalSpace X] : S
implyConnectedSpace X ↔ Nonempty X ∧ forall x y : X, Nonempty (Unique (Path.Homo
topic.Quotient x y))
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FundamentalGroupoid.nonempty_iff`：nonempty_iff (X : Type*) : Nonempty (F
undamentalGroupoid X) ↔ Nonempty X
-/
theorem simply_connected_iff_unique_homotopic (X : Type*) [TopologicalSpace X] :
    SimplyConnectedSpace X ↔
      Nonempty X ∧ ∀ x y : X, Nonempty (Unique (Path.Homotopic.Quotient x y)) := by
  simp only [simplyConnectedSpace_iff, equiv_punit_iff_unique,
    FundamentalGroupoid.nonempty_iff X, and_congr_right_iff, Nonempty.forall]
  intros
  exact ⟨fun h _ _ => h _ _, fun h _ _ => h _ _⟩
/-
**ContinuousMap.HomotopyEquiv.simplyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.HomotopyEquiv.simplyConnectedSpace [hY : SimplyConnectedSpac
e Y] (e : X ≃ₕ Y) : SimplyConnectedSpace X
参数：e : X ≃ₕ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `SimplyConnectedSpace.equiv_unit`：∀ {X : Type u_3} {inst : TopologicalSpa
ce X} [self : SimplyConnectedSpace X],   Nonempty (FundamentalGroupoid X ≌ Categ
oryTheory.Discrete Un…
-/
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace [hY : SimplyConnectedSpace Y]
    (e : X ≃ₕ Y) : SimplyConnectedSpace X :=
  ⟨hY.1.map (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).trans⟩
/-
**ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff (e : X ≃ₕ Y) : Simply
ConnectedSpace X ↔ SimplyConnectedSpace Y
参数：e : X ≃ₕ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`：ContinuousMap.Homotopy
Equiv.simplyConnectedSpace [hY : SimplyConnectedSpace Y] (e : X ≃ₕ Y) : SimplyCo
nnectedSpace X
-/
theorem ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff (e : X ≃ₕ Y) :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace Y :=
  ⟨fun _ ↦ e.symm.simplyConnectedSpace, fun _ ↦ e.simplyConnectedSpace⟩

namespace SimplyConnectedSpace

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

/-
**SimplyConnectedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `SimplyConnectedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x y : X) : Subsingleton (Path.Homotopic.Quotient x y) :=
  @Unique.instSubsingleton _ (Nonempty.some (by
    rw [simply_connected_iff_unique_homotopic] at *; tauto))
/-
**SimplyConnectedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `SimplyConnectedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Subsingleton (FundamentalGroup X x) :=
  inferInstanceAs <| Subsingleton (Path.Homotopic.Quotient x x)
/-
**SimplyConnectedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `SimplyConnectedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : PathConnectedSpace X :=
  let unique_homotopic := (simply_connected_iff_unique_homotopic X).mp inferInstance
  { nonempty := unique_homotopic.1
    joined := fun x y => ⟨(unique_homotopic.2 x y).some.default.out⟩ }

/-- In a simply connected space, any two paths are homotopic -/
/-
**SimplyConnectedSpace.paths_homotopic** 是 Mathlib 中的一个定理，位于命名空间 `SimplyConnecte
dSpace`。
形式化陈述：paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂
参数：p₁ p₂ : Path x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `SimplyConnectedSpace.instSubsingletonQuotient`：∀ {X : Type u_3} [inst : 
TopologicalSpace X] [SimplyConnectedSpace X] (x y : X),   Subsingleton (Path.Hom
otopic.Quotient x y)

--- 原说明 ---
In a simply connected space, any two paths are homotopic
-/
theorem paths_homotopic {x y : X} (p₁ p₂ : Path x y) : Path.Homotopic p₁ p₂ :=
  Quotient.eq.mp (@Subsingleton.elim (Path.Homotopic.Quotient x y) _ _ _)
/-
**SimplyConnectedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `SimplyConnectedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ofContractible (Y : Type*) [TopologicalSpace Y] [ContractibleSpace Y] :
    SimplyConnectedSpace Y :=
  haveI : SimplyConnectedSpace Unit := ⟨⟨FundamentalGroupoid.punitEquivDiscretePUnit⟩⟩
  (ContractibleSpace.hequiv Y Unit).some.simplyConnectedSpace

end SimplyConnectedSpace

/-- A space is simply connected iff it is path connected, and there is at most one path
  up to homotopy between any two points. -/
/-
**simply_connected_iff_paths_homotopic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simply_connected_iff_paths_homotopic : SimplyConnectedSpace Y ↔ PathConnec
tedSpace Y ∧ forall x y : Y, Subsingleton (Path.Homotopic.Quotient x y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplyConnectedSpace.instPathConnectedSpace`：∀ {X : Type u_3} [inst : To
pologicalSpace X] [SimplyConnectedSpace X], PathConnectedSpace X
· 使用定理 `SimplyConnectedSpace.instSubsingletonQuotient`：∀ {X : Type u_3} [inst : 
TopologicalSpace X] [SimplyConnectedSpace X] (x y : X),   Subsingleton (Path.Hom
otopic.Quotient x y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `simply_connected_iff_unique_homotopic`：simply_connected_iff_unique_homot
opic (X : Type*) [TopologicalSpace X] : SimplyConnectedSpace X ↔ Nonempty X ∧ fo
rall x y : X, Nonempty (Uni…
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X

--- 原说明 ---
A space is simply connected iff it is path connected, and there is at most one p
ath
  up to homotopy between any two points.
-/
theorem simply_connected_iff_paths_homotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ x y : Y, Subsingleton (Path.Homotopic.Quotient x y) :=
  ⟨by intro; constructor <;> infer_instance, fun h => by
    cases h; rw [simply_connected_iff_unique_homotopic]
    exact ⟨inferInstance, fun x y => ⟨uniqueOfSubsingleton ⟦PathConnectedSpace.somePath x y⟧⟩⟩⟩

/-- Another version of `simply_connected_iff_paths_homotopic` -/
/-
**simply_connected_iff_paths_homotopic'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simply_connected_iff_paths_homotopic' : SimplyConnectedSpace Y ↔ PathConne
ctedSpace Y ∧ forall {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `simply_connected_iff_paths_homotopic`：simply_connected_iff_paths_homotop
ic : SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧ forall x y : Y, Subsingleto
n (Path.Homotopic.Quotient…

--- 原说明 ---
Another version of `simply_connected_iff_paths_homotopic`
-/
theorem simply_connected_iff_paths_homotopic' :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ {x y : Y} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ := by
  convert! simply_connected_iff_paths_homotopic (Y := Y)
  simp [Path.Homotopic.Quotient, Setoid.eq_top_iff]; rfl

set_option backward.isDefEq.respectTransparency false in
open Path.Homotopic.Quotient in
/-- A space is simply connected if and only if it is path-connected and every loop
    at any basepoint is null-homotopic (i.e., homotopic to the constant loop). -/
/-
**simply_connected_iff_loops_nullhomotopic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simply_connected_iff_loops_nullhomotopic : SimplyConnectedSpace Y ↔ PathCo
nnectedSpace Y ∧ forall (x : Y) (γ : Path x x), Path.Homotopic γ (Path.refl x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `simply_connected_iff_paths_homotopic'`：simply_connected_iff_paths_homoto
pic' : SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧ forall {x y : Y} (p₁ p₂ :
 Path x y), Path.Homotopic …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Path.Homotopic.Quotient.eq`：eq {p q : Path x₀ x₁} : mk p = mk q ↔ Homoto
pic p q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Path.Homotopic.Quotient.trans_assoc`：trans_assoc {x₀ x₁ x₂ x₃ : X} (γ₀ :
 Homotopic.Quotient x₀ x₁) (γ₁ : Homotopic.Quotient x₁ x₂) (γ₂ : Homotopic.Quoti
ent x₂ x₃) : trans (trans…
· 使用定理 `Path.Homotopic.Quotient.symm_trans`：symm_trans (γ : Homotopic.Quotient x
₀ x₁) : trans (symm γ) γ = refl x₁
· 使用定理 `Path.Homotopic.Quotient.trans_refl`：trans_refl (γ : Homotopic.Quotient x
₀ x₁) : trans γ (refl x₁) = γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A space is simply connected if and only if it is path-connected and every loop
    at any basepoint is null-homotopic (i.e., homotopic to the constant loop).
-/
theorem simply_connected_iff_loops_nullhomotopic :
    SimplyConnectedSpace Y ↔
      PathConnectedSpace Y ∧ ∀ (x : Y) (γ : Path x x), Path.Homotopic γ (Path.refl x) := by
  rw [simply_connected_iff_paths_homotopic']
  constructor
  · -- Forward: all paths homotopic implies all loops null-homotopic
    intro ⟨hpc, hall⟩
    exact ⟨hpc, fun x γ => hall γ (Path.refl x)⟩
  · -- Backward: all loops null-homotopic implies all paths homotopic
    intro ⟨hpc, hloops⟩
    refine ⟨hpc, fun {x y} p₁ p₂ => ?_⟩
    -- Work in the quotient where structural steps can be done by simp
    rw [← eq]
    replace hloops : ∀ (x : Y) (γ : Path x x),
        (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      fun x γ => Quotient.sound (hloops x γ)
    have h : trans ⟦p₁⟧ (symm ⟦p₂⟧) = refl x := by
      simpa using hloops x (p₁.trans p₂.symm)
    calc ⟦p₁⟧
      _ = trans (trans ⟦p₁⟧ (symm ⟦p₂⟧)) ⟦p₂⟧ := by simp
      _ = ⟦p₂⟧ := by grind

/-!
### Simply connected sets
-/

/-- We say that a set is simply connected if it's a simply connected topological space
in the induced topology. -/
/-
**IsSimplyConnected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSimplyConnected (s : Set X) : Prop
参数：s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set is simply connected if it's a simply connected topological spa
ce
in the induced topology.
-/
def IsSimplyConnected (s : Set X) : Prop := SimplyConnectedSpace s
/-
**IsSimplyConnected.simplyConnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimplyConnected.simplyConnectedSpace {s : Set X} (hs : IsSimplyConnected
 s) : SimplyConnectedSpace s
参数：hs : IsSimplyConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSimplyConnected.simplyConnectedSpace {s : Set X} (hs : IsSimplyConnected s) :
    SimplyConnectedSpace s := hs
/-
**IsSimplyConnected.isPathConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimplyConnected.isPathConnected {s : Set X} (hs : IsSimplyConnected s) :
 IsPathConnected s
参数：hs : IsSimplyConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimplyConnected.simplyConnectedSpace`：IsSimplyConnected.simplyConnecte
dSpace {s : Set X} (hs : IsSimplyConnected s) : SimplyConnectedSpace s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `SimplyConnectedSpace.instPathConnectedSpace`：∀ {X : Type u_3} [inst : To
pologicalSpace X] [SimplyConnectedSpace X], PathConnectedSpace X
-/
theorem IsSimplyConnected.isPathConnected {s : Set X} (hs : IsSimplyConnected s) :
    IsPathConnected s :=
  have := hs.simplyConnectedSpace
  isPathConnected_iff_pathConnectedSpace.mpr inferInstance
/-
**IsSimplyConnected.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSimplyConnected.nonempty {s : Set X} (hs : IsSimplyConnected s) : s.None
mpty
参数：hs : IsSimplyConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPathConnected.nonempty`：IsPathConnected.nonempty (h : IsPathConnected 
F) : F.Nonempty
· 使用定理 `IsSimplyConnected.isPathConnected`：IsSimplyConnected.isPathConnected {s 
: Set X} (hs : IsSimplyConnected s) : IsPathConnected s
-/
theorem IsSimplyConnected.nonempty {s : Set X} (hs : IsSimplyConnected s) : s.Nonempty :=
  hs.isPathConnected.nonempty
/-
**Topology.IsEmbedding.isSimplyConnected_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.isSimplyConnected_image {f : X -> Y} (hf : Topology.I
sEmbedding f) {s : Set X} : IsSimplyConnected (f '' s) ↔ IsSimplyConnected s
参数：hf : Topology.IsEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff`：ContinuousMap.Homo
topyEquiv.simplyConnectedSpace_iff (e : X ≃ₕ Y) : SimplyConnectedSpace X ↔ Simpl
yConnectedSpace Y
-/
theorem Topology.IsEmbedding.isSimplyConnected_image {f : X → Y} (hf : Topology.IsEmbedding f)
    {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
  hf.homeomorphImage s |>.toHomotopyEquiv |>.simplyConnectedSpace_iff |>.symm

@[simp]
/-
**Homeomorph.isSimplyConnected_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.isSimplyConnected_image (f : X ≃ₜ Y) {s : Set X} : IsSimplyConn
ected (f '' s) ↔ IsSimplyConnected s
参数：f : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.isSimplyConnected_image`：Topology.IsEmbedding.isSim
plyConnected_image {f : X -> Y} (hf : Topology.IsEmbedding f) {s : Set X} : IsSi
mplyConnected (f '' s) ↔ IsSimplyC…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
theorem Homeomorph.isSimplyConnected_image (f : X ≃ₜ Y) {s : Set X} :
    IsSimplyConnected (f '' s) ↔ IsSimplyConnected s :=
  f.isEmbedding.isSimplyConnected_image

@[simp]
/-
**Homeomorph.isSimplyConnected_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.isSimplyConnected_preimage (f : X ≃ₜ Y) {s : Set Y} : IsSimplyC
onnected (f ⁻¹' s) ↔ IsSimplyConnected s
参数：f : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
· 使用定理 `Homeomorph.isSimplyConnected_image`：Homeomorph.isSimplyConnected_image (
f : X ≃ₜ Y) {s : Set X} : IsSimplyConnected (f '' s) ↔ IsSimplyConnected s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Homeomorph.isSimplyConnected_preimage (f : X ≃ₜ Y) {s : Set Y} :
    IsSimplyConnected (f ⁻¹' s) ↔ IsSimplyConnected s := by
  rw [← image_symm, isSimplyConnected_image]

/-- A set is simply connected iff it's path connected
and any loop is homotopic to the constant path within `s`. -/
/-
**isSimplyConnected_iff_exists_homotopy_refl_forall_mem** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：isSimplyConnected_iff_exists_homotopy_refl_forall_mem {s : Set X} : IsSimp
lyConnected s ↔ IsPathConnected s ∧ forall x, forall p : Path x x, (forall t, p 
t in s) -> exists F : p.Homotopy (.refl x), forall t, F t in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSimplyConnected.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (s 
: Set X), IsSimplyConnected s = SimplyConnectedSpace ↑s
· 使用定理 `simply_connected_iff_loops_nullhomotopic`：simply_connected_iff_loops_nul
lhomotopic : SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧ forall (x : Y) (γ :
 Path x x), Path.Homotopic γ (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isPathConnected_iff_pathConnectedSpace`：isPathConnected_iff_pathConnecte
dSpace : IsPathConnected F ↔ PathConnectedSpace F
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousMap.HomotopyLike.toContinuousMapClass`：∀ {X : outParam (Type u
_3)} {Y : outParam (Type u_4)} {inst : TopologicalSpace X} {inst_1 : Topological
Space Y}   {F : Type u_5} {f₀ f₁ : ou…
· 使用定理 `ContinuousMap.HomotopyWith.instHomotopyLike`：∀ {X : Type u} {Y : Type v}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   {
P : C(X, Y) → Prop}, ContinuousMa…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ContinuousMap.HomotopyWith.apply_zero`：apply_zero (F : HomotopyWith f₀ f
₁ P) (x : X) : F (0, x) = f₀ x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Path.map_coe`：map_coe (γ : Path x y) {f : X -> Y} (h : Continuous f) : (
γ.map h : I -> Y) = f ∘ γ
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ContinuousMap.HomotopyWith.apply_one`：apply_one (F : HomotopyWith f₀ f₁ 
P) (x : X) : F (1, x) = f₁ x
· 使用定理 `Path.refl_apply`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (x
_1 : ↑unitInterval), (Path.refl x) x_1 = x
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A set is simply connected iff it's path connected
and any loop is homotopic to the constant path within `s`.
-/
theorem isSimplyConnected_iff_exists_homotopy_refl_forall_mem {s : Set X} :
    IsSimplyConnected s ↔ IsPathConnected s ∧ ∀ x, ∀ p : Path x x, (∀ t, p t ∈ s) →
      ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ s := by
  rw [IsSimplyConnected, simply_connected_iff_loops_nullhomotopic,
    ← isPathConnected_iff_pathConnectedSpace]
  refine .and .rfl ⟨fun h x p hp ↦ ?_, fun h x p ↦ ?_⟩
  · lift x to s using by simpa using hp 0
    rcases h x {
      toFun := fun t ↦ ⟨p t, hp t⟩
      source' := by simp
      target' := by simp
    } with ⟨F⟩
    exact ⟨F.map (.restrict s (.id _)), fun t ↦ (F t).2⟩
  · rcases h x (p.map continuous_subtype_val) (fun t ↦ (p t).2) with ⟨F, hF⟩
    exact ⟨{
      toFun t := ⟨F t, hF t⟩
      map_zero_left := by simp
      map_one_left := by simp
      prop' := by simp
    }⟩

open scoped Pointwise

@[to_additive (attr := simp)]
/-
**isSimplyConnected_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimplyConnected_smul_set_iff {G : Type*} [Group G] [MulAction G X] [Cont
inuousConstSMul G X] {c : G} {s : Set X} : IsSimplyConnected (c • s) ↔ IsSimplyC
onnected s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isSimplyConnected_image`：Homeomorph.isSimplyConnected_image (
f : X ≃ₜ Y) {s : Set X} : IsSimplyConnected (f '' s) ↔ IsSimplyConnected s
-/
theorem isSimplyConnected_smul_set_iff {G : Type*} [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {c : G} {s : Set X} :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
  Homeomorph.smul c |>.isSimplyConnected_image

@[simp]
/-
**isSimplyConnected_smul_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSimplyConnected_smul_set₀_iff {G : Type*} [GroupWithZero G] [MulAction G X]
    [ContinuousConstSMul G X] {c : G} {s : Set X} (hc : c ≠ 0) :
    IsSimplyConnected (c • s) ↔ IsSimplyConnected s :=
  isSimplyConnected_smul_set_iff (c := Units.mk0 c hc)
