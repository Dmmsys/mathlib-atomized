/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The fixed submodule of a linear map

- `LinearMap.fixedSubmodule`: the submodule of a linear map consisting of its fixed points.

-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)


/-- The fixed submodule of a linear map. -/
/-
**LinearMap.fixedSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：fixedSubmodule (f : V ->ₗ[R] V) : Submodule R V where carrier
参数：f : V ->ₗ[R] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fixed submodule of a linear map.
-/
def fixedSubmodule (f : V →ₗ[R] V) : Submodule R V where
  carrier := { x | f x = x }
  add_mem' {x y} hx hy := by aesop
  zero_mem' := by simp
  smul_mem' r x hx := by aesop

@[simp]
/-
**LinearMap.mem_fixedSubmodule_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_fixedSubmodule_iff {f : V ->ₗ[R] V} {v : V} : v in f.fixedSubmodule ↔ 
f v = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fixedSubmodule_iff {f : V →ₗ[R] V} {v : V} :
    v ∈ f.fixedSubmodule ↔ f v = v := by
  simp [fixedSubmodule]
/-
**LinearMap.fixedSubmodule_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fixedSubmodule_eq_ker {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [M
odule R V] (f : V ->ₗ[R] V) : f.fixedSubmodule = LinearMap.ker (f - id (R
参数：f : V ->ₗ[R] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixedSubmodule_eq_ker {R : Type*} [Ring R]
    {V : Type*} [AddCommGroup V] [Module R V] (f : V →ₗ[R] V) :
    f.fixedSubmodule = LinearMap.ker (f - id (R := R)) := by
  ext; simp [sub_eq_zero]
/-
**LinearMap.fixedSubmodule_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fixedSubmodule_eq_top_iff {f : V ->ₗ[R] V} : f.fixedSubmodule = ⊤ ↔ f = id
 (R
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
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixedSubmodule_eq_top_iff {f : V →ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = id (R := R) := by
  simp [LinearMap.ext_iff, Submodule.ext_iff]
/-
**LinearMap.fixedSubmodule_inf_fixedSubmodule_le_comp** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap`。
形式化陈述：fixedSubmodule_inf_fixedSubmodule_le_comp (f g : V ->ₗ[R] V) : f.fixedSubm
odule ⊓ g.fixedSubmodule <= (f ∘ₗ g).fixedSubmodule
参数：f g : V ->ₗ[R] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fixedSubmodule_inf_fixedSubmodule_le_comp (f g : V →ₗ[R] V) :
    f.fixedSubmodule ⊓ g.fixedSubmodule ≤ (f ∘ₗ g).fixedSubmodule := by
  intro; simp_all
/-
**LinearMap.fixedSubmodule_comp_inf_fixedSubmodule_le** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap`。
形式化陈述：fixedSubmodule_comp_inf_fixedSubmodule_le (f g : V ->ₗ[R] V) : (f ∘ₗ g).fi
xedSubmodule ⊓ g.fixedSubmodule <= f.fixedSubmodule
参数：f g : V ->ₗ[R] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fixedSubmodule_comp_inf_fixedSubmodule_le (f g : V →ₗ[R] V) :
    (f ∘ₗ g).fixedSubmodule ⊓ g.fixedSubmodule ≤ f.fixedSubmodule := by intro; aesop

end LinearMap

namespace LinearEquiv

open scoped Pointwise
open LinearMap Submodule MulAction

variable {R : Type*} [Semiring R]
  {U V : Type*} [AddCommMonoid U] [AddCommMonoid V]
  [Module R U] [Module R V] (e : V ≃ₗ[R] V)

variable {P : Submodule R U} {Q : Submodule R V}

/-
**LinearEquiv.fixedSubmodule_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fixedSubmodule_eq_top_iff {f : V ≃ₗ[R] V} : f.fixedSubmodule = ⊤ ↔ f = .re
fl R V
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
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixedSubmodule_eq_top_iff {f : V ≃ₗ[R] V} :
    f.fixedSubmodule = ⊤ ↔ f = .refl R V := by
  simp [LinearEquiv.ext_iff, Submodule.ext_iff]
/-
**LinearEquiv.mem_stabilizer_submodule_of_le_fixedSubmodule** 是 Mathlib 中的一个定理，位
于命名空间 `LinearEquiv`。
形式化陈述：mem_stabilizer_submodule_of_le_fixedSubmodule {e : V ≃ₗ[R] V} {W : Submodu
le R V} (hW : W <= LinearMap.fixedSubmodule e) : e in stabilizer (V ≃ₗ[R] V) W
参数：hW : W <= LinearMap.fixedSubmodule e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_stabilizer_submodule_iff_map_eq`：mem_stabilizer_submodule_
iff_map_eq {e : G} : e in stabilizer G S ↔ S.map (DistribSMul.toLinearMap R M e)
 = S
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `LinearMap.mem_fixedSubmodule_iff`：mem_fixedSubmodule_iff {f : V ->ₗ[R] V
} {v : V} : v in f.fixedSubmodule ↔ f v = v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem mem_stabilizer_submodule_of_le_fixedSubmodule
    {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W ≤ LinearMap.fixedSubmodule e) :
    e ∈ stabilizer (V ≃ₗ[R] V) W := by
  rw [mem_stabilizer_submodule_iff_map_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx : x ∈ W, rfl⟩
    suffices e x = x by simpa [this, coe_coe]
    rw [← coe_toLinearMap, ← mem_fixedSubmodule_iff]
    exact hW hx
  · intro x hx
    refine ⟨x, hx, ?_⟩
    simp only [DistribSMul.toLinearMap_apply, LinearEquiv.smul_def]
    rw [← coe_toLinearMap, ← mem_fixedSubmodule_iff]
    exact hW hx
/-
**LinearEquiv.mem_stabilizer_fixedSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqu
iv`。
形式化陈述：mem_stabilizer_fixedSubmodule (e : V ≃ₗ[R] V) : e in stabilizer _ e.fixedS
ubmodule
参数：e : V ≃ₗ[R] V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.mem_stabilizer_submodule_of_le_fixedSubmodule`：mem_stabilize
r_submodule_of_le_fixedSubmodule {e : V ≃ₗ[R] V} {W : Submodule R V} (hW : W <= 
LinearMap.fixedSubmodule e) : e in stabilizer (…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mem_stabilizer_fixedSubmodule (e : V ≃ₗ[R] V) :
    e ∈ stabilizer _ e.fixedSubmodule :=
  mem_stabilizer_submodule_of_le_fixedSubmodule (le_refl _)
/-
**LinearEquiv.map_eq_of_mem_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
形式化陈述：map_eq_of_mem_fixingSubgroup (W : Submodule R V) (he : e in fixingSubgroup
 _ W.carrier) : map e.toLinearMap W = W
参数：W : Submodule R V；he : e in fixingSubgroup _ W.carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem map_eq_of_mem_fixingSubgroup (W : Submodule R V)
    (he : e ∈ fixingSubgroup _ W.carrier) :
    map e.toLinearMap W = W := by
  ext v
  simp only [mem_fixingSubgroup_iff, carrier_eq_coe, SetLike.mem_coe, LinearEquiv.smul_def] at he
  refine ⟨fun ⟨w, hv, hv'⟩ ↦ ?_, fun hv ↦ ?_⟩
  · simp only [SetLike.mem_coe, coe_coe] at hv hv'
    rwa [← hv', he w hv]
  · refine ⟨v, hv, he v hv⟩

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

set_option backward.isDefEq.respectTransparency false in
/-- When `u : V ≃ₗ[R] V` maps a submodule `W` into itself,
this is the induced linear equivalence of `V ⧸ W`, as a group homomorphism. -/
/-
**LinearEquiv.reduce** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：reduce (W : Submodule R V) : stabilizer (V ≃ₗ[R] V) W ->* (V ⧸ W) ≃ₗ[R] (V
 ⧸ W) where toFun u
参数：W : Submodule R V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `u : V ≃ₗ[R] V` maps a submodule `W` into itself,
this is the induced linear equivalence of `V ⧸ W`, as a group homomorphism.
-/
def reduce (W : Submodule R V) : stabilizer (V ≃ₗ[R] V) W →* (V ⧸ W) ≃ₗ[R] (V ⧸ W) where
  toFun u := Quotient.equiv W W u.val u.prop
  map_mul' u v := by
    ext x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    simp
  map_one' := by aesop

@[simp]
/-
**LinearEquiv.reduce_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：reduce_mk (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) : red
uce W u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u.val x)
参数：W : Submodule R V；u : stabilizer (V ≃ₗ[R] V) W；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduce_mk (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u.val x) :=
  rfl
/-
**LinearEquiv.reduce_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：reduce_mkQ (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) : re
duce W u (W.mkQ x) = W.mkQ (u.val x)
参数：W : Submodule R V；u : stabilizer (V ≃ₗ[R] V) W；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reduce_mkQ (W : Submodule R V) (u : stabilizer (V ≃ₗ[R] V) W) (x : V) :
    reduce W u (W.mkQ x) = W.mkQ (u.val x) :=
  rfl

/-- The linear equivalence deduced from `e : V ≃ₗ[R] V`
by passing to the quotient by `e.fixedSubmodule`. -/
/-
**LinearEquiv.fixedReduce** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：fixedReduce (e : V ≃ₗ[R] V) : (V ⧸ e.fixedSubmodule) ≃ₗ[R] V ⧸ e.fixedSubm
odule
参数：e : V ≃ₗ[R] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence deduced from `e : V ≃ₗ[R] V`
by passing to the quotient by `e.fixedSubmodule`.
-/
def fixedReduce (e : V ≃ₗ[R] V) :
    (V ⧸ e.fixedSubmodule) ≃ₗ[R] V ⧸ e.fixedSubmodule :=
  reduce e.fixedSubmodule ⟨e, e.mem_stabilizer_fixedSubmodule⟩

@[simp]
/-
**LinearEquiv.fixedReduce_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fixedReduce_mk (e : V ≃ₗ[R] V) (x : V) : fixedReduce e (Submodule.Quotient
.mk x) = Submodule.Quotient.mk (e x)
参数：e : V ≃ₗ[R] V；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixedReduce_mk (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) :=
  rfl

@[simp]
/-
**LinearEquiv.fixedReduce_mkQ** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fixedReduce_mkQ (e : V ≃ₗ[R] V) (x : V) : fixedReduce e (e.fixedSubmodule.
mkQ x) = e.fixedSubmodule.mkQ (e x)
参数：e : V ≃ₗ[R] V；x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixedReduce_mkQ (e : V ≃ₗ[R] V) (x : V) :
    fixedReduce e (e.fixedSubmodule.mkQ x) = e.fixedSubmodule.mkQ (e x) :=
  rfl
/-
**LinearEquiv.fixedReduce_eq_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fixedReduce_eq_smul_iff (e : V ≃ₗ[R] V) (a : R) : (forall x, e.fixedReduce
 x = a • x) ↔ forall v, e v - a • v in e.fixedSubmodule
参数：e : V ≃ₗ[R] V；a : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
theorem fixedReduce_eq_smul_iff (e : V ≃ₗ[R] V) (a : R) :
    (∀ x, e.fixedReduce x = a • x) ↔
      ∀ v, e v - a • v ∈ e.fixedSubmodule := by
  simp only [← e.fixedSubmodule.ker_mkQ, mem_ker, map_sub, ← fixedReduce_mkQ, sub_eq_zero]
  constructor
  · intro H x; simp [H]
  · intro H x
    have ⟨y, hy⟩ := e.fixedSubmodule.mkQ_surjective x
    rw [← hy]
    apply H
/-
**LinearEquiv.fixedReduce_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fixedReduce_eq_one (e : V ≃ₗ[R] V) : e.fixedReduce = LinearEquiv.refl R _ 
↔ forall v, e v - v in e.fixedSubmodule
参数：e : V ≃ₗ[R] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.fixedReduce_eq_smul_iff`：fixedReduce_eq_smul_iff (e : V ≃ₗ[R
] V) (a : R) : (forall x, e.fixedReduce x = a • x) ↔ forall v, e v - a • v in e.
fixedSubmodule
-/
theorem fixedReduce_eq_one (e : V ≃ₗ[R] V) :
    e.fixedReduce = LinearEquiv.refl R _ ↔ ∀ v, e v - v ∈ e.fixedSubmodule := by
  simpa [LinearEquiv.ext_iff] using fixedReduce_eq_smul_iff e 1

end LinearEquiv

end

