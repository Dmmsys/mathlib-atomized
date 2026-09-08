/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# `map` and `comap` for `Submodule`s

## Main declarations

* `Submodule.map`: The pushforward of a submodule `p ⊆ M` by `f : M → M₂`
* `Submodule.comap`: The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`
* `Submodule.giMapComap`: `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
* `Submodule.gciMapComap`: `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.

## Tags

submodule, subspace, linear map, pushforward, pullback
-/

@[expose] public section

open Function Pointwise Set

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable {x : M}

section

variable [RingHomSurjective σ₁₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
/-
**Submodule.map** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of a submodule `p ⊆ M` by `f : M → M₂`
-/
def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]
/-
**Submodule.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f 
'' p
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl
/-
**Submodule.map_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_toAddSubmonoid (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (p.map f).to
AddSubmonoid = p.toAddSubmonoid.map (f : M ->+ M₂)
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem map_toAddSubmonoid (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl
/-
**Submodule.map_toAddSubmonoid'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_toAddSubmonoid' (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (p.map f).t
oAddSubmonoid = p.toAddSubmonoid.map f
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem map_toAddSubmonoid' (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl

@[simp]
/-
**Submodule._root_.AddMonoidHom.coe_toIntLinearMap_map** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_map {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A) :
    (AddSubgroup.toIntSubmodule s).map f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.map f) := rfl

@[simp]
/-
**Submodule._root_.MonoidHom.coe_toAdditive_map** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonoidHom.coe_toAdditive_map {G G₂ : Type*} [Group G] [Group G₂] (f : G →* G₂)
    (s : Subgroup G) :
    s.toAddSubgroup.map (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.map f) := rfl

@[simp]
/-
**Submodule._root_.AddMonoidHom.coe_toMultiplicative_map** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoidHom.coe_toMultiplicative_map {G G₂ : Type*} [AddGroup G] [AddGroup G₂]
    (f : G →+ G₂) (s : AddSubgroup G) :
    s.toSubgroup.map (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.map f) := rfl

@[simp]
/-
**Submodule.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂} : x in map f p ↔
 exists y, y in p ∧ f y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂} :
    x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x :=
  Iff.rfl
/-
**Submodule.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r in p) :
 f r in map f p
参数：h : r in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
  Set.mem_image_of_mem _ h
/-
**Submodule.apply_coe_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：apply_coe_mem_map (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p) : f r i
n map f p
参数：f : M ->ₛₗ[σ₁₂] M₂；r : p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem apply_coe_mem_map (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p) : f r ∈ map f p :=
  mem_map_of_mem r.prop

@[simp]
/-
**Submodule.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_id : map (LinearMap.id : M →ₗ[R] M) p = p :=
  Submodule.ext fun a => by simp
/-
**Submodule.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M ->ₛₗ[σ₁₂] 
M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M ->ₛₗ[σ₁₃] M₃) 
p = map g (map f p)
参数：f : M ->ₛₗ[σ₁₂] M₂；g : M₂ ->ₛₗ[σ₂₃] M₃；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M →ₛₗ[σ₁₂] M₂)
    (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
  SetLike.coe_injective <| by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]

@[gcongr]
/-
**Submodule.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M} : p <= p' -> map f p 
<= map f p'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono {f : M →ₛₗ[σ₁₂] M₂} {p p' : Submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  image_mono

@[simp]
/-
**Submodule.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} (p : Submodule R M) [inst_6 : RingHomSurjective σ₁₂], Submodule.map 0 p
 = ⊥
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : ∃ x : M, x ∈ p := ⟨0, p.zero_mem⟩
  ext <| by simp [this, eq_comm]
/-
**Submodule.map_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_add_le (f g : M ->ₛₗ[σ₁₂] M₂) : map (f + g) p <= map f p ⊔ map g p
参数：f g : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem_sup`：add_mem_sup {S T : Submodule R M} {s t : M} (hs :
 s in S) (ht : t in T) : s + t in S ⊔ T
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
-/
theorem map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p ⊔ map g p := by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)
/-
**Submodule.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inf_le (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} : (p ⊓ q).map f <= p
.map f ⊓ q.map f
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
-/
theorem map_inf_le (f : M →ₛₗ[σ₁₂] M₂) {p q : Submodule R M} :
    (p ⊓ q).map f ≤ p.map f ⊓ q.map f :=
  image_inter_subset f p q
/-
**Submodule.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (hf : Injective f) : (p
 ⊓ q).map f = p.map f ⊓ q.map f
参数：f : M ->ₛₗ[σ₁₂] M₂；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (f : M →ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (hf : Injective f) :
    (p ⊓ q).map f = p.map f ⊓ q.map f :=
  SetLike.coe_injective <| Set.image_inter hf
/-
**Submodule.map_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (f : M ->ₛₗ[σ₁₂
] M₂) (hf : Injective f) : (⨅ i, p i).map f = ⨅ i, (p i).map f
参数：f : M ->ₛₗ[σ₁₂] M₂；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
lemma map_iInf {ι : Sort*} [Nonempty ι] {p : ι → Submodule R M} (f : M →ₛₗ[σ₁₂] M₂)
    (hf : Injective f) : (⨅ i, p i).map f = ⨅ i, (p i).map f :=
  SetLike.coe_injective <| by simpa only [map_coe, coe_iInf] using hf.injOn.image_iInter_eq
/-
**Submodule.range_map_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_map_nonempty (N : Submodule R M) : (Set.range (fun ϕ => Submodule.ma
p ϕ N : (M ->ₛₗ[σ₁₂] M₂) -> Submodule R₂ M₂)).Nonempty
参数：N : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
-/
theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

end

section SemilinearMap

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `LinearEquiv.submoduleMap` for a
computable version when `f` has an explicit inverse. -/
/-
**Submodule.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：equivMapOfInjective (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule 
R M) : p ≃ₛₗ[σ₁₂] p.map f
参数：f : M ->ₛₗ[σ₁₂] M₂；i : Injective f；p : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `LinearEquiv.submoduleMa
p` for a
computable version when `f` has an explicit inverse.
-/
noncomputable def equivMapOfInjective (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }

@[simp]
/-
**Submodule.coe_equivMapOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_equivMapOfInjective_apply (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : 
Submodule R M) (x : p) : (equivMapOfInjective f i p x : M₂) = f x
参数：f : M ->ₛₗ[σ₁₂] M₂；i : Injective f；p : Submodule R M；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem coe_equivMapOfInjective_apply (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p) : (equivMapOfInjective f i p x : M₂) = f x :=
  rfl

@[simp]
/-
**Submodule.map_equivMapOfInjective_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：map_equivMapOfInjective_symm_apply (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) 
(p : Submodule R M) (x : p.map f) : f ((equivMapOfInjective f i p).symm x) = x
参数：f : M ->ₛₗ[σ₁₂] M₂；i : Injective f；p : Submodule R M；x : p.map f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Submodule.coe_equivMapOfInjective_apply`：coe_equivMapOfInjective_apply (
f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) (x : p) : (equivMapOfI
njective f i p x : M₂) = f x
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem map_equivMapOfInjective_symm_apply (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p.map f) : f ((equivMapOfInjective f i p).symm x) = x := by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x, coe_equivMapOfInjective_apply,
    i.eq_iff, LinearEquiv.apply_symm_apply]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
@[implicit_reducible]
/-
**Submodule.comap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：comap (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R₂ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`
-/
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]
/-
**Submodule.comap_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M)
 = f ⁻¹' p
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl

@[simp]
/-
**Submodule.AddMonoidHom.coe_toIntLinearMap_comap** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.AddMonoidHom`。
形式化陈述：∀ {A : Type u_9} {A₂ : Type u_10} [inst : AddCommGroup A] [inst_1 : AddCom
mGroup A₂] (f : A →+ A₂) (s : AddSubgroup A₂),   Submodule.comap f.toIntLinearMa
p (AddSubgroup.toIntSubmodule s) = AddSubgroup.toIntSubmodule (AddSubgroup.comap
 f s)
参数：f : A →+ A₂；s : AddSubgroup A₂；AddSubgroup.toIntSubmodule s；AddSubgroup.comap
 f s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddMonoidHom.coe_toIntLinearMap_comap {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    (AddSubgroup.toIntSubmodule s).comap f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.comap f) := rfl

@[simp]
/-
**Submodule.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂} : x in comap f p ↔ f 
x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂} : x ∈ comap f p ↔ f x ∈ p :=
  Iff.rfl

@[simp]
/-
**Submodule.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_id : comap (LinearMap.id : M ->ₗ[R] M) p = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem comap_id : comap (LinearMap.id : M →ₗ[R] M) p = p :=
  SetLike.coe_injective rfl
/-
**Submodule.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃
) : comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap g p)
参数：f : M ->ₛₗ[σ₁₂] M₂；g : M₂ ->ₛₗ[σ₂₃] M₃；p : Submodule R₃ M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl

@[gcongr]
/-
**Submodule.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂} : q <= q' -> coma
p f q <= comap f q'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono {f : M →ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  preimage_mono
/-
**Submodule.le_comap_pow_of_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_comap_pow_of_le_comap (p : Submodule R M) {f : M ->ₗ[R] M} (h : p <= p.
comap f) (k : Nat) : p <= p.comap (f ^ k)
参数：p : Submodule R M；h : p <= p.comap f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Submodule.comap_id`：comap_id : comap (LinearMap.id : M ->ₗ[R] M) p = p
· 使用定理 `Module.End.iterate_succ`：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (
f' ^ n) f'
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
-/
theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M}
    (h : p ≤ p.comap f) (k : ℕ) : p ≤ p.comap (f ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, comap_comp, h.trans (comap_mono ih)]

section

variable [RingHomSurjective σ₁₂]

/-
**Submodule.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodul
e R₂ M₂} : map f p <= q ↔ p <= comap f q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p ≤ q ↔ p ≤ comap f q :=
  image_subset_iff
/-
**Submodule.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} [inst_6 : RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂),   GaloisConnectio
n (Submodule.map f) (Submodule.comap f)
参数：f : M →ₛₗ[σ₁₂] M₂；Submodule.map f；Submodule.comap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
-/
theorem gc_map_comap (f : M →ₛₗ[σ₁₂] M₂) : GaloisConnection (map f) (comap f)
  | _, _ => map_le_iff_le_comap

@[simp]
/-
**Submodule.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
-/
theorem map_bot (f : M →ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/-
**Submodule.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f p ⊔ map f p'
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
-/
theorem map_sup (f : M →ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[simp]
/-
**Submodule.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> Submodule R M) : map f
 (⨆ i, p i) = ⨆ i, map f (p i)
参数：f : M ->ₛₗ[σ₁₂] M₂；p : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
-/
theorem map_iSup {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → Submodule R M) :
    map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
/-
**Submodule.disjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：disjoint_map {f : M ->ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) {p q : Submo
dule R M} (hpq : Disjoint p q) : Disjoint (p.map f) (q.map f)
参数：hf : Function.Injective f；hpq : Disjoint p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_inf`：map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (h
f : Injective f) : (p ⊓ q).map f = p.map f ⊓ q.map f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
-/
lemma disjoint_map {f : M →ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) {p q : Submodule R M}
    (hpq : Disjoint p q) : Disjoint (p.map f) (q.map f) := by
  rw [disjoint_iff, ← map_inf f hf, disjoint_iff.mp hpq, map_bot]

end

@[simp]
/-
**Submodule.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_top (f : M →ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤ :=
  rfl

@[simp]
/-
**Submodule.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_inf (f : M ->ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q'
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_inf (f : M →ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl

@[simp]
/-
**Submodule.comap_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> Submodule R₂ M₂) : c
omap f (⨅ i, p i) = ⨅ i, comap f (p i)
参数：f : M ->ₛₗ[σ₁₂] M₂；p : ι -> Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
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
theorem comap_iInf {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂)
    (p : ι → Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i) := by
  ext
  simp

@[simp]
/-
**Submodule.comap_finsetInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_finsetInf {ι : Type*} (f : M ->ₛₗ[σ₁₂] M₂) (s : Finset ι) (p : ι -> 
Submodule R₂ M₂) : comap f (s.inf p) = s.inf fun i => comap f (p i)
参数：f : M ->ₛₗ[σ₁₂] M₂；s : Finset ι；p : ι -> Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_finsetInf {ι : Type*} (f : M →ₛₗ[σ₁₂] M₂)
    (s : Finset ι) (p : ι → Submodule R₂ M₂) : comap f (s.inf p) = s.inf fun i ↦ comap f (p i) := by
  simp [Finset.inf_eq_iInf]

@[simp]
/-
**Submodule.comap_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_zero : comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
  ext <| by simp
/-
**Submodule.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_comap_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R
₂ M₂) : map f (comap f q) <= q
参数：f : M ->ₛₗ[σ₁₂] M₂；q : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
-/
theorem map_comap_le [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) :
    map f (comap f q) ≤ q :=
  (gc_map_comap f).l_u_le _
/-
**Submodule.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_comap_map [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R
 M) : p <= comap f (map f p)
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
-/
theorem le_comap_map [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p ≤ comap f (map f p) :=
  (gc_map_comap f).le_u_l _

section submoduleOf

/-- For any `R` submodules `p` and `q`, `p ⊓ q` as a submodule of `q`. -/
/-
**Submodule.submoduleOf** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：submoduleOf (p q : Submodule R M) : Submodule R q
参数：p q : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R` submodules `p` and `q`, `p ⊓ q` as a submodule of `q`.
-/
def submoduleOf (p q : Submodule R M) : Submodule R q :=
  Submodule.comap q.subtype p

/-- If `p ≤ q`, then `p` as a subgroup of `q` is isomorphic to `p`. -/
/-
**Submodule.submoduleOfEquivOfLe** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：submoduleOfEquivOfLe {p q : Submodule R M} (h : p <= q) : p.submoduleOf q 
≃ₗ[R] p where toFun m
参数：h : p <= q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p ≤ q`, then `p` as a subgroup of `q` is isomorphic to `p`.
-/
def submoduleOfEquivOfLe {p q : Submodule R M} (h : p ≤ q) : p.submoduleOf q ≃ₗ[R] p where
  toFun m := ⟨m.1, m.2⟩
  invFun m := ⟨⟨m.1, h m.2⟩, m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end submoduleOf

section GaloisInsertion

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
/-
**Submodule.giMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：giMapComap (hf : Surjective f) : GaloisInsertion (map f) (comap f)
参数：hf : Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…

--- 原说明 ---
`map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
-/
def giMapComap (hf : Surjective f) : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩

variable (hf : Surjective f)
include hf
/-
**Submodule.map_comap_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p
参数：p : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _
/-
**Submodule.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_surjective_of_surjective : Function.Surjective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_surjective`：l_surjective [Preorder α] [PartialOrder β]
 (gi : GaloisInsertion l u) : Surjective l
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
/-
**Submodule.comap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_injective_of_surjective : Function.Injective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_injective`：u_injective [Preorder α] [PartialOrder β] (
gi : GaloisInsertion l u) : Injective u
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
/-
**Submodule.map_sup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_sup_comap_of_surjective (p q : Submodule R₂ M₂) : (p.comap f ⊔ q.comap
 f).map f = p ⊔ q
参数：p q : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
  (giMapComap hf).l_sup_u _ _
/-
**Submodule.map_iSup_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_iSup_comap_of_surjective {ι : Sort*} (S : ι -> Submodule R₂ M₂) : (⨆ i
, (S i).comap f).map f = iSup S
参数：S : ι -> Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem map_iSup_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _
/-
**Submodule.map_inf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inf_comap_of_surjective (p q : Submodule R₂ M₂) : (p.comap f ⊓ q.comap
 f).map f = p ⊓ q
参数：p q : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_inf_u`：l_inf_u [SemilatticeInf α] [SemilatticeInf β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊓ u b) = a ⊓ b
-/
theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
  (giMapComap hf).l_inf_u _ _
/-
**Submodule.map_iInf_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_iInf_comap_of_surjective {ι : Sort*} (S : ι -> Submodule R₂ M₂) : (⨅ i
, (S i).comap f).map f = iInf S
参数：S : ι -> Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iInf_u`：l_iInf_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨅ i, u (f i)) = ⨅ i
, f i
-/
theorem map_iInf_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _
/-
**Submodule.comap_le_comap_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：comap_le_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f <= q.
comap f ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.u_le_u_iff`：u_le_u_iff [Preorder α] [Preorder β] (gi : G
aloisInsertion l u) {a b} : u a <= u b ↔ a <= b
-/
theorem comap_le_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f ≤ q.comap f ↔ p ≤ q :=
  (giMapComap hf).u_le_u_iff
/-
**Submodule.comap_lt_comap_iff_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodul
e`。
形式化陈述：comap_lt_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f < q.c
omap f ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Submodule.comap_le_comap_iff_of_surjective`：comap_le_comap_iff_of_surjec
tive {p q : Submodule R₂ M₂} : p.comap f <= q.comap f ↔ p <= q
-/
lemma comap_lt_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f < q.comap f ↔ p < q := by
  apply lt_iff_lt_of_le_iff_le' <;> exact comap_le_comap_iff_of_surjective hf
/-
**Submodule.comap_strictMono_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：comap_strictMono_of_surjective : StrictMono (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.strictMono_u`：strictMono_u [Preorder α] [Preorder β] (gi
 : GaloisInsertion l u) : StrictMono u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

variable {p q}
/-
**Submodule.le_map_of_comap_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：le_map_of_comap_le_of_surjective (h : q.comap f <= p) : q <= p.map f
参数：h : q.comap f <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Submodule.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (p : Su
bmodule R₂ M₂) : (p.comap f).map f = p
-/
theorem le_map_of_comap_le_of_surjective (h : q.comap f ≤ p) : q ≤ p.map f :=
  map_comap_eq_of_surjective hf q ▸ map_mono h
/-
**Submodule.lt_map_of_comap_lt_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：lt_map_of_comap_lt_of_surjective (h : q.comap f < p) : q < p.map f
参数：h : q.comap f < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `Submodule.le_map_of_comap_le_of_surjective`：le_map_of_comap_le_of_surjec
tive (h : q.comap f <= p) : q <= p.map f
-/
theorem lt_map_of_comap_lt_of_surjective (h : q.comap f < p) : q < p.map f := by
  rw [lt_iff_le_not_ge] at h ⊢; rw [map_le_iff_le_comap]
  exact h.imp_left (le_map_of_comap_le_of_surjective hf)

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
/-
**Submodule.gciMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：gciMapComap (hf : Injective f) : GaloisCoinsertion (map f) (comap f)
参数：hf : Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…

--- 原说明 ---
`map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.
-/
def gciMapComap (hf : Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp only [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]

variable (hf : Injective f)
include hf
/-
**Submodule.comap_map_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
-/
theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _
/-
**Submodule.comap_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_surjective_of_injective : Function.Surjective (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_surjective`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsert
ion l u), Function.S…
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
/-
**Submodule.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_injective_of_injective : Function.Injective (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
/-
**Submodule.comap_inf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).com
ap f = p ⊓ q
参数：p q : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_inf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
  (gciMapComap hf).u_inf_l _ _
/-
**Submodule.comap_iInf_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_iInf_map_of_injective {ι : Sort*} (S : ι -> Submodule R M) : (⨅ i, (
S i).map f).comap f = iInf S
参数：S : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iInf_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iInf_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _
/-
**Submodule.comap_sup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).com
ap f = p ⊔ q
参数：p q : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_sup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l : 
β → α} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   (gi : GaloisCoins
ertion l u) (a …
-/
theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
  (gciMapComap hf).u_sup_l _ _
/-
**Submodule.comap_iSup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_iSup_map_of_injective {ι : Sort*} (S : ι -> Submodule R M) : (⨆ i, (
S i).map f).comap f = iSup S
参数：S : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_iSup_l`：∀ {α : Type u} {β : Type v} {u : α → β} {l :
 β → α} [inst : CompleteLattice α] [inst_1 : CompleteLattice β]   (gi : GaloisCo
insertion l u) {…
-/
theorem comap_iSup_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _
/-
**Submodule.map_le_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_le_map_iff_of_injective (p q : Submodule R M) : p.map f <= q.map f ↔ p
 <= q
参数：p q : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
-/
theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
  (gciMapComap hf).l_le_l_iff
/-
**Submodule.map_strictMono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_strictMono_of_injective : StrictMono (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.strictMono_l`：∀ {α : Type u} {β : Type v} {u : α → β} 
{l : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion 
l u), StrictMono l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
/-
**Submodule.map_lt_map_iff_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_lt_map_iff_of_injective {p q : Submodule R M} : p.map f < q.map f ↔ p 
< q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_lt_map_iff_of_injective {p q : Submodule R M} :
    p.map f < q.map f ↔ p < q := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, map_le_map_iff_of_injective hf,
    (map_injective_of_injective hf).ne_iff]
/-
**Submodule.comap_lt_of_lt_map_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：comap_lt_of_lt_map_of_injective {p : Submodule R M} {q : Submodule R₂ M₂} 
(h : q < p.map f) : q.comap f < p
参数：h : q < p.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.map_lt_map_iff_of_injective`：map_lt_map_iff_of_injective {p q 
: Submodule R M} : p.map f < q.map f ↔ p < q
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Submodule.map_comap_le`：map_comap_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) (q : Submodule R₂ M₂) : map f (comap f q) <= q
-/
lemma comap_lt_of_lt_map_of_injective {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : q < p.map f) : q.comap f < p := by
  rw [← map_lt_map_iff_of_injective hf]
  exact (map_comap_le _ _).trans_lt h
/-
**Submodule.map_covBy_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_covBy_of_injective {p q : Submodule R M} (h : p ⋖ q) : p.map f ⋖ q.map
 f
参数：h : p ⋖ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.map_lt_map_iff_of_injective`：map_lt_map_iff_of_injective {p q 
: Submodule R M} : p.map f < q.map f ↔ p < q
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用引理 `Submodule.comap_lt_of_lt_map_of_injective`：comap_lt_of_lt_map_of_injecti
ve {p : Submodule R M} {q : Submodule R₂ M₂} (h : q < p.map f) : q.comap f < p
-/
lemma map_covBy_of_injective {p q : Submodule R M} (h : p ⋖ q) :
    p.map f ⋖ q.map f := by
  refine ⟨lt_of_le_of_ne (map_mono h.1.le) ((map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

end GaloisCoinsertion

end SemilinearMap

section OrderIso

variable [RingHomSurjective σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps symm_apply apply]
/-
**Submodule.orderIsoMapComapOfBijective** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orderIsoMapComapOfBijective (f : M ->ₛₗ[σ₁₂] M₂) (hf : Bijective f) : Subm
odule R M ≃o Submodule R₂ M₂ where toFun
参数：f : M ->ₛₗ[σ₁₂] M₂；hf : Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isomorphism induces an order isomorphism of submodules.
-/
def orderIsoMapComapOfBijective (f : M →ₛₗ[σ₁₂] M₂) (hf : Bijective f) :
    Submodule R M ≃o Submodule R₂ M₂ where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps! apply]
/-
**Submodule.orderIsoMapComap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orderIsoMapComap (f : M ≃ₛₗ[σ₁₂] M₂) : Submodule R M ≃o Submodule R₂ M₂
参数：f : M ≃ₛₗ[σ₁₂] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
A linear isomorphism induces an order isomorphism of submodules.
-/
def orderIsoMapComap (f : M ≃ₛₗ[σ₁₂] M₂) :
    Submodule R M ≃o Submodule R₂ M₂ := orderIsoMapComapOfBijective (f : M →ₛₗ[σ₁₂] M₂) f.bijective

@[simp]
/-
**Submodule.orderIsoMapComap_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：orderIsoMapComap_symm_apply (f : M ≃ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (o
rderIsoMapComap f).symm p = comap (f : M ->ₛₗ[σ₁₂] M₂) p
参数：f : M ≃ₛₗ[σ₁₂] M₂；p : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderIsoMapComap_symm_apply (f : M ≃ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap f).symm p = comap (f : M →ₛₗ[σ₁₂] M₂) p :=
  rfl

variable {e : M ≃ₛₗ[σ₁₂] M₂}
variable {p}
/-
**Submodule.map_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} {p : Submodule R M} [inst_6 : RingHomSurjective σ₁₂] {σ₂₁ : R₂ →+* R}  
 [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] {e : M ≃ₛₗ[
σ₁₂] M₂},   Submodule.map (↑e) p = ⊥ ↔ p = ⊥
参数：↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_bot_iff`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : E
quivLike F α β] [inst_1 : LE α] [inst_2 : OrderBot α]   [inst_3 : PartialOrder β
] [i…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
@[simp] protected lemma map_eq_bot_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) = ⊥ ↔ p = ⊥ :=
  map_eq_bot_iff (orderIsoMapComap e)
/-
**Submodule.map_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} {p : Submodule R M} [inst_6 : RingHomSurjective σ₁₂] {σ₂₁ : R₂ →+* R}  
 [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] {e : M ≃ₛₗ[
σ₁₂] M₂},   Submodule.map (↑e) p = ⊤ ↔ p = ⊤
参数：↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_top_iff`：map_eq_top_iff [LE α] [OrderTop α] [PartialOrder β] [Ord
erTop β] [OrderIsoClass F α β] (f : F) {a : α} : f a = ⊤ ↔ a = ⊤
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
@[simp] protected lemma map_eq_top_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) = ⊤ ↔ p = ⊤ :=
  map_eq_top_iff (orderIsoMapComap e)
/-
**Submodule.map_ne_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} {p : Submodule R M} [inst_6 : RingHomSurjective σ₁₂] {σ₂₁ : R₂ →+* R}  
 [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] {e : M ≃ₛₗ[
σ₁₂] M₂},   Submodule.map (↑e) p ≠ ⊥ ↔ p ≠ ⊥
参数：↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma map_ne_bot_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) ≠ ⊥ ↔ p ≠ ⊥ := by simp
/-
**Submodule.map_ne_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} {p : Submodule R M} [inst_6 : RingHomSurjective σ₁₂] {σ₂₁ : R₂ →+* R}  
 [inst_7 : RingHomInvPair σ₁₂ σ₂₁] [inst_8 : RingHomInvPair σ₂₁ σ₁₂] {e : M ≃ₛₗ[
σ₁₂] M₂},   Submodule.map (↑e) p ≠ ⊤ ↔ p ≠ ⊤
参数：↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma map_ne_top_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) ≠ ⊤ ↔ p ≠ ⊤ := by simp

end OrderIso

--TODO(Mario): is there a way to prove this from order properties?
/-
**Submodule.map_inf_eq_map_inf_comap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p :
 Submodule R M} {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
-/
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') :=
  .symm <| SetLike.coe_injective <| image_inter_preimage _ _ _

@[simp]
/-
**Submodule.map_comap_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
  ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩
/-
**Submodule.eq_zero_of_bot_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] (b : ↥⊥),   b = 0
参数：b : ↥⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
-/
theorem eq_zero_of_bot_submodule : ∀ b : (⊥ : Submodule R M), b = 0
  | ⟨b', hb⟩ => Subtype.ext <| show b' = 0 from (mem_bot R).1 hb

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
/-
**Submodule._root_.LinearMap.iInf_invariant** 是 Mathlib 中的一个定理，位于命名空间 `Submodule
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infimum of a family of invariant submodule of an endomorphism is also an inv
ariant
submodule.
-/
theorem _root_.LinearMap.iInf_invariant {σ : R →+* R} {ι : Sort*}
    (f : M →ₛₗ[σ] M) {p : ι → Submodule R M} (hf : ∀ i, ∀ v ∈ p i, f v ∈ p i) :
    ∀ v ∈ iInf p, f v ∈ iInf p := by
  simp only [mem_iInf]
  exact fun v a i ↦ hf i v (a i)
/-
**Submodule.disjoint_iff_comap_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.s
ubtype q = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff,
    map_comap_subtype, map_bot, disjoint_iff]

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
/-
**Submodule.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₂ : Type u_7} [inst : Ring R] [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) [inst_3 : Add
CommGroup M₂] [inst_4 : _root_.Module R M₂] (f : M →ₗ[R] M₂),   Submodule.map (-
f) p = Submodule.map f p
参数：p : Submodule R M；f : M →ₗ[R] M₂；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected theorem map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

@[simp]
/-
**Submodule.comap_neg** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：comap_neg {f : M ->ₗ[R] M₂} {p : Submodule R M₂} : p.comap (-f) = p.comap 
f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma comap_neg {f : M →ₗ[R] M₂} {p : Submodule R M₂} :
    p.comap (-f) = p.comap f := by
  ext; simp
/-
**Submodule.map_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：map_toAddSubgroup (f : M ->ₗ[R] M₂) (p : Submodule R M) : (p.map f).toAddS
ubgroup = p.toAddSubgroup.map (f : M ->+ M₂)
参数：f : M ->ₗ[R] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_toAddSubgroup (f : M →ₗ[R] M₂) (p : Submodule R M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map (f : M →+ M₂) :=
  rfl

end AddCommGroup

end Submodule

namespace Submodule

variable {K : Type*} {V : Type*} {V₂ : Type*}
variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/-
**Submodule.comap_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_smul (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a != 0) : p
.comap (a • f) = p.comap f
参数：f : V ->ₗ[K] V₂；p : Submodule K V₂；a : K；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_smul (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a ≠ 0) :
    p.comap (a • f) = p.comap f := by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]
/-
**Submodule.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {K : Type u_9} {V : Type u_10} {V₂ : Type u_11} [inst : Semifield K] [in
st_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [inst_3 : AddCommMonoid V
₂] [inst_4 : _root_.Module K V₂] (f : V →ₗ[K] V₂)   (p : Submodule K V) (a : K),
 a ≠ 0 → Submodule.map (a • f) p = Submodule.map f p
参数：f : V →ₗ[K] V₂；p : Submodule K V；a : K；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.comap_smul`：comap_smul (f : V ->ₗ[K] V₂) (p : Submodule K V₂) 
(a : K) (h : a != 0) : p.comap (a • f) = p.comap f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
protected theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) :
    p.map (a • f) = p.map f :=
  le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])
/-
**Submodule.comap_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K) : p.comap (a • 
f) = ⨅ _ : a != 0, p.comap f
参数：f : V ->ₗ[K] V₂；p : Submodule K V₂；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Submodule.comap_zero`：comap_zero : comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.comap_smul`：comap_smul (f : V ->ₗ[K] V₂) (p : Submodule K V₂) 
(a : K) (h : a != 0) : p.comap (a • f) = p.comap f
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
-/
theorem comap_smul' (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) :
    p.comap (a • f) = ⨅ _ : a ≠ 0, p.comap f := by
  by_cases h : a = 0 <;> simp [h, comap_smul]
/-
**Submodule.map_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V) (a : K) : p.map (a • f) = 
⨆ _ : a != 0, map f p
参数：f : V ->ₗ[K] V₂；p : Submodule K V；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Submodule.map_zero`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.map_smul`：∀ {K : Type u_9} {V : Type u_10} {V₂ : Type u_11} [i
nst : Semifield K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [in
st_3 : A…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
-/
theorem map_smul' (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) :
    p.map (a • f) = ⨆ _ : a ≠ 0, map f p := by
  by_cases h : a = 0 <;> simp [h, Submodule.map_smul]

end Submodule

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps apply_coe symm_apply]
/-
**Submodule.comapSubtypeEquivOfLe** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p <= q) : comap q.subty
pe p ≃ₗ[R] p where toFun x
参数：hpq : p <= q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`.
-/
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.subtype p ≃ₗ[R] p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

end Submodule

namespace Submodule

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable (p : Submodule R M) (q : Submodule R₂ M₂)

@[simp high]
/-
**Submodule.mem_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x in p.map (e : M ->ₛₗ[τ₁₂] M
₂) ↔ e.symm x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} :
    x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔ e.symm x ∈ p := by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩
/-
**Submodule.map_equiv_eq_comap_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) : K.map (e
 : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ ->ₛₗ[τ₂₁] M)
参数：e : M ≃ₛₗ[τ₁₂] M₂；K : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_map_equiv`：mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x 
in p.map (e : M ->ₛₗ[τ₁₂] M₂) ↔ e.symm x in p
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]
/-
**Submodule.comap_equiv_eq_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) : K.coma
p (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ ->ₛₗ[τ₂₁] M)
参数：e : M ≃ₛₗ[τ₁₂] M₂；K : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
-/
theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm

variable {p}
/-
**Submodule.map_symm_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} : K.map (e.symm 
: M₂ ->ₛₗ[τ₂₁] M) = p ↔ p.map (e : M ->ₛₗ[τ₁₂] M₂) = K
参数：e : M ≃ₛₗ[τ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} :
    K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) = p ↔ p.map (e : M →ₛₗ[τ₁₂] M₂) = K := by
  rw [map_equiv_eq_comap_symm]
  exact (orderIsoMapComap e).symm_apply_eq.trans eq_comm
/-
**Submodule.orderIsoMapComap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) : orderIso
MapComap e p = comap (e.symm : M₂ ->ₛₗ[τ₂₁] M) p
参数：e : M ≃ₛₗ[τ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
-/
theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    orderIsoMapComap e p = comap (e.symm : M₂ →ₛₗ[τ₂₁] M) p :=
  p.map_equiv_eq_comap_symm _
/-
**Submodule.orderIsoMapComap_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) : (
orderIsoMapComap e).symm p = map (e.symm : M₂ ->ₛₗ[τ₂₁] M) p
参数：e : M ≃ₛₗ[τ₁₂] M₂；p : Submodule R₂ M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
-/
theorem orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap e).symm p = map (e.symm : M₂ →ₛₗ[τ₂₁] M) p :=
  p.comap_equiv_eq_map_symm _
/-
**Submodule.inf_comap_le_comap_add** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inf_comap_le_comap_add (f₁ f₂ : M ->ₛₗ[τ₁₂] M₂) : comap f₁ q ⊓ comap f₂ q 
<= comap (f₁ + f₂) q
参数：f₁ f₂ : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) :
    comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q := by
  simp only [SetLike.le_def, mem_comap, mem_inf, LinearMap.add_apply]
  exact fun _ h ↦ add_mem h.1 h.2
/-
**Submodule.surjOn_iff_le_map** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：surjOn_iff_le_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submod
ule R M} {q : Submodule R₂ M₂} : Set.SurjOn f p q ↔ q <= p.map f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma surjOn_iff_le_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} : Set.SurjOn f p q ↔ q ≤ p.map f :=
  Iff.rfl

end Submodule

namespace Submodule

variable {S N N₂ : Type*}
variable [CommSemiring S] [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable [AddCommMonoid N] [AddCommMonoid N₂] [Module S N] [Module S N₂]
variable {τ₁₂ : R →+* R₂}
variable (p : Submodule R M) (q : Submodule R₂ M₂)
variable (pₗ : Submodule S N) (qₗ : Submodule S N₂)

/-
**Submodule.comap_le_comap_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_le_comap_smul (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : comap f q <= comap (c 
• f) q
参数：f : M ->ₛₗ[τ₁₂] M₂；c : R₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem comap_le_comap_smul (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) : comap f q ≤ comap (c • f) q := by
  simp only [SetLike.le_def, mem_comap, LinearMap.smul_apply]
  exact fun _ h ↦ smul_mem _ _ h
/-
**Submodule.map_smul_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_smul_le_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : ma
p (c • f) p <= map f p
参数：f : M ->ₛₗ[τ₁₂] M₂；c : R₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.comap_le_comap_smul`：comap_le_comap_smul (f : M ->ₛₗ[τ₁₂] M₂) 
(c : R₂) : comap f q <= comap (c • f) q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_smul_le_map [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) :
    map (c • f) p ≤ map f p := by
  grw [map_le_iff_le_comap, ← comap_le_comap_smul (map f p) f c, ← map_le_iff_le_comap]

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
/-
**Submodule.compatibleMaps** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：compatibleMaps : Submodule S (N ->ₗ[S] N₂) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M
`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`.
-/
def compatibleMaps : Submodule S (N →ₗ[S] N₂) where
  carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)

end Submodule

namespace LinearMap

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

/-- The `LinearMap` from the preimage of a submodule to itself.

This is the linear version of `AddMonoidHom.addSubmonoidComap`
and `AddMonoidHom.addSubgroupComap`. -/
@[simps!]
/-
**LinearMap.submoduleComap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：submoduleComap (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) : q.comap f ->ₛₗ
[σ₁₂] q
参数：f : M ->ₛₗ[σ₁₂] M₂；q : Submodule R₂ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearMap` from the preimage of a submodule to itself.

This is the linear version of `AddMonoidHom.addSubmonoidComap`
and `AddMonoidHom.addSubgroupComap`.
-/
def submoduleComap (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) : q.comap f →ₛₗ[σ₁₂] q :=
  f.restrict fun _ ↦ Submodule.mem_comap.1
/-
**LinearMap.submoduleComap_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：submoduleComap_surjective_of_surjective (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodul
e R₂ M₂) (hf : Surjective f) : Surjective (f.submoduleComap q)
参数：f : M ->ₛₗ[σ₁₂] M₂；q : Submodule R₂ M₂；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.submoduleComap_apply_coe`：∀ {R : Type u_1} {R₂ : Type u_3} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submoduleComap_surjective_of_surjective (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
    (hf : Surjective f) : Surjective (f.submoduleComap q) := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

/-- A linear map between two modules restricts to a linear map from any submodule p of the
domain onto the image of that submodule.

This is the linear version of `AddMonoidHom.addSubmonoidMap` and `AddMonoidHom.addSubgroupMap`.

TODO: Consider making this an `abbrev`, dropping its API, and renaming to something like
`restrictSubmodule`. -/
/-
**LinearMap.submoduleMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：submoduleMap [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R
 M) : p ->ₛₗ[σ₁₂] p.map f
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map between two modules restricts to a linear map from any submodule p 
of the
domain onto the image of that submodule.

This is the linear version of `AddMonoidHom.addSubmonoidMap` and `AddMonoidHom.a
ddSubgroupMap`.

TODO: Consider making this an `abbrev`, dropping its API, and renaming to someth
ing like
`restrictSubmodule`.
-/
def submoduleMap [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p →ₛₗ[σ₁₂] p.map f :=
  f.restrict fun x hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
/-
**LinearMap.submoduleMap_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：submoduleMap_coe_apply [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {p : S
ubmodule R M} (x : p) : ↑(f.submoduleMap p x) = f x
参数：f : M ->ₛₗ[σ₁₂] M₂；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submoduleMap_coe_apply [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M}
    (x : p) : ↑(f.submoduleMap p x) = f x := rfl
/-
**LinearMap.submoduleMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：submoduleMap_surjective [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : 
Submodule R M) : Function.Surjective (f.submoduleMap p)
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.addSubmonoidMap_surjective`：∀ {M : Type u_1} {N : Type u_2}
 [inst : AddZeroClass M] [inst_1 : AddZeroClass N] (f : M →+ N) (M' : AddSubmono
id M),   Function.Surjective …
-/
theorem submoduleMap_surjective [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    Function.Surjective (f.submoduleMap p) := f.toAddMonoidHom.addSubmonoidMap_surjective _

@[grind inj]
/-
**LinearMap.submoduleMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：submoduleMap_injective [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : 
Injective f) (p : Submodule R M) : Injective (f.submoduleMap p)
参数：hf : Injective f；p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.addSubmonoidMap_injective`：∀ {M : Type u_1} {N : Type u_2} 
[inst : AddZeroClass M] [inst_1 : AddZeroClass N] {f : M →+ N},   Function.Injec
tive ⇑f → ∀ (M' : AddSubmono…
-/
theorem submoduleMap_injective [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : Injective f)
    (p : Submodule R M) : Injective (f.submoduleMap p) :=
  f.toAddMonoidHom.addSubmonoidMap_injective hf _
/-
**LinearMap.submoduleMap_injective_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：submoduleMap_injective_of_injOn [RingHomSurjective σ₁₂] {p : Submodule R M
} {f : M ->ₛₗ[σ₁₂] M₂} (hf : Set.InjOn f p) : Injective (f.submoduleMap p)
参数：hf : Set.InjOn f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submoduleMap_injective_of_injOn [RingHomSurjective σ₁₂]
    {p : Submodule R M} {f : M →ₛₗ[σ₁₂] M₂} (hf : Set.InjOn f p) :
    Injective (f.submoduleMap p) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  replace hxy : f x = f y := by simpa [Subtype.ext_iff] using hxy
  aesop

open Submodule
/-
**LinearMap.map_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ ->ₛₗ[σ
₂₁] M) (h p') : map (codRestrict p f h) p' = comap p.subtype (p'.map f)
参数：p : Submodule R M；f : M₂ ->ₛₗ[σ₂₁] M；h p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]
/-
**LinearMap.comap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_codRestrict (p : Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (hf p') : comap
 (codRestrict p f hf) p' = comap f (map p.subtype p')
参数：p : Submodule R M；f : M₂ ->ₛₗ[σ₂₁] M；hf p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    comap (codRestrict p f hf) p' = comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩
/-
**LinearMap.map_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_domRestrict [RingHomSurjective σ₂₁] (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ
[σ₂₁] M) (p') : map (domRestrict f p) p' = map f (map p.subtype p')
参数：p : Submodule R₂ M₂；f : M₂ ->ₛₗ[σ₂₁] M；p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
-/
theorem map_domRestrict [RingHomSurjective σ₂₁] (p : Submodule R₂ M₂) (f : M₂ →ₛₗ[σ₂₁] M) (p') :
    map (domRestrict f p) p' = map f (map p.subtype p') :=
  map_comp p.subtype f p'
/-
**LinearMap.comap_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_domRestrict (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p') : comap 
(domRestrict f p) p' = comap p.subtype (comap f p')
参数：p : Submodule R₂ M₂；f : M₂ ->ₛₗ[σ₂₁] M；p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_comp`：comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] 
M₃) (p : Submodule R₃ M₃) : comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap
 g p)
-/
theorem comap_domRestrict (p : Submodule R₂ M₂) (f : M₂ →ₛₗ[σ₂₁] M) (p') :
    comap (domRestrict f p) p' = comap p.subtype (comap f p') :=
  comap_comp p.subtype f p'

set_option backward.isDefEq.respectTransparency.types false in
/-
**LinearMap.map_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_restrict [RingHomSurjective σ₂₁] {p : Submodule R₂ M₂} {q : Submodule 
R M} {f : M₂ ->ₛₗ[σ₂₁] M} (h : forall x in p, f x in q) (p') : map (f.restrict h
) p' = comap q.subtype (map f (map p.subtype p'))
参数：h : forall x in p, f x in q；p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.restrict_eq_codRestrict_domRestrict`：restrict_eq_codRestrict_d
omRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} (hf : 
forall x in p, f x in q) : f.restri…
· 使用定理 `LinearMap.map_codRestrict`：map_codRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') : map (codRestrict p f h) p' = comap 
p.subtype (p'.m…
· 使用定理 `LinearMap.map_domRestrict`：map_domRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p') : map (domRestrict f p) p' = map f (m
ap p.subtype p'…
-/
theorem map_restrict [RingHomSurjective σ₂₁] {p : Submodule R₂ M₂} {q : Submodule R M}
    {f : M₂ →ₛₗ[σ₂₁] M} (h : ∀ x ∈ p, f x ∈ q) (p') :
    map (f.restrict h) p' = comap q.subtype (map f (map p.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict, map_codRestrict, map_domRestrict]

set_option backward.isDefEq.respectTransparency.types false in
/-
**LinearMap.comap_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_restrict {p : Submodule R₂ M₂} {q : Submodule R M} {f : M₂ ->ₛₗ[σ₂₁]
 M} (h : forall x in p, f x in q) (p') : comap (f.restrict h) p' = comap p.subty
pe (comap f (map q.subtype p'))
参数：h : forall x in p, f x in q；p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.restrict_eq_codRestrict_domRestrict`：restrict_eq_codRestrict_d
omRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} (hf : 
forall x in p, f x in q) : f.restri…
· 使用定理 `LinearMap.comap_codRestrict`：comap_codRestrict (p : Submodule R M) (f : 
M₂ ->ₛₗ[σ₂₁] M) (hf p') : comap (codRestrict p f hf) p' = comap f (map p.subtype
 p')
· 使用定理 `LinearMap.comap_domRestrict`：comap_domRestrict (p : Submodule R₂ M₂) (f 
: M₂ ->ₛₗ[σ₂₁] M) (p') : comap (domRestrict f p) p' = comap p.subtype (comap f p
')
-/
theorem comap_restrict {p : Submodule R₂ M₂} {q : Submodule R M} {f : M₂ →ₛₗ[σ₂₁] M}
    (h : ∀ x ∈ p, f x ∈ q) (p') :
    comap (f.restrict h) p' = comap p.subtype (comap f (map q.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict, comap_codRestrict, comap_domRestrict]

end LinearMap

/-! ### Linear equivalences -/

namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (e : M ≃ₛₗ[σ₁₂] M₂)

set_option backward.isDefEq.respectTransparency false in
/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap` on the left. -/
/-
**LinearEquiv.submoduleMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M ->ₛₗ[σ₁₂] M₂)
 : Submodule R₂ M₂)
参数：p : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A linear equivalence of two modules restricts to a linear equivalence from any s
ubmodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`
.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap
` on the left.
-/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, and_true, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }

@[simp]
/-
**LinearEquiv.submoduleMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e
 x
参数：p : Submodule R M；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl

@[simp]
/-
**LinearEquiv.submoduleMap_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：submoduleMap_symm_apply (p : Submodule R M) (x : (p.map (e : M ->ₛₗ[σ₁₂] M
₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x
参数：p : Submodule R M；x : (p.map (e : M ->ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl

end

end AddCommMonoid

end LinearEquiv

