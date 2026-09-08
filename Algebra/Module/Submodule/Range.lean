/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Set.Finite.Range

/-!
# Range of linear maps

The range `LinearMap.range` of a (semi)linear map `f : M → M₂` is a submodule of `M₂`.

More specifically, `LinearMap.range` applies to any `SemilinearMapClass` over a `RingHomSurjective`
ring homomorphism.

Note that this also means that dot notation (i.e. `f.range` for a linear map `f`) does not work.

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module, range
-/

@[expose] public section

open Function

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

section

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
/-
**LinearMap.range** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern].
-/
def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
/-
**LinearMap.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range f : Set M₂
) = Set.range f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : (range f : Set M₂) = Set.range f :=
  rfl
/-
**LinearMap.range_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range
 f).toAddSubmonoid = AddMonoidHom.mrange f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl

@[simp]
/-
**LinearMap.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {x} : x in range f 
↔ exists y, f y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
/-
**LinearMap.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : range f = map 
f ⊤
参数：f : M ->ₛₗ[τ₁₂] M₂。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_eq_map [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : range f = map f ⊤ := by
  ext
  simp
/-
**LinearMap.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_range_self [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (x : M) : f x 
in range f
参数：f : M ->ₛₗ[τ₁₂] M₂；x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_self [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (x : M) : f x ∈ range f :=
  ⟨x, rfl⟩

@[simp]
/-
**LinearMap.range_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id : range (LinearMap.id : M →ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id
/-
**LinearMap.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurject
ive τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g.comp f : M ->ₛₗ[τ
₁₃] M₃) = map g (range f)
参数：f : M ->ₛₗ[τ₁₂] M₂；g : M₂ ->ₛₗ[τ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)
/-
**LinearMap.range_comp_le_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M
 ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g.comp f : M ->ₛₗ[τ₁₃] M₃) <= rang
e g
参数：f : M ->ₛₗ[τ₁₂] M₂；g : M₂ ->ₛₗ[τ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
/-
**LinearMap.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊤ ↔ 
Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq_top [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} :
    range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff, coe_range, top_coe, Set.range_eq_univ]
/-
**LinearMap.range_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_top_of_surjective [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (h
f : Surjective f) : range f = ⊤
参数：f : M ->ₛₗ[τ₁₂] M₂；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
-/
theorem range_eq_top_of_surjective [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (hf : Surjective f) :
    range f = ⊤ := range_eq_top.2 hf
/-
**LinearMap.range_add_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_add_le [RingHomSurjective τ₁₂] (f g : M ->ₛₗ[τ₁₂] M₂) : range (f + g
) <= range f ⊔ range g
参数：f g : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem_sup`：add_mem_sup {S T : Submodule R M} {s t : M} (hs :
 s in S) (ht : t in T) : s + t in S ⊔ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem range_add_le [RingHomSurjective τ₁₂] (f g : M →ₛₗ[τ₁₂] M₂) :
    range (f + g) ≤ range f ⊔ range g := by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [mem_range, exists_apply_eq_apply]
/-
**LinearMap.range_le_iff_comap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_le_iff_comap [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submo
dule R₂ M₂} : range f <= p ↔ comap f p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
/-
**LinearMap.map_le_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R
 M} : map f p <= range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem map_le_range [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

@[simp]
/-
**LinearMap.range_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [
Ring R₂] [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : 
R ->+* R₂} [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) =
 LinearMap.range f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map_neg`：∀ {R : Type u_1} {M : Type u_5} {M₂ : Type u_7} [inst
 : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodu
le R M)…
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  rw [range_comp, Submodule.map_neg, Submodule.map_id]
/-
**LinearMap.range_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R
 →+* R₂} [inst_6 : RingHomSurjective τ₁₂] (K : Submodule R M) (f : M →ₛₗ[τ₁₂] M₂
),   (f.domRestrict K).range = Submodule.map f K
参数：K : Submodule R M；f : M →ₛₗ[τ₁₂] M₂；f.domRestrict K。
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma range_domRestrict [RingHomSurjective τ₁₂] (K : Submodule R M) (f : M →ₛₗ[τ₁₂] M₂) :
    range (domRestrict f K) = K.map f := by ext; simp
/-
**LinearMap.range_domRestrict_le_range** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (S
 : Submodule R M) : LinearMap.range (f.domRestrict S) <= LinearMap.range f
参数：f : M ->ₛₗ[τ₁₂] M₂；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
lemma range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (S : Submodule R M) :
    LinearMap.range (f.domRestrict S) ≤ LinearMap.range f := by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]
/-
**LinearMap._root_.AddMonoidHom.coe_toIntLinearMap_range** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_range {M M₂ : Type*} [AddCommGroup M]
    [AddCommGroup M₂] (f : M →+ M₂) :
    LinearMap.range f.toIntLinearMap = AddSubgroup.toIntSubmodule f.range := rfl
/-
**LinearMap._root_.Submodule.map_comap_eq_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submodule.map_comap_eq_of_le [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂}
    {p : Submodule R₂ M₂} (h : p ≤ LinearMap.range f) : (p.comap f).map f = p :=
  SetLike.coe_injective <| Set.image_preimage_eq_of_subset h
/-
**LinearMap.range_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_restrictScalars [SMul R R₂] [Module R₂ M] [Module R M₂] [CompatibleS
Mul M M₂ R R₂] [IsScalarTower R R₂ M₂] (f : M ->ₗ[R₂] M₂) : LinearMap.range (f.r
estrictScalars R) = (LinearMap.range f).restrictScalars R
参数：f : M ->ₗ[R₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_restrictScalars [SMul R R₂] [Module R₂ M] [Module R M₂] [CompatibleSMul M M₂ R R₂]
    [IsScalarTower R R₂ M₂] (f : M →ₗ[R₂] M₂) :
    LinearMap.range (f.restrictScalars R) = (LinearMap.range f).restrictScalars R := rfl

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
/-
**LinearMap.iterateRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：iterateRange (f : M ->ₗ[R] M) : Nat ->o (Submodule R M)ᵒᵈ where toFun n
参数：f : M ->ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decreasing sequence of submodules consisting of the ranges of the iterates o
f a linear map.
-/
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' := monotone_nat_of_le_succ fun | n, _, ⟨x, rfl⟩ => ⟨f x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.iterateRange_succ** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：iterateRange_succ {f : M ->ₗ[R] M} {n : Nat} : iterateRange f (n + 1) = (i
terateRange f n).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.iterateRange_coe`：∀ {R : Type u_1} {M : Type u_5} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : M →ₗ[R] M
) (n : ℕ), f.ite…
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `Module.End.iterate_succ'`：iterate_succ' (n : Nat) : f' ^ (n + 1) = .comp
 f' (f' ^ n)
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iterateRange_succ {f : M →ₗ[R] M} {n : ℕ} :
    iterateRange f (n + 1) = (iterateRange f n).map f := by
  simp only [iterateRange_coe, range_eq_map, ← map_comp, Module.End.iterate_succ']

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
/-
**LinearMap.rangeRestrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap`。
形式化陈述：rangeRestrict [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : M ->ₛₗ[τ₁₂] L
inearMap.range f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f

--- 原说明 ---
Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`.
-/
abbrev rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype M₂`. -/
/-
**LinearMap.fintypeRange** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M -
>ₛₗ[τ₁₂] M₂) : Fintype (range f)
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype M₂`.
-/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Fintype (range f) :=
  Set.fintypeRange f
/-
**LinearMap.range_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_codRestrict {τ₂₁ : R₂ ->+* R} [RingHomSurjective τ₂₁] (p : Submodule
 R M) (f : M₂ ->ₛₗ[τ₂₁] M) (hf) : range (codRestrict p f hf) = comap p.subtype (
LinearMap.range f)
参数：p : Submodule R M；f : M₂ ->ₛₗ[τ₂₁] M；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `LinearMap.map_codRestrict`：map_codRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') : map (codRestrict p f h) p' = comap 
p.subtype (p'.m…
-/
theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _
/-
**LinearMap._root_.Submodule.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂)
    (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
  le_antisymm (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩
/-
**LinearMap._root_.Submodule.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂}
    {q : Submodule R₂ M₂} (h : q ≤ range f) :
    map f (comap f q) = q := by
  rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]
/-
**LinearMap.range_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_zero [RingHomSurjective τ₁₂] : range (0 : M ->ₛₗ[τ₁₂] M₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_zero`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
-/
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _

section

variable [RingHomSurjective τ₁₂]

/-
**LinearMap.range_le_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_le_bot_iff (f : M ->ₛₗ[τ₁₂] M₂) : range f <= ⊥ ↔ f = 0
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
-/
theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top
/-
**LinearMap.range_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_le_bot_iff`：range_le_bot_iff (f : M ->ₛₗ[τ₁₂] M₂) : rang
e f <= ⊥ ↔ f = 0
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]
/-
**LinearMap.range_le_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃} : range f <= k
er g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun _ => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩
/-
**LinearMap.comap_le_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_le_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'} : comap 
f p <= comap f p' ↔ p <= p'
参数：hf : range f = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
-/
theorem comap_le_comap_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'} :
    comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H ↦ by rwa [SetLike.le_def, (range_eq_top.1 hf).forall], comap_mono⟩
/-
**LinearMap.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) : Injective (comap
 f)
参数：hf : range f = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.comap_le_comap_iff`：comap_le_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (h
f : range f = ⊤) {p p'} : comap f p <= comap f p' ↔ p <= p'
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem comap_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) : Injective (comap f) := fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

-- TODO (?): generalize the next two lemmas to semilinear maps with `f ∘ₗ g` bijective.
/-
**LinearMap.ker_eq_range_of_comp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_range_of_comp_eq_id {M P} [AddCommGroup M] [Module R M] [AddCommGro
up P] [Module R P] {f : M ->ₗ[R] P} {g : P ->ₗ[R] M} (h : f ∘ₗ g = .id) : ker f 
= range (LinearMap.id - g ∘ₗ f)
参数：h : f ∘ₗ g = .id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用定理 `LinearMap.comp_sub`：comp_sub (f g : M ->ₛₗ[σ₁₂] N₂) (h : N₂ ->ₛₗ[σ₂₃] N₃
) : h.comp (g - f) = h.comp g - h.comp f
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem ker_eq_range_of_comp_eq_id {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M →ₗ[R] P} {g : P →ₗ[R] M} (h : f ∘ₗ g = .id) :
    ker f = range (LinearMap.id - g ∘ₗ f) :=
  le_antisymm (fun x hx ↦ ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩) <|
    range_le_ker_iff.mpr <| by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

/-- If `f : E →ₗ[R] F` has a left inverse `g`, then `range f = ker (f ∘ g - id)`.

This is the dual version of `LinearMap.ker_eq_range_of_comp_eq_id`. -/
/-
**LinearMap.range_eq_ker_of_leftInverse** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_eq_ker_of_leftInverse {M P} [AddCommGroup M] [Module R M] [AddCommGr
oup P] [Module R P] {f : M ->ₗ[R] P} {g : P ->ₗ[R] M} (h : LeftInverse g f) : f.
range = ker ((f.comp g) - LinearMap.id)
参数：h : LeftInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f : E →ₗ[R] F` has a left inverse `g`, then `range f = ker (f ∘ g - id)`.

This is the dual version of `LinearMap.ker_eq_range_of_comp_eq_id`.
-/
lemma range_eq_ker_of_leftInverse {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M →ₗ[R] P} {g : P →ₗ[R] M}
    (h : LeftInverse g f) : f.range = ker ((f.comp g) - LinearMap.id) :=
  -- If `y = f x ∈ range f`, we have `(f ∘ g) y = f (g (f x)) = f x = y` by hypothesis `h`.
  -- Conversely, f g z - z = 0 implies z = f (g z) ∈ range f.
  le_antisymm (by rintro y ⟨x, rfl⟩; simp [h x]) (fun x hx ↦ ⟨g x, by simpa [sub_eq_zero] using hx⟩)

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}
variable {f : M →ₛₗ[τ₁₂] M₂}

open Submodule

/-
**LinearMap.range_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range 
f).toAddSubgroup = f.toAddMonoidHom.range
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubgroup = f.toAddMonoidHom.range :=
  rfl
/-
**LinearMap.ker_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} : ker f <= p ↔ exis
ts y in range f, f ⁻¹' {y} subseteq p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe, coe_range, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

end Ring

section CommSemiring

variable [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

/-
**LinearMap.range_smul_le_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_smul_le_range (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : range (c • f) <= range
 f
参数：f : M ->ₛₗ[τ₁₂] M₂；c : R₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_smul_le_map`：map_smul_le_map [RingHomSurjective τ₁₂] (f : 
M ->ₛₗ[τ₁₂] M₂) (c : R₂) : map (c • f) p <= map f p
-/
theorem range_smul_le_range (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) : range (c • f) ≤ range f := by
  simpa only [range_eq_map] using Submodule.map_smul_le_map _ _ _

end CommSemiring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/-
**LinearMap.range_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : range (a • f) = range 
f
参数：f : V ->ₗ[K] V₂；a : K；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_smul`：∀ {K : Type u_9} {V : Type u_10} {V₂ : Type u_11} [i
nst : Semifield K] [inst_1 : AddCommMonoid V]   [inst_2 : _root_.Module K V] [in
st_3 : A…
-/
theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f := by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h
/-
**LinearMap.range_smul'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_smul' (f : V ->ₗ[K] V₂) (a : K) : range (a • f) = ⨆ _ : a != 0, rang
e f
参数：f : V ->ₗ[K] V₂；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Submodule.map_smul'`：map_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V) (a 
: K) : p.map (a • f) = ⨆ _ : a != 0, map f p
-/
theorem range_smul' (f : V →ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a ≠ 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R →+* R₂}

open LinearMap

@[simp]
/-
**Submodule.map_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : map f ⊤ = range f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
-/
theorem map_top [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : map f ⊤ = range f :=
  (range_eq_map f).symm

@[simp]
/-
**Submodule.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_subtype : range p.subtype = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
-/
theorem range_subtype : range p.subtype = p := by simpa using map_comap_subtype p ⊤
/-
**Submodule.map_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_subtype_le (p' : Submodule R p) : map p.subtype p' <= p
参数：p' : Submodule R p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f
-/
theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ range p.subtype)

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p`. -/
/-
**Submodule.map_subtype_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_subtype_top : map p.subtype (⊤ : Submodule R p) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Under the canonical linear map from a submodule `p` to the ambient space `M`, th
e image of the
maximal submodule of `p` is just `p`.
-/
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp

@[simp]
/-
**Submodule.comap_subtype_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p <
= p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [map_subtype_top]
/-
**Submodule.submoduleOf_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {p q : Submodule R M}, p.submoduleOf q = ⊤ ↔
 q ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma submoduleOf_eq_top {p q : Submodule R M} :
    p.submoduleOf q = ⊤ ↔ q ≤ p := by simp [submoduleOf]

@[simp]
/-
**Submodule.comap_subtype_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_subtype_self : comap p.subtype p = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.comap_subtype_eq_top`：comap_subtype_eq_top {p p' : Submodule R
 M} : comap p.subtype p' = ⊤ ↔ p <= p'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl
/-
**Submodule.submoduleOf_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：submoduleOf_self (N : Submodule R M) : N.submoduleOf N = ⊤
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
-/
theorem submoduleOf_self (N : Submodule R M) : N.submoduleOf N = ⊤ := comap_subtype_self _
/-
**Submodule.submoduleOf_sup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：submoduleOf_sup_of_le {N₁ N₂ N : Submodule R M} (h₁ : N₁ <= N) (h₂ : N₂ <=
 N) : (N₁ ⊔ N₂).submoduleOf N = N₁.submoduleOf N ⊔ N₂.submoduleOf N
参数：h₁ : N₁ <= N；h₂ : N₂ <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem submoduleOf_sup_of_le {N₁ N₂ N : Submodule R M} (h₁ : N₁ ≤ N) (h₂ : N₂ ≤ N) :
    (N₁ ⊔ N₂).submoduleOf N = N₁.submoduleOf N ⊔ N₂.submoduleOf N := by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

@[simp]
/-
**Submodule.comap_subtype_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：comap_subtype_le_iff {p q r : Submodule R M} : q.comap p.subtype <= r.coma
p p.subtype ↔ p ⊓ q <= p ⊓ r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
-/
lemma comap_subtype_le_iff {p q r : Submodule R M} :
    q.comap p.subtype ≤ r.comap p.subtype ↔ p ⊓ q ≤ p ⊓ r :=
  ⟨fun h ↦ by simpa using map_mono (f := p.subtype) h,
   fun h ↦ by simpa using comap_mono (f := p.subtype) h⟩
/-
**Submodule.range_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_inclusion (p q : Submodule R M) (h : p <= q) : range (inclusion h) =
 comap q.subtype p
参数：p q : Submodule R M；h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.inclusion.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p p' : Submodul
e R M} (h : p …
· 使用定理 `LinearMap.map_codRestrict`：map_codRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') : map (codRestrict p f h) p' = comap 
p.subtype (p'.m…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem range_inclusion (p q : Submodule R M) (h : p ≤ q) :
    range (inclusion h) = comap q.subtype p := by
  rw [← map_top, inclusion, LinearMap.map_codRestrict, map_top, range_subtype]

@[simp]
/-
**Submodule.map_subtype_range_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_subtype_range_inclusion {p p' : Submodule R M} (h : p <= p') : map p'.
subtype (range <| inclusion h) = p
参数：h : p <= p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_inclusion`：range_inclusion (p q : Submodule R M) (h : p 
<= q) : range (inclusion h) = comap q.subtype p
· 使用定理 `Submodule.map_comap_eq`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} 
{M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_subtype_range_inclusion {p p' : Submodule R M} (h : p ≤ p') :
    map p'.subtype (range <| inclusion h) = p := by simp [range_inclusion, map_comap_eq, h]
/-
**Submodule.restrictScalars_map** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：restrictScalars_map [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower
 R R₂ M] [IsScalarTower R R₂ M₂] (f : M ->ₗ[R₂] M₂) (M' : Submodule R₂ M) : (M'.
map f).restrictScalars R = (M'.restrictScalars R).map (f.restrictScalars R)
参数：f : M ->ₗ[R₂] M₂；M' : Submodule R₂ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrictScalars_map [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower R R₂ M]
    [IsScalarTower R R₂ M₂] (f : M →ₗ[R₂] M₂) (M' : Submodule R₂ M) :
    (M'.map f).restrictScalars R = (M'.restrictScalars R).map (f.restrictScalars R) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`.

See also `Submodule.mapIic`. -/
/-
**Submodule.MapSubtype.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.MapSubtype`
。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → (p : Submodule R M
) → Submodule R ↥p ≃o { p' // p' ≤ p }
参数：p : Submodule R M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p

--- 原说明 ---
If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in
 `N`.

See also `Submodule.mapIic`.
-/
def MapSubtype.orderIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
  right_inv := fun ⟨q, hq⟩ => Subtype.ext <| by simp [map_comap_subtype p, inf_of_le_right hq]
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans <| by
    dsimp
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
/-
**Submodule.MapSubtype.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.MapSu
btype`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → (p : Submodule R M) → Subm
odule R ↥p ↪o Submodule R M
参数：p : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the 
ordering of
submodules of `M`.
-/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.orderIso p).trans <|
    Subtype.relEmbedding (X := Submodule R M) (fun p p' ↦ p ≤ p') _

@[simp]
/-
**Submodule.map_subtype_embedding_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_subtype_embedding_eq (p' : Submodule R p) : MapSubtype.orderEmbedding 
p p' = map p.subtype p'
参数：p' : Submodule R p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_subtype_embedding_eq (p' : Submodule R p) :
    MapSubtype.orderEmbedding p p' = map p.subtype p' :=
  rfl

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`. -/
/-
**Submodule.mapIic** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mapIic (p : Submodule R M) : Submodule R p ≃o Set.Iic p
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in
 `N`.
-/
def mapIic (p : Submodule R M) :
    Submodule R p ≃o Set.Iic p :=
  Submodule.MapSubtype.orderIso p
/-
**Submodule.coe_mapIic_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (p : Submodule R M) (q : Submodule R ↥p), ↑(
p.mapIic q) = Submodule.map p.subtype q
参数：p : Submodule R M；q : Submodule R ↥p；p.mapIic q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mapIic_apply
    (p : Submodule R M) (q : Submodule R p) :
    (p.mapIic q : Submodule R M) = q.map p.subtype :=
  rfl
/-
**Submodule.codisjoint_map** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：codisjoint_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} (hf : Function
.Surjective f) {p q : Submodule R M} (hpq : Codisjoint p q) : Codisjoint (p.map 
f) (q.map f)
参数：hf : Function.Surjective f；hpq : Codisjoint p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
-/
lemma codisjoint_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} (hf : Function.Surjective f)
    {p q : Submodule R M} (hpq : Codisjoint p q) : Codisjoint (p.map f) (q.map f) := by
  rw [codisjoint_iff, ← Submodule.map_sup, codisjoint_iff.mp hpq, map_top,
    LinearMap.range_eq_top_of_surjective f hf]

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- A monomorphism is injective. -/
/-
**LinearMap.ker_eq_bot_of_cancel** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_of_cancel {f : M ->ₛₗ[τ₁₂] M₂} (h : forall u v : ker f ->ₗ[R] M
, f.comp u = f.comp v -> u = v) : ker f = ⊥
参数：h : forall u v : ker f ->ₗ[R] M, f.comp u = f.comp v -> u = v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp_ker_subtype`：comp_ker_subtype (f : M ->ₛₗ[τ₁₂] M₂) : f.co
mp (ker f).subtype = 0
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥

--- 原说明 ---
A monomorphism is injective.
-/
theorem ker_eq_bot_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : ker f →ₗ[R] M, f.comp u = f.comp v → u = v) : ker f = ⊥ := by
  have h₁ : f.comp (0 : ker f →ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f),
    ← h 0 (ker f).subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero
/-
**LinearMap.range_comp_of_range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
 [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃) (hf : range 
f = ⊤) : range (g.comp f : M ->ₛₗ[τ₁₃] M₃) = range g
参数：g : M₂ ->ₛₗ[τ₂₃] M₃；hf : range f = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
-/
theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]

section Image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submoduleImage N` is `ϕ(N)` as a submodule of `M'` -/
/-
**LinearMap.submoduleImage** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodul
e R M} (ϕ : O ->ₗ[R] M') (N : Submodule R M) : Submodule R M'
参数：ϕ : O ->ₗ[R] M'；N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submoduleImage N` is `ϕ(N)` as a submodule of `M'`
-/
def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ

@[simp]
/-
**LinearMap.mem_submoduleImage** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Subm
odule R M} {ϕ : O ->ₗ[R] M'} {N : Submodule R M} {x : M'} : x in ϕ.submoduleImag
e N ↔ exists (y : _) (yO : y in O), y in N ∧ ϕ ⟨y, yO⟩ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O), y ∈ N ∧ ϕ ⟨y, yO⟩ = x := by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩
/-
**LinearMap.mem_submoduleImage_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O 
: Submodule R M} {ϕ : O ->ₗ[R] M'} {N : Submodule R M} (hNO : N <= O) {x : M'} :
 x in ϕ.submoduleImage N ↔ exists (y : _) (yN : y in N), ϕ ⟨y, hNO yN⟩ = x
参数：hNO : N <= O。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} (hNO : N ≤ O) {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  grind [mem_submoduleImage]
/-
**LinearMap.submoduleImage_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：submoduleImage_apply_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {
O : Submodule R M} (ϕ : O ->ₗ[R] M') (N : Submodule R M) (hNO : N <= O) : ϕ.subm
oduleImage N = range (ϕ.comp (Submodule.inclusion hNO))
参数：ϕ : O ->ₗ[R] M'；N : Submodule R M；hNO : N <= O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.submoduleImage.eq_1`：∀ {R : Type u_1} {M : Type u_5} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {M' : Type 
u_10} [inst_3 : Add…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.range_inclusion`：range_inclusion (p q : Submodule R M) (h : p 
<= q) : range (inclusion h) = comap q.subtype p
-/
theorem submoduleImage_apply_of_le {M' : Type*} [AddCommMonoid M'] [Module R M']
    {O : Submodule R M} (ϕ : O →ₗ[R] M') (N : Submodule R M) (hNO : N ≤ O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.inclusion hNO)) := by
  rw [submoduleImage, range_comp, Submodule.range_inclusion]

end Image

section rangeRestrict

variable [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂)

/-
**LinearMap.range_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R
 →+* R₂} [inst_6 : RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂), f.rangeRestrict.r
ange = ⊤
参数：f : M →ₛₗ[τ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `LinearMap.range_codRestrict`：range_codRestrict {τ₂₁ : R₂ ->+* R} [RingHo
mSurjective τ₂₁] (p : Submodule R M) (f : M₂ ->ₛₗ[τ₂₁] M) (hf) : range (codRestr
ict p f hf) = com…
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem range_rangeRestrict : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]
/-
**LinearMap.surjective_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：surjective_rangeRestrict : Surjective f.rangeRestrict
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
-/
theorem surjective_rangeRestrict : Surjective f.rangeRestrict := by
  rw [← range_eq_top, range_rangeRestrict]
/-
**LinearMap.ker_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_rangeRestrict : ker f.rangeRestrict = ker f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
theorem ker_rangeRestrict : ker f.rangeRestrict = ker f := LinearMap.ker_codRestrict _ _ _
/-
**LinearMap.injective_rangeRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_6} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R
 →+* R₂} [inst_6 : RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂),   Function.Inject
ive ⇑f.rangeRestrict ↔ Function.Injective ⇑f
参数：f : M →ₛₗ[τ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
@[simp] theorem injective_rangeRestrict_iff : Injective f.rangeRestrict ↔ Injective f :=
  Set.injective_codRestrict _

end rangeRestrict

section restrict

open Submodule

variable [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}

@[simp]
/-
**LinearMap.range_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_restrict (h : forall x in p, f x in q) : range (f.restrict h) = coma
p q.subtype (map f p)
参数：h : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.map_restrict`：map_restrict [RingHomSurjective σ₂₁] {p : Submod
ule R₂ M₂} {q : Submodule R M} {f : M₂ ->ₛₗ[σ₂₁] M} (h : forall x in p, f x in q
) (p') : map…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem range_restrict (h : ∀ x ∈ p, f x ∈ q) :
    range (f.restrict h) = comap q.subtype (map f p) := by
  rw [← Submodule.map_top, map_restrict, Submodule.map_top, p.range_subtype]

end restrict

end Semiring

end LinearMap

