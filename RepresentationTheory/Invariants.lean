/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Subspace of invariants a group representation

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of `k[G]`.
The action of this special element gives a projection onto the subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

@[expose] public section

suppress_compilation

universe w u v

open MonoidAlgebra

open Representation

namespace GroupAlgebra

variable (k G : Type*) [CommSemiring k] [Group G]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The average of all elements of the group `G`, considered as an element of `k[G]`. -/
/-
**GroupAlgebra.average** 是 Mathlib 中的一个定义，位于命名空间 `GroupAlgebra`。
形式化陈述：average : k[G]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The average of all elements of the group `G`, considered as an element of `k[G]`
.
-/
noncomputable def average : k[G] := ⅟(Fintype.card G : k) • ∑ g : G, of k G g

set_option backward.isDefEq.respectTransparency.types false in
/-- `average k G` is invariant under left multiplication by elements of `G`. -/
@[simp]
/-
**GroupAlgebra.mul_average_left** 是 Mathlib 中的一个定理，位于命名空间 `GroupAlgebra`。
形式化陈述：mul_average_left (g : G) : .single g 1 * average k G = average k G
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Group.mulLeft_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Func
tion.Bijective fun x => a * x

--- 原说明 ---
`average k G` is invariant under left multiplication by elements of `G`.
-/
theorem mul_average_left (g : G) : .single g 1 * average k G = average k G := by
  simp only [mul_one, Finset.mul_sum, Algebra.mul_smul_comm, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (g * x) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) _]

set_option backward.isDefEq.respectTransparency.types false in
/-- `average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
/-
**GroupAlgebra.mul_average_right** 是 Mathlib 中的一个定理，位于命名空间 `GroupAlgebra`。
形式化陈述：mul_average_right (g : G) : average k G * .single g 1 = average k G
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Group.mulRight_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Fun
ction.Bijective fun x => x * a

--- 原说明 ---
`average k G` is invariant under right multiplication by elements of `G`.
-/
theorem mul_average_right (g : G) : average k G * .single g 1 = average k G := by
  simp only [mul_one, Finset.sum_mul, Algebra.smul_mul_assoc, average, MonoidAlgebra.of_apply,
    MonoidAlgebra.single_mul_single]
  set f : G → k[G] := fun x => .single x 1
  change ⅟(Fintype.card G : k) • ∑ x : G, f (x * g) = ⅟(Fintype.card G : k) • ∑ x : G, f x
  rw [Function.Bijective.sum_comp (Group.mulRight_bijective g) _]

end GroupAlgebra

namespace Representation

section Invariants

open GroupAlgebra

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

/-- The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
/-
**Representation.invariants** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：invariants : Submodule k V where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subspace of invariants, consisting of the vectors fixed by all elements of `
G`.
-/
def invariants : Submodule k V where
  carrier := Set.ofPred fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]
/-
**Representation.mem_invariants** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：mem_invariants (v : V) : v in invariants ρ ↔ forall g : G, ρ g v = v
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ g : G, ρ g v = v := by rfl
/-
**Representation.invariants_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoin
ts (ρ g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
theorem invariants_eq_inter : (invariants ρ).carrier = ⋂ g : G, Function.fixedPoints (ρ g) := by
  ext; simp [Function.IsFixedPt]
/-
**Representation.invariants_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：invariants_eq_top [ρ.IsTrivial] : invariants ρ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Representation.isTrivial_apply`：isTrivial_apply (ρ : Representation k G 
V) [IsTrivial ρ] (g : G) (x : V) : ρ g x = x
-/
theorem invariants_eq_top [ρ.IsTrivial] :
    invariants ρ = ⊤ :=
eq_top_iff.2 (fun x _ g => ρ.isTrivial_apply g x)
/-
**Representation.mem_invariants_iff_of_forall_mem_zpowers** 是 Mathlib 中的一个引理，位于命
名空间 `Representation`。
形式化陈述：mem_invariants_iff_of_forall_mem_zpowers (g : G) (hg : forall x, x in Subg
roup.zpowers g) (x : V) : x in ρ.invariants ↔ ρ g x = x
参数：g : G；hg : forall x, x in Subgroup.zpowers g；x : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `neg_sub_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α
), -a - b = -b - a
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Representation.inv_self_apply`：inv_self_apply (g : G) (x : V) : ρ g⁻¹ (ρ
 g x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_invariants_iff_of_forall_mem_zpowers
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : V) :
    x ∈ ρ.invariants ↔ ρ g x = x :=
  ⟨fun h => h g, fun hx γ => by
    rcases hg γ with ⟨i, rfl⟩
    induction i with | zero => simp | succ i _ => simp_all [zpow_add_one] | pred i h => _
    simpa [neg_sub_comm _ (1 : ℤ), zpow_sub] using congr(ρ g⁻¹ $(h.trans hx.symm))⟩

variable {ρ σ} in
/-
**Representation.mem_linHom_invariants_iff_isIntertwining** 是 Mathlib 中的一个定理，位于命
名空间 `Representation`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Comm
Ring k] [inst_1 : Group G]   [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k
 V] [inst_4 : AddCommGroup W] [inst_5 : _root_.Module k W]   {ρ : Representation
 k G V} {σ : Representation k G W} (f : V →ₗ[k] W),   (∀ (g : G), σ g ∘ₗ f ∘ₗ ρ 
g⁻¹ = f) ↔ ρ.IsIntertwiningMap σ f
参数：f : V →ₗ[k] W；∀ (g : G), σ g ∘ₗ f ∘ₗ ρ g⁻¹ = f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Representation.inv_self_apply`：inv_self_apply (g : G) (x : V) : ρ g⁻¹ (ρ
 g x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Representation.IsIntertwiningMap.isIntertwining`：∀ {A : Type u_1} {G : T
ype u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]  
 [inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `Representation.self_inv_apply`：self_inv_apply (g : G) (x : V) : ρ g (ρ g
⁻¹ x) = x
-/
@[simp] lemma mem_linHom_invariants_iff_isIntertwining (f : V →ₗ[k] W) :
    (∀ (g : G), σ g ∘ₗ f ∘ₗ ρ g⁻¹ = f) ↔ ρ.IsIntertwiningMap σ f := by
  refine ⟨fun hf ↦ ⟨fun γ v ↦ ?_⟩, fun hf γ ↦ ?_⟩
  · specialize hf γ
    nth_rewrite 1 [← hf]
    simp
  · ext v
    simp [hf.isIntertwining]

/-- The invariants of the representation `linHom ρ σ` correspond to intertwining maps
from `ρ` to `σ`. -/
/-
**Representation.invariantsEquivIntertwiningMap** 是 Mathlib 中的一个定义，位于命名空间 `Repre
sentation`。
形式化陈述：invariantsEquivIntertwiningMap : (linHom ρ σ).invariants ≃ₗ[k] Intertwinin
gMap ρ σ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The invariants of the representation `linHom ρ σ` correspond to intertwining map
s
from `ρ` to `σ`.
-/
def invariantsEquivIntertwiningMap : (linHom ρ σ).invariants ≃ₗ[k] IntertwiningMap ρ σ where
  toFun f := f.val.intertwiningMap_of_isIntertwiningMap ρ σ
    ((mem_linHom_invariants_iff_isIntertwining f.val).mp f.property).isIntertwining
  map_add' _ _ := IntertwiningMap.ext_iff.mpr rfl
  map_smul' _ _ := IntertwiningMap.ext_iff.mpr rfl
  invFun g :=
    { val := g.toLinearMap
      property := (mem_linHom_invariants_iff_isIntertwining g.toLinearMap).mpr
        { isIntertwining := g.isIntertwining } }

section

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
/-
**Representation.averageMap** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：averageMap : V ->ₗ[k] V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `average k G` gives a projection map onto the subspace of invarian
ts.
-/
noncomputable def averageMap : V →ₗ[k] V :=
  asAlgebraHom ρ (average k G)

/-- The `averageMap` sends elements of `V` to the subspace of invariants.
-/
/-
**Representation.averageMap_invariant** 是 Mathlib 中的一个定理，位于命名空间 `Representation`
。
形式化陈述：averageMap_invariant (v : V) : averageMap ρ v in invariants ρ
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.averageMap.eq_1`：∀ {k : Type u_1} {G : Type u_2} {V : Typ
e u_3} [inst : CommRing k] [inst_1 : Group G] [inst_2 : AddCommGroup V]   [inst_
3 : _root_.Module k …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Representation.asAlgebraHom_single_one`：asAlgebraHom_single_one (g : G) 
: asAlgebraHom ρ (MonoidAlgebra.single g 1) = ρ g
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `GroupAlgebra.mul_average_left`：mul_average_left (g : G) : .single g 1 * 
average k G = average k G

--- 原说明 ---
The `averageMap` sends elements of `V` to the subspace of invariants.
-/
theorem averageMap_invariant (v : V) : averageMap ρ v ∈ invariants ρ := fun g => by
  rw [averageMap, ← asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul (asAlgebraHom ρ),
    mul_average_left]

/-- The `averageMap` acts as the identity on the subspace of invariants.
-/
/-
**Representation.averageMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：averageMap_id (v : V) (hv : v in invariants ρ) : averageMap ρ v = v
参数：v : V；hv : v in invariants ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Representation.mem_invariants`：mem_invariants (v : V) : v in invariants 
ρ ↔ forall g : G, ρ g v = v
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `averageMap` acts as the identity on the subspace of invariants.
-/
theorem averageMap_id (v : V) (hv : v ∈ invariants ρ) : averageMap ρ v = v := by
  rw [mem_invariants] at hv
  simp [average, map_sum, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k _ v, smul_smul]
/-
**Representation.isProj_averageMap** 是 Mathlib 中的一个定理，位于命名空间 `Representation`。
形式化陈述：isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.averageMap_invariant`：averageMap_invariant (v : V) : aver
ageMap ρ v in invariants ρ
· 使用定理 `Representation.averageMap_id`：averageMap_id (v : V) (hv : v in invariant
s ρ) : averageMap ρ v = v
-/
theorem isProj_averageMap : LinearMap.IsProj ρ.invariants ρ.averageMap :=
  ⟨ρ.averageMap_invariant, ρ.averageMap_id⟩

end
section Subgroup

variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-
**Representation.le_comap_invariants** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：le_comap_invariants (g : G) : (invariants <| ρ.comp S.subtype) <= (invaria
nts <| ρ.comp S.subtype).comap (ρ g)
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem'`：conj_mem' (nH : H.Normal) (n : G) (hn : n in 
H) (g : G) : g⁻¹ * n * g in H
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Representation.self_inv_apply`：self_inv_apply (g : G) (x : V) : ρ g (ρ g
⁻¹ x) = x
-/
lemma le_comap_invariants (g : G) :
    (invariants <| ρ.comp S.subtype) ≤
      (invariants <| ρ.comp S.subtype).comap (ρ g) :=
  fun x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
/-
**Representation.toInvariants** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：toInvariants : Representation k G (invariants (ρ.comp S.subtype))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.le_comap_invariants`：le_comap_invariants (g : G) : (invar
iants <| ρ.comp S.subtype) <= (invariants <| ρ.comp S.subtype).comap (ρ g)

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-rep
resentation on
the invariants of `ρ|_S`.
-/
abbrev toInvariants :
    Representation k G (invariants (ρ.comp S.subtype)) :=
  subrepresentation ρ _ <| le_comap_invariants ρ S
/-
**Representation.** 是 Mathlib 中的一个实例，位于命名空间 `Representation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrivial ((toInvariants ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
/-
**Representation.quotientToInvariants** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representatio
n`。
形式化陈述：quotientToInvariants : Representation k (G ⧸ S) (invariants (ρ.comp S.subt
ype))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.instIsTrivialSubtypeMemSubgroupSubmoduleInvariantsCompLin
earMapIdSubtypeToInvariants`：∀ {k : Type u_1} {G : Type u_2} [inst : CommRing k]
 [inst_1 : Group G] {V : Type u_5} [inst_2 : AddCommGroup V]   [inst_3 : _root_.
Module k …

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-repr
esentation on
the invariants of `ρ|_S`.
-/
abbrev quotientToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotient (toInvariants ρ S) S

/-- The intertwining map between the `G ⧸ S`-representation on the invariants of `ρ|_S` and `ρ`. -/
/-
**Representation.quotientToInvariants_lift** 是 Mathlib 中的一个缩写定义，位于命名空间 `Represen
tation`。
形式化陈述：quotientToInvariants_lift : Representation.IntertwiningMap (MonoidHom.comp
 (quotientToInvariants ρ S) (QuotientGroup.mk' _)) ρ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intertwining map between the `G ⧸ S`-representation on the invariants of `ρ|
_S` and `ρ`.
-/
abbrev quotientToInvariants_lift :
    Representation.IntertwiningMap (MonoidHom.comp (quotientToInvariants ρ S)
      (QuotientGroup.mk' _)) ρ := ⟨Submodule.subtype _, fun _ ↦ rfl⟩

end Subgroup
end Invariants

namespace linHom

open CategoryTheory Action

section Rep

variable {k : Type u} [CommRing k] {G : Type v} [Group G] {X Y : Rep.{w} k G}

/-
**Representation.linHom.mem_invariants_iff_comm** 是 Mathlib 中的一个定理，位于命名空间 `Repre
sentation.linHom`。
形式化陈述：mem_invariants_iff_comm (f : X.V ->ₗ[k] Y.V) (g : G) : (linHom X.ρ Y.ρ) g 
f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f
参数：f : X.V ->ₗ[k] Y.V；g : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `Rep.ρ_mul`：ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Module.End.one_eq_id`：one_eq_id : (1 : Module.End R M) = .id
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem mem_invariants_iff_comm (f : X.V →ₗ[k] Y.V) (g : G) :
    (linHom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f := by
  dsimp
  constructor
  · intro h
    nth_rw 1 [← h]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← Rep.ρ_mul, inv_mul_cancel, map_one,
      Module.End.one_eq_id, LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc, ← h, LinearMap.comp_assoc, ← Rep.ρ_mul, mul_inv_cancel, map_one,
      Module.End.one_eq_id, LinearMap.comp_id]

variable (X Y) in
/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
@[simps]
/-
**Representation.linHom.invariantsEquivRepHom** 是 Mathlib 中的一个定义，位于命名空间 `Represe
ntation.linHom`。
形式化陈述：invariantsEquivRepHom : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where toFu
n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The invariants of the representation `linHom X.ρ Y.ρ` correspond to the represen
tation
homomorphisms from `X` to `Y`.
-/
def invariantsEquivRepHom : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y where
  toFun f := Rep.ofHom ⟨f.val, fun g ↦ (mem_invariants_iff_comm _ g).1 <| f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.hom, fun g => (mem_invariants_iff_comm _ g).2 <| f.hom.2 g⟩

end Rep

section FDRep

variable {k : Type u} [Field k] {G : Type v} [Group G]

/-- The invariants of the representation `linHom X.ρ Y.ρ` correspond to the representation
homomorphisms from `X` to `Y`. -/
/-
**Representation.linHom.invariantsEquivFDRepHom** 是 Mathlib 中的一个定义，位于命名空间 `Repre
sentation.linHom`。
形式化陈述：invariantsEquivFDRepHom (X Y : FDRep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ
[k] X ⟶ Y
参数：X Y : FDRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The invariants of the representation `linHom X.ρ Y.ρ` correspond to the represen
tation
homomorphisms from `X` to `Y`.
-/
def invariantsEquivFDRepHom (X Y : FDRep k G) : (linHom X.ρ Y.ρ).invariants ≃ₗ[k] X ⟶ Y := by
  rw [← FDRep.forget₂_ρ, ← FDRep.forget₂_ρ]
  -- Porting note: The original version used `linHom.invariantsEquivRepHom _ _ ≪≫ₗ`
  exact linHom.invariantsEquivRepHom
    ((forget₂ (FDRep k G) (Rep k G)).obj X) ((forget₂ (FDRep k G) (Rep k G)).obj Y) ≪≫ₗ
    FDRep.forget₂HomLinearEquiv X Y

end FDRep

end linHom

end Representation

namespace Rep

open CategoryTheory

variable {k : Type u} {G : Type v} [CommRing k] [Group G] (A : Rep.{w} k G)
  (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
/-
**Rep.toInvariants** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：toInvariants : Rep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-rep
resentation on
the invariants of `ρ|_S`.
-/
abbrev toInvariants : Rep k G := Rep.of <| A.ρ.toInvariants S

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
/-
**Rep.quotientToInvariants** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：quotientToInvariants : Rep k (G ⧸ S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-repr
esentation on
the invariants of `ρ|_S`.
-/
abbrev quotientToInvariants : Rep k (G ⧸ S) := Rep.of (A.ρ.quotientToInvariants S)

variable (k G)

/-- The functor sending a representation to its submodule of invariants. -/
@[implicit_reducible, simps! obj_carrier map_hom]
/-
**Rep.invariantsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：invariantsFunctor : Rep.{w} k G ⥤ ModuleCat k where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a representation to its submodule of invariants.
-/
noncomputable def invariantsFunctor : Rep.{w} k G ⥤ ModuleCat k where
  obj A := ModuleCat.of k A.ρ.invariants
  map {A B} f := ModuleCat.ofHom <| (f.hom ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by
      have := (hom_comm_apply f g c).symm
      simp_all [hc g]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (invariantsFunctor k G).PreservesZeroMorphisms where
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (invariantsFunctor k G).Additive where
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (invariantsFunctor k G).Linear k where

variable {G} in
/-- Given a normal subgroup S ≤ G, this is the functor sending a `G`-representation `A` to the
`G ⧸ S`-representation it induces on `A^S`. -/
/-
**Rep.quotientToInvariantsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：quotientToInvariantsFunctor (S : Subgroup G) [S.Normal] : Rep.{w} k G ⥤ Re
p k (G ⧸ S) where obj X
参数：S : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup S ≤ G, this is the functor sending a `G`-representation 
`A` to the
`G ⧸ S`-representation it induces on `A^S`.
-/
noncomputable def quotientToInvariantsFunctor (S : Subgroup G) [S.Normal] :
    Rep.{w} k G ⥤ Rep k (G ⧸ S) where
  obj X := X.quotientToInvariants S
  map {X Y} f := Rep.ofHom ⟨((invariantsFunctor k S).map ((Rep.resFunctor S.subtype).map f)).hom,
    fun g ↦ QuotientGroup.induction_on g fun g ↦ by ext; simp [hom_comm_apply]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the functor equipping a module with the trivial representation, and
the functor sending a representation to its submodule of invariants. -/
@[simps]
/-
**Rep.invariantsAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：invariantsAdjunction : trivialFunctor k G ⊣ invariantsFunctor k G where un
it
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the functor equipping a module with the trivial represent
ation, and
the functor sending a representation to its submodule of invariants.
-/
noncomputable def invariantsAdjunction : trivialFunctor k G ⊣ invariantsFunctor k G where
  unit := { app _ := ModuleCat.ofHom <| LinearMap.id.codRestrict _ <| by simp [trivialFunctor] }
  counit := { app X := Rep.ofHom ⟨Submodule.subtype _, fun g ↦ by ext x; exact (x.2 g).symm⟩ }

@[simp]
/-
**Rep.invariantsAdjunction_homEquiv_apply_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：invariantsAdjunction_homEquiv_apply_hom {X : ModuleCat k} {Y : Rep k G} (f
 : (trivialFunctor k G).obj X ⟶ Y) : ((invariantsAdjunction k G).homEquiv _ _ f)
.hom = f.hom.codRestrict _ (by intro _ _; exact (hom_comm_apply f _ _).symm)
参数：f : (trivialFunctor k G).obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invariantsAdjunction_homEquiv_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : (trivialFunctor k G).obj X ⟶ Y) :
    ((invariantsAdjunction k G).homEquiv _ _ f).hom =
      f.hom.codRestrict _ (by intro _ _; exact (hom_comm_apply f _ _).symm) := rfl

@[simp]
/-
**Rep.invariantsAdjunction_homEquiv_symm_apply_hom** 是 Mathlib 中的一个引理，位于命名空间 `Re
p`。
形式化陈述：invariantsAdjunction_homEquiv_symm_apply_hom {X : ModuleCat k} {Y : Rep k 
G} (f : X ⟶ (invariantsFunctor k G).obj Y) : (((invariantsAdjunction k G).homEqu
iv _ _).symm f).hom.toLinearMap = Submodule.subtype _ ∘ₗ f.hom
参数：f : X ⟶ (invariantsFunctor k G).obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma invariantsAdjunction_homEquiv_symm_apply_hom
    {X : ModuleCat k} {Y : Rep k G} (f : X ⟶ (invariantsFunctor k G).obj Y) :
    (((invariantsAdjunction k G).homEquiv _ _).symm f).hom.toLinearMap =
      Submodule.subtype _ ∘ₗ f.hom := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (invariantsFunctor k G).IsRightAdjoint :=
  (invariantsAdjunction k G).isRightAdjoint

end Rep

