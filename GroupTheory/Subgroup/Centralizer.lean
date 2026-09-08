/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Submonoid.Centralizer

/-!
# Centralizers of subgroups
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G G' : Type*} [Group G] [Group G']

namespace Subgroup

variable {H K : Subgroup G}

/-- The `centralizer` of `s` is the subgroup of `g : G` commuting with every `h : s`. -/
@[to_additive
/-- The `centralizer` of `s` is the additive subgroup of `g : G` commuting with every `h : s`. -/]
/-
**Subgroup.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：centralizer (s : Set G) : Subgroup G where __
参数：s : Set G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Set.inv_mem_centralizer`：inv_mem_centralizer (ha : a in centralizer S) :
 a⁻¹ in centralizer S
-/
def centralizer (s : Set G) : Subgroup G where
  __ := Submonoid.centralizer s
  inv_mem' := Set.inv_mem_centralizer

@[to_additive]
/-
**Subgroup.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_centralizer_iff {g : G} {s : Set G} : g in centralizer s ↔ forall h in
 s, h * g = g * h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {g : G} {s : Set G} : g ∈ centralizer s ↔ ∀ h ∈ s, h * g = g * h :=
  Iff.rfl

open scoped commutatorElement in
@[to_additive]
/-
**Subgroup.mem_centralizer_iff_commutator_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subg
roup`。
形式化陈述：mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} : g in centraliz
er s ↔ forall h in s, ⁅h, g⁆ = 1
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_centralizer_iff_commutator_eq_one {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, ⁅h, g⁆ = 1 := by
  simp only [commutatorElement_def, mem_centralizer_iff, mul_inv_eq_iff_eq_mul, one_mul]

open scoped commutatorElement in
@[to_additive]
/-
**Subgroup.mem_centralizer_iff_commutator_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：mem_centralizer_iff_commutator_eq_one' {g : G} {s : Set G} : g in centrali
zer s ↔ forall h in s, ⁅g, h⁆ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commutatorElement_def`：commutatorElement_def {G : Type*} [Group G] (g₁ g
₂ : G) : ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff_commutator_eq_one' {g : G} {s : Set G} :
    g ∈ centralizer s ↔ ∀ h ∈ s, ⁅g, h⁆ = 1 := by
  refine forall₂_congr fun _ _ ↦ ?_
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, one_mul, eq_comm]

@[to_additive]
/-
**Subgroup.mem_centralizer_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：mem_centralizer_singleton_iff {g k : G} : k in Subgroup.centralizer {g} ↔ 
k * g = g * k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
lemma mem_centralizer_singleton_iff {g k : G} :
    k ∈ Subgroup.centralizer {g} ↔ k * g = g * k := by
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm

@[to_additive]
/-
**Subgroup.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_univ : centralizer Set.univ = center G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer Set.univ = center G :=
  SetLike.ext' (Set.centralizer_univ G)

@[to_additive]
/-
**Subgroup.le_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_centralizer_iff : H <= centralizer K ↔ K <= centralizer H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_centralizer_iff : H ≤ centralizer K ↔ K ≤ centralizer H :=
  ⟨fun h x hx _y hy => (h hy x hx).symm, fun h x hx _y hy => (h hy x hx).symm⟩

@[to_additive]
/-
**Subgroup.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_le_centralizer (s) : center G <= centralizer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer (s) : center G ≤ centralizer s :=
  Set.center_subset_centralizer s

@[to_additive]
/-
**Subgroup.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_le {s t : Set G} (h : s subseteq t) : centralizer t <= central
izer s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.centralizer_le`：centralizer_le (h : S subseteq T) : centralize
r T <= centralizer S
-/
theorem centralizer_le {s t : Set G} (h : s ⊆ t) : centralizer t ≤ centralizer s :=
  Submonoid.centralizer_le h

@[to_additive (attr := simp)]
/-
**Subgroup.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s subseteq
 center G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {s : Set G} : centralizer s = ⊤ ↔ s ⊆ center G :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

@[to_additive (attr := simp)]
/-
**Subgroup.centralizer_center** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_center : centralizer (center G : Set G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset {s
 : Set G} : centralizer s = ⊤ ↔ s subseteq center G
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem centralizer_center : centralizer (center G : Set G) = ⊤ :=
  centralizer_eq_top_iff_subset.mpr le_rfl

@[to_additive]
/-
**Subgroup.map_centralizer_le_centralizer_image** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：map_centralizer_le_centralizer_image (s : Set G) (f : G ->* G') : (Subgrou
p.centralizer s).map f <= Subgroup.centralizer (f '' s)
参数：s : Set G；f : G ->* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem map_centralizer_le_centralizer_image (s : Set G) (f : G →* G') :
    (Subgroup.centralizer s).map f ≤ Subgroup.centralizer (f '' s) := by
  rintro - ⟨g, hg, rfl⟩ - ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, hg h hh]

@[to_additive]
/-
**Subgroup.normal_centralizer** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normal_centralizer [H.Normal] : (centralizer H : Subgroup G).Normal where 
conj_mem g hg i h hh
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
instance normal_centralizer [H.Normal] : (centralizer H : Subgroup G).Normal where
  conj_mem g hg i h hh := by
    simpa [-mul_left_inj, -mul_right_inj, mul_assoc]
      using congr(i * $(hg _ <| ‹H.Normal›.conj_mem _ hh i⁻¹) * i⁻¹)

@[to_additive]
/-
**Subgroup.characteristic_centralizer** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：characteristic_centralizer [hH : H.Characteristic] : (centralizer (H : Set
 G)).Characteristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_comap_le`：characteristic_iff_comap_le : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.characteristic_iff_le_comap`：characteristic_iff_le_comap : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H <= H.comap ϕ.toMonoidHom
-/
instance characteristic_centralizer [hH : H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  refine Subgroup.characteristic_iff_comap_le.mpr fun ϕ g hg h hh => ϕ.injective ?_
  rw [map_mul, map_mul]
  exact hg (ϕ h) (Subgroup.characteristic_iff_le_comap.mp hH ϕ hh)

@[to_additive]
/-
**Subgroup.le_centralizer_iff_isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：le_centralizer_iff_isMulCommutative : K <= centralizer K ↔ IsMulCommutativ
e K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用引理 `mul_comm'`：mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) 
: a * b = b * a
-/
theorem le_centralizer_iff_isMulCommutative : K ≤ centralizer K ↔ IsMulCommutative K :=
  ⟨fun h ↦ ⟨⟨fun x y ↦ Subtype.ext <| h y.2 x x.2⟩⟩,
    fun _ x hx y hy ↦ congrArg Subtype.val <| mul_comm' ⟨y, hy⟩ ⟨x, hx⟩⟩

variable (H)

@[to_additive]
/-
**Subgroup.le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_centralizer [h : IsMulCommutative H] : H <= centralizer H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.le_centralizer_iff_isMulCommutative`：le_centralizer_iff_isMulCo
mmutative : K <= centralizer K ↔ IsMulCommutative K
-/
theorem le_centralizer [h : IsMulCommutative H] : H ≤ centralizer H :=
  le_centralizer_iff_isMulCommutative.mpr h

variable {H} in
@[to_additive]
/-
**Subgroup.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
形式化陈述：closure_le_centralizer_centralizer (s : Set G) : closure s <= centralizer 
(centralizer s)
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set G) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le _ |>.mpr Set.subset_centralizer_centralizer

@[to_additive]
/-
**Subgroup.centralizer_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_closure (s : Set G) : centralizer (closure s) = centralizer s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.centralizer_le`：centralizer_le {s t : Set G} (h : s subseteq t)
 : centralizer t <= centralizer s
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.le_centralizer_iff`：le_centralizer_iff : H <= centralizer K ↔ K
 <= centralizer H
· 使用引理 `Subgroup.closure_le_centralizer_centralizer`：closure_le_centralizer_cent
ralizer (s : Set G) : closure s <= centralizer (centralizer s)
-/
theorem centralizer_closure (s : Set G) : centralizer (closure s) = centralizer s :=
  le_antisymm (centralizer_le subset_closure)
    (le_centralizer_iff.mp (closure_le_centralizer_centralizer s))

@[to_additive]
/-
**Subgroup.centralizer_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_eq_iInf (s : Set G) : centralizer s = ⨅ g in s, centralizer {g
}
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `Subgroup.centralizer_le`：centralizer_le {s t : Set G} (h : s subseteq t)
 : centralizer t <= centralizer s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem centralizer_eq_iInf (s : Set G) : centralizer s = ⨅ g ∈ s, centralizer {g} :=
  le_antisymm (le_iInf₂ fun g hg ↦ centralizer_le (Set.singleton_subset_iff.mpr hg)) fun x hx ↦ by
    simpa only [mem_iInf, mem_centralizer_singleton_iff, eq_comm (a := x * _)] using! hx

@[to_additive]
/-
**Subgroup.center_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_eq_iInf {s : Set G} (hs : closure s = ⊤) : center G = ⨅ g in s, cen
tralizer {g}
参数：hs : closure s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.centralizer_univ`：centralizer_univ : centralizer Set.univ = cen
ter G
· 使用定理 `Subgroup.coe_top`：coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ
· 使用定理 `Subgroup.centralizer_closure`：centralizer_closure (s : Set G) : centrali
zer (closure s) = centralizer s
· 使用定理 `Subgroup.centralizer_eq_iInf`：centralizer_eq_iInf (s : Set G) : centrali
zer s = ⨅ g in s, centralizer {g}
-/
theorem center_eq_iInf {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g ∈ s, centralizer {g} := by
  rw [← centralizer_univ, ← coe_top, ← hs, centralizer_closure, centralizer_eq_iInf]

@[to_additive]
/-
**Subgroup.center_eq_infi'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_eq_infi' {s : Set G} (hs : closure s = ⊤) : center G = ⨅ g : s, cen
tralizer {(g : G)}
参数：hs : closure s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.center_eq_iInf`：center_eq_iInf {s : Set G} (hs : closure s = ⊤)
 : center G = ⨅ g in s, centralizer {g}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_subtype''`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_
8} (s : Set ι) (f : ι → α), ⨅ i, f ↑i = ⨅ t ∈ s, f t
-/
theorem center_eq_infi' {s : Set G} (hs : closure s = ⊤) :
    center G = ⨅ g : s, centralizer {(g : G)} := by
  rw [center_eq_iInf hs, ← iInf_subtype'']

/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
/-
**Subgroup.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isMulCommutative_closure {k : Set G} (hcomm : forall x in k, forall y in k
, x * y = y * x) : IsMulCommutative (closure k)
参数：hcomm : forall x in k, forall y in k, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.closure_le_centralizer_centralizer`：closure_le_centralizer_cent
ralizer (s : Set G) : closure s <= centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …
-/
theorem isMulCommutative_closure {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    IsMulCommutative (closure k) :=
  have := closure_le_centralizer_centralizer k
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative group. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-10"))
/-- If all the elements of a set `s` commute, then `closure s` is an additive commutative group. -/]
/-
**Subgroup.closureCommGroupOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subgroup`。
形式化陈述：closureCommGroupOfComm {k : Set G} (hcomm : forall x in k, forall y in k, 
x * y = y * x) : CommGroup (closure k)
参数：hcomm : forall x in k, forall y in k, x * y = y * x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isMulCommutative_closure`：isMulCommutative_closure {k : Set G} 
(hcomm : forall x in k, forall y in k, x * y = y * x) : IsMulCommutative (closur
e k)
-/
abbrev closureCommGroupOfComm {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    CommGroup (closure k) :=
  have := isMulCommutative_closure hcomm
  inferInstance

@[to_additive]
/-
**Subgroup.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instIsMulCommutative_closure {S : Type*} [SetLike S G] [MulMemClass S G] (
s : S) [IsMulCommutative s] : IsMulCommutative (closure (s : Set G))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isMulCommutative_closure`：isMulCommutative_closure {k : Set G} 
(hcomm : forall x in k, forall y in k, x * y = y * x) : IsMulCommutative (closur
e k)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S G] [MulMemClass S G] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set G)) :=
  isMulCommutative_closure fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

@[to_additive]
/-
**Subgroup.centralizer_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：centralizer_le_normalizer (s : Set G) : centralizer s <= normalizer s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem centralizer_le_normalizer (s : Set G) : centralizer s ≤ normalizer s := by
  refine fun g hg h ↦ ⟨fun hh ↦ ?_, fun hh ↦ ?_⟩
  · simpa [← hg h hh]
  · convert! hh
    simpa using hg _ hh

@[to_additive]
/-
**Subgroup.normal_subgroupOf_centralizer_normalizer** 是 Mathlib 中的一个实例，位于命名空间 `S
ubgroup`。
形式化陈述：normal_subgroupOf_centralizer_normalizer (s : Set G) : (centralizer s |>.s
ubgroupOf <| normalizer s).Normal
参数：s : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normal_subgroupOf_iff`：normal_subgroupOf_iff {H K : Subgroup G}
 (hHK : H <= K) : (H.subgroupOf K).Normal ↔ forall h k, h in H -> k in K -> k * 
h * k⁻¹ in H
· 使用定理 `Subgroup.centralizer_le_normalizer`：centralizer_le_normalizer (s : Set G
) : centralizer s <= normalizer s
· 使用定理 `Subgroup.mem_centralizer_iff_commutator_eq_one'`：mem_centralizer_iff_com
mutator_eq_one' {g : G} {s : Set G} : g in centralizer s ↔ forall h in s, ⁅g, h⁆
 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_set_normalizer_iff''`：mem_set_normalizer_iff'' : g in norma
lizer S ↔ forall h, h in S ↔ g⁻¹ * h * g in S
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
instance normal_subgroupOf_centralizer_normalizer (s : Set G) :
    (centralizer s |>.subgroupOf <| normalizer s).Normal := by
  refine (Subgroup.normal_subgroupOf_iff <| centralizer_le_normalizer s).mpr fun c n hc hn ↦ ?_
  refine mem_centralizer_iff_commutator_eq_one'.mpr fun g hg ↦ ?_
  suffices n * (c * (n⁻¹ * g * n) * c⁻¹ * n⁻¹ * g⁻¹) = 1 by simpa [commutatorElement_def, mul_assoc]
  simp [← hc _ <| mem_set_normalizer_iff''.mp hn g |>.mp hg]

@[to_additive]
/-
**Subgroup.normalizer_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalizer_singleton (g : G) : normalizer {g} = centralizer {g}
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `mul_eq_of_eq_mul_inv`：mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem normalizer_singleton (g : G) : normalizer {g} = centralizer {g} := by
  refine ext fun h ↦ ⟨?_, ?_⟩
  · rintro hh g rfl
    exact mul_eq_of_eq_mul_inv (hh g |>.mp rfl).symm
  · refine fun hh g ↦ ⟨?_, ?_⟩ <;> rintro rfl
    · exact (eq_mul_inv_of_mul_eq <| hh g rfl).symm
    · simpa using hh _ rfl

/-- The conjugation action of `N(H)` on `H`. -/
@[simps]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation action of `N(H)` on `H`.
-/
instance : MulDistribMulAction (normalizer H : Subgroup G) H where
  smul g h := ⟨g * h * g⁻¹, (g.2 h).mp h.2⟩
  one_smul g := by simp [HSMul.hSMul]
  mul_smul := by simp [HSMul.hSMul, mul_assoc]
  smul_one := by simp [HSMul.hSMul]
  smul_mul := by simp [HSMul.hSMul]

/-- The homomorphism `N(H) → Aut(H)` with kernel `C(H)`. -/
@[simps!]
/-
**Subgroup.normalizerMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：normalizerMonoidHom : normalizer (H : Set G) ->* MulAut H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism `N(H) → Aut(H)` with kernel `C(H)`.
-/
def normalizerMonoidHom : normalizer (H : Set G) →* MulAut H :=
  MulDistribMulAction.toMulAut (normalizer H : Subgroup G) H
/-
**Subgroup.normalizerMonoidHom_ker** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalizerMonoidHom_ker : H.normalizerMonoidHom.ker = (centralizer H).subg
roupOf (normalizer H : Subgroup G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normalizerMonoidHom_apply_apply_coe`：∀ {G : Type u_1} [inst : G
roup G] (H : Subgroup G) (x : ↥(Subgroup.normalizer ↑H)) (a : ↥H),   ↑((H.normal
izerMonoidHom x) a) = ↑x * ↑a * (↑…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem normalizerMonoidHom_ker :
    H.normalizerMonoidHom.ker = (centralizer H).subgroupOf (normalizer H : Subgroup G) := by
  simp [Subgroup.ext_iff, DFunLike.ext_iff, Subtype.ext_iff,
    mem_subgroupOf, mem_centralizer_iff, eq_mul_inv_iff_mul_eq, eq_comm]

end Subgroup

